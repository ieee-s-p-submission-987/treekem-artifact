module MLS.TreeSync.MembershipProof

open Comparse
open MLS.Crypto
open MLS.Tree
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types
open MLS.TreeSync.TreeHash
open MLS.TreeSync.TreeHash.Proofs

#set-options "--fuel 1 --ifuel 1"

(*

// Some notes:
//
// The functions and theorems in this file are cluttered with preconditons.
// This is because computing a hash comes with a precondition:
// that its input doesn't exceed some given length, e.g. 2^61 for SHA256.
// Because this bound is large, in practice the preconditions will always be true,
// however because of the rigor imposed by machine-checked proofs,
// we must still state those preconditions.
//
// All the functions and theorems in this file work when considering a subtree.
// It means that if someone knows the tree hash of a subtree,
// we can compute and check a membership proof for that particular subtree.
//
// The membership proof comes with external parameters,
// such as its size (corresponding to the height of the associated tree),
// its position (corresponding to the position of the associated tree, if it is a subtree)
// and the leaf index of the member.
// This raise the following question:
// Are these parameters part of the membership proof, or is it some external data?
// This model leaves the choice on that question:
// these parameters can be seen as being part of the membership proof,
// or it can be something that is already agreed upon and don't need to be transmitted on the wire.
// In any case, the security guarantees state that the membership proof covers its size and position,
// ensuring that it is not a malleable part of the membership proof.

(*** Membership proof type ***)

// A membership proof is a path containing a leaf node, and a list of parent nodes along with the sibling tree hash
// The type is parametrized by the size of the path, the position of the node at its root and the index of its leaf.
// See the comment on `tree` and `path` in MLS.Tree for more info
type membership_proof (bytes:Type0) {|crypto_bytes bytes|} (tkt:treekem_types bytes) =
  path (leaf_node_nt bytes tkt) (option (parent_node_nt bytes tkt) & lbytes bytes (hash_length #bytes))

(*** Computing and checking a membership proof ***)

// Precondition for `compute_membership_proof`.
val compute_membership_proof_pre:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i ->
  li:leaf_index l i{Some? (leaf_at t li)} ->
  bool
let rec compute_membership_proof_pre #bytes #cb #tkt #l #i t li =
  match t with
  | TLeaf (Some ln) -> true
  | TNode opn _ _ -> (
    let (child, sibling) = get_child_sibling t li in
    tree_hash_pre sibling &&
    compute_membership_proof_pre child li
  )

// Given a tree `t`, compute the membership proof for leaf at index `li`
val compute_membership_proof:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i ->
  li:leaf_index l i{Some? (leaf_at t li) /\ compute_membership_proof_pre t li} ->
  membership_proof bytes tkt l i li
let rec compute_membership_proof #bytes #cb #tkt #l #i t li =
  match t with
  | TLeaf (Some ln) -> PLeaf ln
  | TNode opn _ _ -> (
    let (child, sibling) = get_child_sibling t li in
    let res_next = compute_membership_proof child li in
    let sibling_hash = tree_hash sibling in
    PNode (opn, sibling_hash) res_next
  )

// Precondition for `membership_proof_to_tree_hash`
val membership_proof_to_tree_hash_pre:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  membership_proof bytes tkt l i li ->
  bool
let rec membership_proof_to_tree_hash_pre #bytes #cb #tkt #l #i #li mp =
  match mp with
  | PLeaf lp -> (
    tree_hash_pre ((TLeaf (Some lp)) <: treesync bytes tkt l i)
  )
  | PNode (opn, sibling_hash) mp_next ->
    membership_proof_to_tree_hash_pre mp_next &&
    (1 + prefixes_length ((ps_option (ps_parent_node_nt tkt)).serialize opn)) + 2 + hash_length #bytes + 2 + hash_length #bytes < hash_max_input_length #bytes

// Auxillary function:
// given a membership proof `mp`, compute the hash of the tree from which it was (supposedly) computed
#push-options "--z3rlimit 15"
val membership_proof_to_tree_hash:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  mp:membership_proof bytes tkt l i li{membership_proof_to_tree_hash_pre mp} ->
  lbytes bytes (hash_length #bytes)
let rec membership_proof_to_tree_hash #bytes #cb #tkt #l #i #li mp =
  match mp with
  | PLeaf lp -> (
    tree_hash ((TLeaf (Some lp)) <: treesync bytes tkt l i)
  )
  | PNode (opn, sibling_hash) mp_next ->
    let child_hash = membership_proof_to_tree_hash mp_next in
    let left_hash = if is_left_leaf li then child_hash else sibling_hash in
    let right_hash = if is_left_leaf li then sibling_hash else child_hash in
    let hash_input: bytes = serialize (tree_hash_input_nt bytes tkt) (ParentTreeHashInput ({
      parent_node = opn;
      left_hash = left_hash;
      right_hash = right_hash;
    })) in
    hash_hash hash_input
#pop-options

// Precondition for `check_membership_proof`
val check_membership_proof_pre:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  membership_proof bytes tkt l i li ->
  bool
let check_membership_proof_pre #bytes #cb #tkt #l #i #li mp =
  membership_proof_to_tree_hash_pre mp

// Final function to check a membership proof:
// we store `root_tree_hash` and received the membership proof `mp` for that hash,
// this function checks that they correspond.
val check_membership_proof:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  bytes -> mp:membership_proof bytes tkt l i li{check_membership_proof_pre mp} ->
  bool
let check_membership_proof #bytes #cb #tkt #l #i #li root_tree_hash mp =
  root_tree_hash = membership_proof_to_tree_hash mp

(*** Correctness theorem ***)

// Correctness of the membership proof lemma:
// If we compute a membership proof from a tree, and compute the hash of the membership proof,
// we obtain the tree hash of the tree.
val compute_membership_proof_to_tree_hash:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i ->
  li:leaf_index l i ->
  Lemma
  (requires
    Some? (leaf_at t li) /\
    compute_membership_proof_pre t li /\
    membership_proof_to_tree_hash_pre (compute_membership_proof t li) /\
    tree_hash_pre t
  )
  (ensures membership_proof_to_tree_hash (compute_membership_proof t li) == tree_hash t)
let rec compute_membership_proof_to_tree_hash #bytes #cb #tkt #l #i t li =
  match t with
  | TLeaf (Some ln) -> ()
  | TNode opn _ _ -> (
    let (child, sibling) = get_child_sibling t li in
    compute_membership_proof_to_tree_hash child li
  )

// Final correctness theorem:
// `check_membership_proof` will succeed when called with the tree hash of a tree,
// and the membership proof for some leaf of that tree.
val compute_membership_proof_correct:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i ->
  li:leaf_index l i ->
  Lemma
  (requires
    Some? (leaf_at t li) /\
    compute_membership_proof_pre t li /\
    check_membership_proof_pre (compute_membership_proof t li) /\
    tree_hash_pre t
  )
  (ensures check_membership_proof (tree_hash t) (compute_membership_proof t li))
let compute_membership_proof_correct #bytes #cb #tkt #l #i t li =
  compute_membership_proof_to_tree_hash t li

(*** Security theorem ***)

// Predicate stating the guarantees offered by the membership proof.
// This is used in the next theorems.
// It states:
// the leaf node at index `li` in the tree and the leaf node stored in the membership proof match.
// Moreover, all parent nodes between the leaf and the root match the ones in the membership proof.
val membership_proof_guarantees:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  treesync bytes tkt l i -> membership_proof bytes tkt l i li ->
  bool
let rec membership_proof_guarantees #bytes #cb #tkt #l #i #li t mp =
  match t, mp with
  | TLeaf oln, PLeaf ln ->
    oln = Some ln
  | TNode t_opn _ _, PNode (mp_opn, _) mp_next -> (
    let (child, _) = get_child_sibling t li in
    t_opn = mp_opn &&
    membership_proof_guarantees child mp_next
  )

// Auxillary function for the proof
val membership_proof_to_hash_input:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  mp:membership_proof bytes tkt l i li{membership_proof_to_tree_hash_pre mp} ->
  tree_hash_input_nt bytes tkt
let membership_proof_to_hash_input #bytes #cb #tkt #l #i #li mp =
  match mp with
  | PLeaf lp -> (
    get_tree_hash_input ((TLeaf (Some lp)) <: treesync bytes tkt l i)
  )
  | PNode (opn, sibling_hash) mp_next ->
    let child_hash = membership_proof_to_tree_hash mp_next in
    let left_hash = if is_left_leaf li then child_hash else sibling_hash in
    let right_hash = if is_left_leaf li then sibling_hash else child_hash in
    ParentTreeHashInput ({
      parent_node = opn;
      left_hash = left_hash;
      right_hash = right_hash;
    })

// Main lemma.
// See the security theorem below for an informal explanation.
#push-options "--z3rlimit 50"
val membership_proof_to_tree_hash_security_aux:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  #l':nat -> #i':tree_index l' ->
  t:treesync bytes tkt l' i' ->
  mp:membership_proof bytes tkt l i li ->
  Pure (bytes & bytes)
  (requires
    tree_hash_pre t /\
    membership_proof_to_tree_hash_pre mp /\
    membership_proof_to_tree_hash mp == tree_hash t
  )
  (ensures (fun (b1, b2) ->
    (
      l == l' /\ i == i' /\
      membership_proof_guarantees t mp
    ) \/ (
      length b1 < hash_max_input_length #bytes /\
      length b2 < hash_max_input_length #bytes /\
      hash_hash b1 == hash_hash b2 /\ ~(b1 == b2)
    )
  ))
let rec membership_proof_to_tree_hash_security_aux #bytes #cb #tkt #l #i #li #l' #i' t mp =
  ( // Don't know why this is useful, bad SMT encoding somewhere?
    match mp with
    | PLeaf lp -> ()
    | PNode (opn, sibling_hash) mp_next -> ()
  );
  let t_hash_input = get_tree_hash_input t in
  let mp_hash_input = membership_proof_to_hash_input mp in
  let serialized_t_hash_input: bytes = serialize _ t_hash_input in
  let serialized_mp_hash_input: bytes = serialize _ mp_hash_input in
  parse_serialize_inv_lemma #bytes _ t_hash_input;
  parse_serialize_inv_lemma #bytes _ mp_hash_input;
  assert(length serialized_t_hash_input < hash_max_input_length #bytes);
  assert(length serialized_mp_hash_input < hash_max_input_length #bytes);
  if l = l' && i = i' && membership_proof_guarantees t mp then
    (empty, empty)
  else if not (t_hash_input = mp_hash_input) then (
    (serialized_t_hash_input, serialized_mp_hash_input)
  ) else (
    match t, mp with
    | TNode _ left right, PNode _ mp_next -> (
      if is_left_leaf li then (
        membership_proof_to_tree_hash_security_aux left mp_next
      ) else (
        membership_proof_to_tree_hash_security_aux right mp_next
      )
    )
  )
#pop-options

// The theorem reads as follows:
// For all `root_tree_hash`, membership proof `mp`,
// if `mp` verifies with `root_tree_hash`,
// then for all trees with a tree hash equal to `root_tree_hash`,
// they have the same size and position as `mp`,
// moreover the tree and the membership proof are related by the predicate `membership_proof_guarantees`,
// or we can compute a hash collision.
//
// In other words, if we find a counter-example to the guarantees offered by membership proof,
// then we can derive from it a hash collision.
// Hence, breaking the security of membership proof is as hard as computing a hash collision,
// which is assumed to be hard.
//
// Note that the theorem says "for all trees" and not "there exists a tree":
// we cannot guarantee the existence of a tree because the sibling tree hashes in the membership
// could be garbage, and not correspond to actual tree hashes.
// The "for all" then means if there exists a tree with a tree hash equal to `root_tree_hash`,
// then that tree has the relation we want with the membership proof.

val membership_proof_to_tree_hash_security:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  #l':nat -> #i':tree_index l' ->
  root_tree_hash:bytes ->
  t:treesync bytes tkt l' i' ->
  mp:membership_proof bytes tkt l i li ->
  Pure (bytes & bytes)
  (requires
    tree_hash_pre t /\
    check_membership_proof_pre mp /\
    check_membership_proof root_tree_hash mp /\
    root_tree_hash == tree_hash t
  )
  (ensures (fun (b1, b2) ->
    (
      l == l' /\ i == i' /\
      membership_proof_guarantees t mp
    ) \/ (
      length b1 < hash_max_input_length #bytes /\
      length b2 < hash_max_input_length #bytes /\
      hash_hash b1 == hash_hash b2 /\ ~(b1 == b2)
    )
  ))
let membership_proof_to_tree_hash_security #bytes #cb #tkt #l #i #li #l' #i' root_tree_hash t mp =
  membership_proof_to_tree_hash_security_aux t mp

*)
