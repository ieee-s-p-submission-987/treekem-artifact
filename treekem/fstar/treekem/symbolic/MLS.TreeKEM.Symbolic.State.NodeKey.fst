module MLS.TreeKEM.Symbolic.State.NodeKey

open Comparse
open DY.Core
open DY.Lib
open MLS.Crypto
open MLS.Tree
open MLS.NetworkTypes
open MLS.TreeKEM.Types
open MLS.Symbolic.Parsers
open MLS.Symbolic
open FStar.Mul

#set-options "--fuel 0 --ifuel 0"

val ps_hpke_private_key:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  parser_serializer_prefix bytes (hpke_private_key bytes)
let ps_hpke_private_key #bytes #cb =
  mk_trivial_isomorphism (ps_lbytes (hpke_private_key_length #bytes))

val ps_treekem_priv:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  l:nat -> i:tree_index l -> li:leaf_index l i ->
  parser_serializer_prefix bytes (treekem_priv bytes l i li)
let ps_treekem_priv #bytes #cb l i li =
  mk_trivial_isomorphism (ps_path ps_hpke_private_key (ps_option ps_hpke_private_key) l i li)

[@@ with_bytes bytes]
type treekem_node_keys_state = {
  l: nat;
  i: tree_index l;
  li: leaf_index l i;
  [@@@ with_parser #bytes (ps_treekem_priv l i li)]
  path: treekem_priv bytes l i li;
}

%splice [ps_treekem_node_keys_state] (gen_parser (`treekem_node_keys_state))
%splice [ps_treekem_node_keys_state_is_well_formed] (gen_is_well_formed_lemma (`treekem_node_keys_state))

instance local_state_treekem_node_keys_state: local_state treekem_node_keys_state = {
  tag = "MLS.TreeKEM.NodeKeyState";
  format = mk_parseable_serializeable ps_treekem_node_keys_state;
}

val node_key_label_pred:
  principal -> bytes ->
  principal -> string -> state_id -> treekem_node_keys_state -> prop
let node_key_label_pred prin1 leaf_pk =
  fun prin2 tag sid st ->
    prin1 == prin2 /\
    tag == "MLS.TreeKEM.NodeKeyState" /\
    hpke_pk (get_path_leaf st.path) == leaf_pk

val node_key_usage: usage
let node_key_usage = 
  mk_hpke_sk_usage ("MLS.NodeHpkeKey", empty)

val entropy_usage_for_node_key: usage
let entropy_usage_for_node_key = 
  mk_hpke_entropy_usage ("MLS.NodeHpkeKey", empty)

val node_key_label:
  principal -> bytes ->
  label
let node_key_label prin leaf_pk =
  typed_state_pred_label (node_key_label_pred prin leaf_pk)

val node_key_label_can_flow_public:
  tr:trace ->
  prin:principal -> leaf_pk:bytes ->
  Lemma
  (requires
    (node_key_label prin leaf_pk) `can_flow tr` public
  )
  (ensures
    exists sid l i li (path:treekem_priv bytes l i li).
      state_was_corrupt tr prin "MLS.TreeKEM.NodeKeyState" sid { l; i; li; path } /\
      hpke_pk (get_path_leaf path) == leaf_pk
  )
let node_key_label_can_flow_public tr prin leaf_pk = ()

val is_node_sk_for_leaf_pk:
  {|crypto_invariants|} ->
  trace -> principal -> bytes -> bytes ->
  prop
let is_node_sk_for_leaf_pk tr prin leaf_pk node_sk =
  bytes_invariant tr node_sk /\
  get_label tr node_sk `can_flow tr` node_key_label prin leaf_pk /\
  node_sk `has_usage tr` node_key_usage

val is_node_pk_for_leaf_pk:
  {|crypto_invariants|} ->
  trace -> principal -> bytes -> bytes ->
  prop
let is_node_pk_for_leaf_pk tr prin leaf_pk node_pk =
  bytes_invariant tr node_pk /\
  get_hpke_sk_label tr node_pk `can_flow tr` node_key_label prin leaf_pk /\
  node_pk `has_hpke_sk_usage tr` node_key_usage

#push-options "--fuel 1 --ifuel 1"
val treekem_priv_state_pred:
  {|crypto_invariants|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  trace -> principal -> treekem_priv bytes l i li ->
  prop
let rec treekem_priv_state_pred #cinvs #l #i #li tr prin p =
  match p with
  | PLeaf leaf_sk ->
    is_node_sk_for_leaf_pk tr prin (hpke_pk leaf_sk) leaf_sk
  | PNode opt_node_sk p_next ->
    treekem_priv_state_pred tr prin p_next /\ (
      match opt_node_sk with
      | None -> True
      | Some node_sk -> (
        is_node_sk_for_leaf_pk tr prin (hpke_pk (get_path_leaf p)) node_sk
      )
    )
#pop-options

#push-options "--fuel 1 --ifuel 1"
val treekem_priv_state_pred_later:
  {|crypto_invariants|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  tr1:trace -> tr2:trace -> prin:principal -> p:treekem_priv bytes l i li ->
  Lemma
  (requires
    treekem_priv_state_pred tr1 prin p /\
    tr1 <$ tr2
  )
  (ensures treekem_priv_state_pred tr2 prin p)
let rec treekem_priv_state_pred_later #cinvs #l #i #li tr1 tr2 prin p =
  match p with
  | PLeaf leaf_sk -> ()
  | PNode opt_node_sk p_next ->
    treekem_priv_state_pred_later tr1 tr2 prin p_next
#pop-options

#push-options "--fuel 1 --ifuel 1"
val treekem_priv_state_pred_knowable:
  {|crypto_invariants|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  tr:trace -> prin:principal -> p:treekem_priv bytes l i li ->
  Lemma
  (requires treekem_priv_state_pred tr prin p)
  (ensures is_well_formed_prefix (ps_treekem_priv l i li) (is_knowable_by (node_key_label prin (hpke_pk (get_path_leaf p))) tr) p)
let rec treekem_priv_state_pred_knowable #cinvs #l #i #li tr prin p =
  match p with
  | PLeaf leaf_sk -> ()
  | PNode opt_node_sk p_next ->
    treekem_priv_state_pred_knowable tr prin p_next
#pop-options

val treekem_node_keys_state_pred: {|crypto_invariants|} -> local_state_predicate treekem_node_keys_state
let treekem_node_keys_state_pred #cinvs = {
  pred = (fun tr prin sid content ->
    treekem_priv_state_pred tr prin content.path
  );
  pred_later = (fun tr1 tr2 prin sid content ->
    treekem_priv_state_pred_later tr1 tr2 prin content.path
  );
  pred_knowable = (fun tr prin sid content ->
    treekem_priv_state_pred_knowable tr prin content.path;
    is_well_formed_prefix_weaken ps_treekem_node_keys_state (is_knowable_by (node_key_label prin (hpke_pk (get_path_leaf content.path))) tr) (is_knowable_by (principal_typed_state_content_label prin (local_state_treekem_node_keys_state.tag) sid content) tr) content
  );
}

val has_treekem_node_keys_state_invariant: {|protocol_invariants|} -> prop
let has_treekem_node_keys_state_invariant #invs =
  has_local_state_predicate treekem_node_keys_state_pred

val treekem_node_keys_state_tag_and_invariant: {|crypto_invariants|} -> dtuple2 string local_bytes_state_predicate
let treekem_node_keys_state_tag_and_invariant #ci = (|local_state_treekem_node_keys_state.tag, local_state_predicate_to_local_bytes_state_predicate treekem_node_keys_state_pred|)
