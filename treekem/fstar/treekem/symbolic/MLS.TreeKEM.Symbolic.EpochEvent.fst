module MLS.TreeKEM.Symbolic.EpochEvent

open Comparse
open DY.Core
open DY.Lib
open MLS.Symbolic
open MLS.TreeSync.Symbolic.State.SignatureKey
open MLS.TreeSync.Symbolic.Parsers
open MLS.Bootstrap.Symbolic.KeyPackage
open MLS.TreeKEM.Symbolic.Tree.Labels
open MLS.Tree
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types
open MLS.TreeKEM.NetworkTypes
open MLS.Bootstrap.NetworkTypes
open MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation
open MLS.TreeKEM.Symbolic.State.EpochSecrets
open MLS.Crypto
open MLS.NetworkTypes
open MLS.TreeKEM.KeySchedule
open MLS.Result

#set-options "--fuel 1 --ifuel 1"

val ps_psks:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  parser_serializer bytes (list (pre_shared_key_id_nt bytes & bytes))
let ps_psks #bytes #bl =
  ps_list (
    mk_isomorphism
      (pre_shared_key_id_nt bytes & bytes)
      (Comparse.bind ps_pre_shared_key_id_nt (fun _ -> ps_bytes))
      (fun (|x,y|) -> (x,y))
      (fun (x,y) -> (|x,y|))
  )

type i_just_joined_group = {
  inviter: nat;
}

%splice [ps_i_just_joined_group] (gen_parser (`i_just_joined_group))

type commit_type =
  | AddOnlyCommit
  | FullCommit

%splice [ps_commit_type] (gen_parser (`commit_type))

[@@ with_bytes bytes]
type i_processed_commit_group = {
  previous_init_secret: bytes;
  previous_group_context: group_context_nt bytes;
  commit_ty: commit_type;
  [@@@ with_parser #bytes (ps_list (ps_key_package_nt tkt))]
  joiners: list (key_package_nt bytes tkt);
}

%splice [ps_i_processed_commit_group] (gen_parser (`i_processed_commit_group))

[@@ with_bytes bytes]
type how_am_i_in_group =
  | JustJoined: i_just_joined_group -> how_am_i_in_group
  | ProcessedCommit: i_processed_commit_group -> how_am_i_in_group

%splice [ps_how_am_i_in_group] (gen_parser (`how_am_i_in_group))

[@@ with_bytes bytes]
type i_am_in_group = {
  how: how_am_i_in_group;
  group_context: group_context_nt bytes;
  tree_height: nat;
  [@@@ with_parser #bytes (ps_treesync tkt tree_height 0)]
  tree: treesync bytes tkt tree_height 0;
  [@@@ with_parser #bytes ps_psks]
  psks: list (pre_shared_key_id_nt bytes & bytes);
  epoch_secret: bytes;
  init_secret: bytes;
}

%splice [ps_i_am_in_group] (gen_parser (`i_am_in_group))

instance event_i_am_in_group: event i_am_in_group = {
  tag = "MLS.TreeKEM.IAmInGroup";
  format = mk_parseable_serializeable ps_i_am_in_group;
}

val bytes_invariant_psks:
  {|crypto_invariants|} ->
  trace -> list (pre_shared_key_id_nt bytes & bytes) ->
  prop
let bytes_invariant_psks #cinvs tr psks =
  for_allP (bytes_invariant tr) (List.Tot.map snd psks)

val bytes_invariant_psks_later:
  {|crypto_invariants|} ->
  tr1:trace -> tr2:trace ->
  psks:list (pre_shared_key_id_nt bytes & bytes) ->
  Lemma
  (requires
    bytes_invariant_psks tr1 psks /\
    tr1 <$ tr2
  )
  (ensures bytes_invariant_psks tr2 psks)
  [SMTPat (bytes_invariant_psks tr1 psks); SMTPat (tr1 <$ tr2)]
let bytes_invariant_psks_later #cinvs tr1 tr2 psks =
  for_allP_eq (bytes_invariant tr1) (List.Tot.map snd psks);
  for_allP_eq (bytes_invariant tr2) (List.Tot.map snd psks)

val compute_psk_secret_label:
  {|crypto_usages|} ->
  trace -> list (pre_shared_key_id_nt bytes & bytes) ->
  label
let compute_psk_secret_label #cusgs tr psks =
  List.Tot.fold_right meet (List.Tot.map (get_label tr) (List.Tot.map snd psks)) public

val compute_psk_secret_label_later:
  {|crypto_invariants|} ->
  tr1:trace -> tr2:trace ->
  psks:list (pre_shared_key_id_nt bytes & bytes) ->
  Lemma
  (requires
    bytes_invariant_psks tr1 psks /\
    tr1 <$ tr2
  )
  (ensures compute_psk_secret_label tr1 psks == compute_psk_secret_label tr2 psks)
  [SMTPat (compute_psk_secret_label tr1 psks); SMTPat (tr1 <$ tr2)]
let rec compute_psk_secret_label_later #cinvs tr1 tr2 psks =
  match psks with
  | [] -> ()
  | h::t ->
    compute_psk_secret_label_later tr1 tr2 t

val joiners_are_stale_participants:
  #l:nat ->
  list (key_package_nt bytes tkt) -> treesync bytes tkt l 0 ->
  prop
let joiners_are_stale_participants #l joiners tree =
  forall (joiner:key_package_nt bytes tkt).
    List.Tot.memP joiner joiners ==> (
      exists li.
        Some? (leaf_at tree li) /\
        (Some?.v (leaf_at tree li)) == joiner.tbs.leaf_node /\
        (Some?.v (leaf_at tree li)).data.source == LNS_key_package
    )

val i_am_in_group_pred: {|crypto_invariants|} -> event_predicate i_am_in_group
let i_am_in_group_pred #cinvs tr me ev =
  Success (ev.group_context.tree_hash <: bytes) == MLS.TreeSync.TreeHash.tree_hash ev.tree /\
  bytes_invariant tr ev.epoch_secret /\
  bytes_invariant tr ev.init_secret /\
  join (get_label tr ev.epoch_secret) (mk_epoch_secret_label InitSecret ev.group_context) `can_flow tr` (get_label tr ev.init_secret) /\
  i_have_verified_every_leaf_node tr me ev.tree ev.group_context.group_id /\
  (
    match ev.how with
    | JustJoined { inviter } -> (
      inviter < pow2 ev.tree_height /\
      Some? (leaf_at ev.tree inviter) /\
      Some? (credential_to_principal (Some?.v (leaf_at ev.tree inviter)).data.credential) /\ (
        let Some inviter_leaf_node = leaf_at ev.tree inviter in
        let Some inviter_id = credential_to_principal inviter_leaf_node.data.credential in
        (
          is_corrupt tr (signature_key_label inviter_id inviter_leaf_node.data.signature_key)
        ) \/ (
          exists inviter_ev.
            inviter_ev.group_context == ev.group_context /\
            inviter_ev.epoch_secret == ev.epoch_secret /\
            inviter_ev.psks == ev.psks /\
            ProcessedCommit? inviter_ev.how /\
            joiners_are_stale_participants (ProcessedCommit?._0 inviter_ev.how).joiners ev.tree /\
            event_triggered tr inviter_id inviter_ev
        )
      )
    )
    | ProcessedCommit last_epoch_link -> (
      bytes_invariant tr last_epoch_link.previous_init_secret /\
      bytes_invariant_psks tr ev.psks /\
      (forall (joiner:key_package_nt bytes tkt).
        List.Tot.memP joiner last_epoch_link.joiners ==> (
          i_have_verified_key_package tr me joiner
        )
      ) /\
      exists previous_ev.
        event_triggered tr me previous_ev /\
        previous_ev.group_context == last_epoch_link.previous_group_context /\
        previous_ev.init_secret == last_epoch_link.previous_init_secret /\ (
          let commit_secret_label =
            match last_epoch_link.commit_ty with
            | AddOnlyCommit -> public
            | FullCommit -> node_sk_label ev.tree ev.group_context.group_id
          in
          let psk_secret_label = compute_psk_secret_label tr ev.psks in
          let joiners_label = List.Tot.fold_right join (List.Tot.map key_package_to_init_label last_epoch_link.joiners) secret in
          let epoch_secret_label =
            meet
              (join
                (meet
                  (get_label tr last_epoch_link.previous_init_secret)
                  commit_secret_label
                )
                joiners_label
              )
              psk_secret_label
          in
          epoch_secret_label `can_flow tr` (get_label tr ev.epoch_secret)
        )
    )
  )

val has_i_am_in_group_invariant:
  {|protocol_invariants|} ->
  prop
let has_i_am_in_group_invariant #invs =
  has_event_pred i_am_in_group_pred

val i_am_in_group_tag_and_invariant: {|crypto_invariants|} -> (string & compiled_event_predicate)
let i_am_in_group_tag_and_invariant #cinvs =
  (event_i_am_in_group.tag, compile_event_pred i_am_in_group_pred)

val has_treekem_invariants:
  {|protocol_invariants|} ->
  prop
let has_treekem_invariants #invs =
  has_key_package_has_been_verified_invariant /\
  has_leaf_node_has_been_verified_invariant /\
  has_i_am_in_group_invariant
