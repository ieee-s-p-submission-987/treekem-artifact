module MLS.TreeKEM.Symbolic.State.EpochSecrets

open Comparse
open DY.Core
open DY.Lib
open MLS.NetworkTypes
open MLS.Tree
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types
open MLS.TreeKEM.NetworkTypes
open MLS.TreeSync.TreeHash
open MLS.TreeSync.TreeHash.Proofs
open MLS.Result
open MLS.Symbolic
open MLS.Symbolic.Labels.Big
open MLS.Symbolic.Labels.Prop
open MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation

#set-options "--fuel 0 --ifuel 0"

type epoch_secret_type =
  | InitSecret: epoch_secret_type
  | SenderDataSecret: epoch_secret_type
  // The encryption secret should be managed by TreeDEM (once it is proved)
  | EncryptionSecret: epoch_secret_type
  | ExporterSecret: epoch_secret_type
  | ExternalSecret: epoch_secret_type
  | ConfirmationKey: epoch_secret_type
  | MembershipKey: epoch_secret_type
  | ResumptionPSK: epoch_secret_type
  | EpochAuthenticator: epoch_secret_type

#push-options "--fuel 1 --ifuel 1"
%splice [ps_epoch_secret_type] (gen_parser (`epoch_secret_type))
%splice [ps_epoch_secret_type_is_well_formed] (gen_is_well_formed_lemma (`epoch_secret_type))
#pop-options

[@@ with_bytes bytes]
type treekem_epoch_secret = {
  ty: epoch_secret_type;
  context: group_context_nt bytes;
  secret: bytes;
}

%splice [ps_treekem_epoch_secret] (gen_parser (`treekem_epoch_secret))
%splice [ps_treekem_epoch_secret_is_well_formed] (gen_is_well_formed_lemma (`treekem_epoch_secret))

instance local_state_treekem_epoch_secret: local_state treekem_epoch_secret = {
  tag = "MLS.TreeKEM.EpochSecrets";
  format = mk_parseable_serializeable ps_treekem_epoch_secret;
}

[@@ with_bytes bytes]
type epoch_secret_usage_data = {
  group_context: group_context_nt bytes;
}

%splice [ps_epoch_secret_usage_data] (gen_parser (`epoch_secret_usage_data))

instance parseable_serializeable_bytes_epoch_secret_usage_data: parseable_serializeable bytes epoch_secret_usage_data =
  mk_parseable_serializeable ps_epoch_secret_usage_data

#push-options "--ifuel 1"
val mk_epoch_secret_usage:
  epoch_secret_type -> group_context_nt bytes ->
  usage
let mk_epoch_secret_usage ty group_context =
  match ty with
  | InitSecret ->
    KdfExpandKey "MLS.TreeKEM.InitSecret" (serialize _ {group_context})
  | SenderDataSecret ->
    KdfExpandKey "MLS.TreeDEM.SenderDataSecret" (serialize _ {group_context})
  | EncryptionSecret ->
    KdfExpandKey "MLS.TreeDEM.EncryptionSecret" (serialize _ {group_context})
  | ExporterSecret ->
    KdfExpandKey "MLS.TreeKEM.ExporterSecret" (serialize _ {group_context})
  | ExternalSecret ->
    NoUsage
  | ConfirmationKey ->
    NoUsage
  | MembershipKey ->
    NoUsage
  | ResumptionPSK ->
    NoUsage
  | EpochAuthenticator ->
    NoUsage
#pop-options

val mk_principal_epoch_secret_label_pred:
  principal -> epoch_secret_type -> group_context_nt bytes ->
  principal -> string -> state_id -> treekem_epoch_secret -> prop
let mk_principal_epoch_secret_label_pred prin1 ty group_context =
  fun prin2 tag sid st ->
    prin1 == prin2 /\
    tag == "MLS.TreeKEM.EpochSecrets" /\
    st.ty == ty /\
    st.context == group_context

val mk_principal_epoch_secret_label:
  epoch_secret_type -> principal -> group_context_nt bytes ->
  label
let mk_principal_epoch_secret_label ty prin group_context =
  typed_state_pred_label (mk_principal_epoch_secret_label_pred prin ty group_context)

val mk_tree_epoch_secret_label_aux:
  #l:nat ->
  epoch_secret_type -> group_context_nt bytes -> treesync bytes tkt l 0 ->
  leaf_index l 0 ->
  label
let mk_tree_epoch_secret_label_aux #l ty group_context t li =
  match leaf_at t li with
  | None -> secret
  | Some leaf_node -> (
    match credential_to_principal leaf_node.data.credential with
    | None -> DY.Core.Label.Unknown.unknown_label
    | Some prin -> (
      mk_principal_epoch_secret_label ty prin group_context
    )
  )

val mk_tree_epoch_secret_label:
  #l:nat ->
  epoch_secret_type -> group_context_nt bytes -> treesync bytes tkt l 0 ->
  label
let mk_tree_epoch_secret_label #l ty group_context t =
  big_join (mk_tree_epoch_secret_label_aux ty group_context t)

type full_tree = l:nat & treesync bytes tkt l 0

val tree_hash_full_tree_rel:
  bytes -> full_tree ->
  prop
let tree_hash_full_tree_rel t_hash (|l, t|) =
  Success t_hash == tree_hash t

val mk_epoch_secret_label_aux:
  epoch_secret_type -> group_context_nt bytes -> full_tree ->
  label
let mk_epoch_secret_label_aux ty group_context (|l, t|) =
  meet
    (prop_to_label (tree_hash_full_tree_rel group_context.tree_hash (|l, t|)))
    (mk_tree_epoch_secret_label ty group_context t)

val mk_epoch_secret_label:
  epoch_secret_type -> group_context_nt bytes ->
  label
let mk_epoch_secret_label ty group_context =
  big_join (mk_epoch_secret_label_aux ty group_context)

val mk_epoch_secret_label_eq:
  #l:nat ->
  ty:epoch_secret_type -> group_context:group_context_nt bytes ->
  t:treesync bytes tkt l 0 ->
  Lemma
  (requires
    Success (group_context.tree_hash <: bytes) == tree_hash t
  )
  (ensures
    mk_epoch_secret_label ty group_context == mk_tree_epoch_secret_label ty group_context t
  )
let mk_epoch_secret_label_eq #l ty group_context t =
  intro_label_equal
    (mk_epoch_secret_label ty group_context)
    (mk_tree_epoch_secret_label ty group_context t)
    (fun tr ->
      // ->
      big_join_flow_to_component tr (mk_epoch_secret_label_aux ty group_context) (|l, t|);
      prop_to_label_true (tree_hash_full_tree_rel group_context.tree_hash (|l, t|));

      // <-
      introduce forall ft2. mk_tree_epoch_secret_label ty group_context t  `can_flow tr` mk_epoch_secret_label_aux ty group_context ft2 with (
        let (|l2, t2|) = ft2 in
        let p = tree_hash_full_tree_rel group_context.tree_hash ft2 in
        eliminate p \/ ~p
        returns _
        with _. (
          let (b1, b2) = tree_hash_inj t t2 in
          FStar.Classical.move_requires_2 hash_injective b1 b2
        )
        and _. (
          prop_to_label_false p
        )
      )
    )

val mk_tree_epoch_secret_label_is_corrupt:
  #l:nat ->
  tr:trace ->
  ty:epoch_secret_type -> group_context:group_context_nt bytes -> t:treesync bytes tkt l 0 ->
  Lemma
  (requires
    (forall leaf_index. Some? (leaf_at t leaf_index) ==> (Some? (credential_to_principal (Some?.v (leaf_at t leaf_index)).data.credential))) /\
    is_corrupt tr (mk_tree_epoch_secret_label ty group_context t)
  )
  (ensures (
    exists leaf_index.
      Some? (leaf_at t leaf_index) /\
      is_corrupt tr (mk_principal_epoch_secret_label ty (Some?.v (credential_to_principal (Some?.v (leaf_at t leaf_index)).data.credential)) group_context)
  ))
let mk_tree_epoch_secret_label_is_corrupt #l tr ty group_context t =
  normalize_term_spec (is_corrupt tr secret)
