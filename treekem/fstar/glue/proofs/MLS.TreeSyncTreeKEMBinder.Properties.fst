module MLS.TreeSyncTreeKEMBinder.Properties

open MLS.TreeSyncTreeKEMBinder
open MLS.Crypto
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeKEM.NetworkTypes
open MLS.Tree
open MLS.TreeSync.Types
open MLS.TreeKEM.Types
open MLS.TreeSync.API.Types
open MLS.TreeKEM.API.Tree.Types

#set-options "--fuel 1 --ifuel 1"

val treesync_treekem_rel:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  treesync bytes tkt l i -> treekem bytes l i ->
  prop
let treesync_treekem_rel ts tk =
  treesync_to_treekem ts == tk

val treesync_treekem_state_rel:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #token_t:Type ->
  #group_id:mls_bytes bytes -> #leaf_ind:nat ->
  treesync_state bytes tkt token_t group_id -> treekem_tree_state bytes leaf_ind ->
  prop
let treesync_treekem_state_rel #bytes #cb #token_t #group_id #leaf_ind st_ts st_tk =
  st_ts.levels == st_tk.levels /\
  st_ts.tree `treesync_treekem_rel` st_tk.tree

val external_pathsync_pre_pathkem_rel:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  external_pathsync bytes tkt l i li -> pre_pathkem bytes l i li ->
  prop
let rec external_pathsync_pre_pathkem_rel #bytes #cb #l #i #li ps pk =
  match ps, pk with
  | PLeaf lns, PLeaf lnk ->
    (lns <: leaf_node_data_nt bytes tkt).content == (lnk <: treekem_leaf bytes).public_key
  | PNode opt_pns ps_next, PNode opt_pnk pk_next ->
    external_pathsync_pre_pathkem_rel ps_next pk_next /\
    opt_pns == opt_pnk

val pathsync_pre_pathkem_rel:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  pathsync bytes tkt l i li -> pre_pathkem bytes l i li ->
  prop
let rec pathsync_pre_pathkem_rel #bytes #cb #l #i #li ps pk =
  match ps, pk with
  | PLeaf lns, PLeaf lnk ->
    (lns <: leaf_node_nt bytes tkt).data.content == (lnk <: treekem_leaf bytes).public_key
  | PNode opt_pns ps_next, PNode opt_pnk pk_next ->
    pathsync_pre_pathkem_rel ps_next pk_next /\
    opt_pns == opt_pnk

val pathsync_pathkem_rel:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  pathsync bytes tkt l i li -> pathkem bytes l i li ->
  prop
let rec pathsync_pathkem_rel #bytes #cb #l #i #li ps pk =
  match ps, pk with
  | PLeaf lns, PLeaf lnk ->
    (lns <: leaf_node_nt bytes tkt).data.content == (lnk <: treekem_leaf bytes).public_key
  | PNode opt_pns ps_next, PNode opt_pnk pk_next ->
    pathsync_pathkem_rel ps_next pk_next /\ (
      match opt_pns, opt_pnk with
      | Some pns, Some pnk ->
        pns == pnk.encryption_key
      | None, None -> True
      | _, _ -> False
    )
