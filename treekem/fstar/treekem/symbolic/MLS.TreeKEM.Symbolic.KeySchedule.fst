module MLS.TreeKEM.Symbolic.KeySchedule

open DY.Core
open DY.Lib
open Comparse
open MLS.Result
open MLS.Crypto
open MLS.Crypto.Derived.Lemmas
open MLS.TreeDEM.NetworkTypes
open MLS.TreeKEM.NetworkTypes
open MLS.TreeKEM.KeySchedule
open MLS.NetworkTypes
open MLS.Bootstrap.NetworkTypes
open MLS.Bootstrap.Welcome
open MLS.Symbolic
open MLS.Symbolic.Labels.Big
open MLS.Symbolic.Labels.Prop
open MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation
open MLS.Bootstrap.Symbolic.KeyPackage
open MLS.Crypto.Derived.Symbolic.EncryptWithLabel
open MLS.Crypto.Derived.Symbolic.ExpandWithLabel
open MLS.TreeDEM.Message.Transcript

#set-options "--fuel 0 --ifuel 0"

type commit_is_last_in_tx_hash_aux_witness (bytes:Type0) {|crypto_bytes bytes|} =
  wire_format_nt & framed_content_nt bytes & bytes & lbytes bytes (hash_output_length #bytes)

val commit_is_last_in_tx_hash_aux:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  commit_nt bytes -> bytes -> commit_is_last_in_tx_hash_aux_witness bytes ->
  prop
let commit_is_last_in_tx_hash_aux #bytes #cb commit confirmed_transcript_hash (wire_format, msg, signature, interim_transcript_hash) =
  Success confirmed_transcript_hash == compute_confirmed_transcript_hash wire_format msg signature interim_transcript_hash /\
  msg.content.content_type == CT_commit /\
  commit == msg.content.content

val commit_is_last_in_tx_hash:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  commit_nt bytes -> bytes ->
  prop
let commit_is_last_in_tx_hash #bytes #cb commit confirmed_transcript_hash =
  exists witness. commit_is_last_in_tx_hash_aux commit confirmed_transcript_hash witness

#push-options "--ifuel 1"
val proposal_or_ref_rel:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  proposal_or_ref_nt bytes -> proposal_nt bytes ->
  prop
let proposal_or_ref_rel #bytes #cb por p =
  match por with
  | POR_proposal p' -> p == p'
  | POR_reference ref ->
    Success (ref <: bytes) == make_proposal_ref (serialize _ p)
#pop-options

#push-options "--fuel 1 --ifuel 1"
val proposal_or_refs_rel:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  list (proposal_or_ref_nt bytes) -> list (proposal_nt bytes) ->
  prop
let rec proposal_or_refs_rel #bytes #cb pors ps =
  match pors, ps with
  | [], [] -> True
  | h1::t1, h2::t2 ->
    proposal_or_ref_rel h1 h2 /\
    proposal_or_refs_rel t1 t2
  | _ -> False
#pop-options

#push-options "--fuel 1 --ifuel 1"
val proposals_to_key_packages:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  list (proposal_nt bytes) ->
  list (key_package_nt bytes tkt)
let rec proposals_to_key_packages #bytes #bl l =
  match l with
  | [] -> []
  | (P_add {key_package})::t -> key_package::proposals_to_key_packages t
  | _::t -> proposals_to_key_packages t
#pop-options

val compute_confirmed_transcript_hash_inj:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  wire_format1:wire_format_nt -> msg1:framed_content_nt bytes -> signature1:bytes -> interim_transcript_hash1:lbytes bytes (hash_output_length #bytes) ->
  wire_format2:wire_format_nt -> msg2:framed_content_nt bytes -> signature2:bytes -> interim_transcript_hash2:lbytes bytes (hash_output_length #bytes) ->
  Pure (bytes & bytes)
  (requires
    Success? (compute_confirmed_transcript_hash wire_format1 msg1 signature1 interim_transcript_hash1) /\
    Success? (compute_confirmed_transcript_hash wire_format2 msg2 signature2 interim_transcript_hash2) /\
    compute_confirmed_transcript_hash wire_format1 msg1 signature1 interim_transcript_hash1 == compute_confirmed_transcript_hash wire_format2 msg2 signature2 interim_transcript_hash2
  )
  (ensures fun (b1, b2) ->
    (
      wire_format1 == wire_format2 /\
      msg1 == msg2 /\
      signature1 == signature2 /\
      interim_transcript_hash1 == interim_transcript_hash2
    ) \/
    is_hash_collision b1 b2
  )
let compute_confirmed_transcript_hash_inj #bytes #cb wire_format1 msg1 signature1 interim_transcript_hash1 wire_format2 msg2 signature2 interim_transcript_hash2 =
  bytes_hasEq #bytes;
  if wire_format1 = wire_format2 && msg1 = msg2 && signature1 = signature2 && interim_transcript_hash1 = interim_transcript_hash2 then
    (empty, empty)
  else (
    let confirmed_transcript_hash_input1 = {
      wire_format = wire_format1;
      content = msg1;
      signature = signature1;
    } in
    let confirmed_transcript_hash_input2 = {
      wire_format = wire_format2;
      content = msg2;
      signature = signature2;
    } in
    let hash_input_1 = concat #bytes interim_transcript_hash1 (serialize _ confirmed_transcript_hash_input1) in
    let hash_input_2 = concat #bytes interim_transcript_hash2 (serialize _ confirmed_transcript_hash_input2) in
    split_concat #bytes interim_transcript_hash1 (serialize _ confirmed_transcript_hash_input1);
    split_concat #bytes interim_transcript_hash2 (serialize _ confirmed_transcript_hash_input2);
    parse_serialize_inv_lemma #bytes _ confirmed_transcript_hash_input1;
    parse_serialize_inv_lemma #bytes _ confirmed_transcript_hash_input2;
    (hash_input_1, hash_input_2)
  )

val commit_is_last_in_tx_hash_aux_lemma:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  commit1:commit_nt bytes -> commit2:commit_nt bytes ->
  confirmed_transcript_hash:bytes ->
  witness1:commit_is_last_in_tx_hash_aux_witness bytes -> witness2:commit_is_last_in_tx_hash_aux_witness bytes ->
  Pure (bytes & bytes)
  (requires
    commit_is_last_in_tx_hash_aux commit1 confirmed_transcript_hash witness1 /\
    commit_is_last_in_tx_hash_aux commit2 confirmed_transcript_hash witness2
  )
  (ensures fun (b1, b2) ->
    commit1 == commit2 \/
    is_hash_collision b1 b2
  )
let commit_is_last_in_tx_hash_aux_lemma #bytes #cb commit1 commit2 confirmed_transcript_hash (wire_format1, msg1, signature1, interim_transcript_hash1) (wire_format2, msg2, signature2, interim_transcript_hash2) =
  compute_confirmed_transcript_hash_inj wire_format1 msg1 signature1 interim_transcript_hash1 wire_format2 msg2 signature2 interim_transcript_hash2

val commit_is_last_in_tx_hash_inj_lemma:
  commit1:commit_nt bytes -> commit2:commit_nt bytes ->
  confirmed_transcript_hash:bytes ->
  Lemma
  (requires
    commit_is_last_in_tx_hash commit1 confirmed_transcript_hash /\
    commit_is_last_in_tx_hash commit2 confirmed_transcript_hash
  )
  (ensures commit1 == commit2)
let commit_is_last_in_tx_hash_inj_lemma commit1 commit2 confirmed_transcript_hash =
  eliminate exists witness1 witness2. commit_is_last_in_tx_hash_aux commit1 confirmed_transcript_hash witness1 /\ commit_is_last_in_tx_hash_aux commit2 confirmed_transcript_hash witness2
  returns commit1 == commit2
  with _. (
    let (b1, b2) = commit_is_last_in_tx_hash_aux_lemma commit1 commit2 confirmed_transcript_hash witness1 witness2 in
    hash_injective b1 b2
  )

#push-options "--ifuel 1"
val proposal_or_ref_rel_lemma:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  proposal_or_ref:proposal_or_ref_nt bytes ->
  proposal1:proposal_nt bytes -> proposal2:proposal_nt bytes ->
  Pure (bytes & bytes)
  (requires
    proposal_or_ref_rel proposal_or_ref proposal1 /\
    proposal_or_ref_rel proposal_or_ref proposal2
  )
  (ensures fun (b1, b2) ->
    proposal1 == proposal2 \/
    is_hash_collision b1 b2
  )
let proposal_or_ref_rel_lemma #bytes #cb proposal_or_ref proposal1 proposal2 =
  match proposal_or_ref with
  | POR_proposal _ -> (empty, empty)
  | POR_reference ref ->
    parse_serialize_inv_lemma #bytes _ proposal1;
    parse_serialize_inv_lemma #bytes _ proposal2;
    make_proposal_ref_inj (serialize _ proposal1) (serialize _ proposal2)
#pop-options

#push-options "--ifuel 1 --fuel 1"
val proposal_or_refs_rel_lemma:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  proposal_or_refs:list (proposal_or_ref_nt bytes) ->
  proposals1:list (proposal_nt bytes) -> proposals2:list (proposal_nt bytes) ->
  Pure (bytes & bytes)
  (requires
    proposal_or_refs_rel proposal_or_refs proposals1 /\
    proposal_or_refs_rel proposal_or_refs proposals2
  )
  (ensures fun (b1, b2) ->
    proposals1 == proposals2 \/
    is_hash_collision b1 b2
  )
let rec proposal_or_refs_rel_lemma #bytes #cb proposal_or_refs proposals1 proposals2 =
  match proposal_or_refs, proposals1, proposals2 with
  | [], [], [] -> (empty, empty)
  | hpor::tpor, h1::t1, h2::t2 ->
    if h1 = h2 then
      proposal_or_refs_rel_lemma tpor t1 t2
    else
      proposal_or_ref_rel_lemma hpor h1 h2
#pop-options

val confirmed_transcript_hash_to_init_label_aux:
  bytes ->
  commit_nt bytes & list (proposal_nt bytes) ->
  label
let confirmed_transcript_hash_to_init_label_aux confirmed_transcript_hash (commit, proposals) =
  meet (
    prop_to_label (
      commit_is_last_in_tx_hash commit confirmed_transcript_hash /\
      proposal_or_refs_rel commit.proposals proposals
    )
  ) (
    List.Tot.fold_right join (List.Tot.map key_package_to_init_label (proposals_to_key_packages proposals)) secret
  )


val confirmed_transcript_hash_to_init_label:
  bytes ->
  label
let confirmed_transcript_hash_to_init_label confirmed_transcript_hash =
  big_join (confirmed_transcript_hash_to_init_label_aux confirmed_transcript_hash)

#push-options "--ifuel 1"
val confirmed_transcript_hash_to_init_label_eq:
  confirmed_transcript_hash:bytes ->
  commit:commit_nt bytes -> proposals:list (proposal_nt bytes) ->
  Lemma
  (requires
    commit_is_last_in_tx_hash commit confirmed_transcript_hash /\
    proposal_or_refs_rel commit.proposals proposals
  )
  (ensures
    confirmed_transcript_hash_to_init_label confirmed_transcript_hash
    ==
    List.Tot.fold_right join (List.Tot.map key_package_to_init_label (proposals_to_key_packages proposals)) secret
  )
let confirmed_transcript_hash_to_init_label_eq confirmed_transcript_hash commit proposals =
  intro_label_equal
    (confirmed_transcript_hash_to_init_label confirmed_transcript_hash)
    (List.Tot.fold_right join (List.Tot.map key_package_to_init_label (proposals_to_key_packages proposals)) secret)
    (fun tr ->
      // ->
      big_join_flow_to_component tr (confirmed_transcript_hash_to_init_label_aux confirmed_transcript_hash) (commit, proposals);
      prop_to_label_true (
        commit_is_last_in_tx_hash commit confirmed_transcript_hash /\
        proposal_or_refs_rel commit.proposals proposals
      );

      // <-
      let init_label = List.Tot.fold_right join (List.Tot.map key_package_to_init_label (proposals_to_key_packages proposals)) secret in
      introduce forall commit2 proposals2. init_label `can_flow tr` (confirmed_transcript_hash_to_init_label_aux confirmed_transcript_hash) (commit2, proposals2) with (
        let p = 
          commit_is_last_in_tx_hash commit2 confirmed_transcript_hash /\
          proposal_or_refs_rel commit2.proposals proposals2
        in
        eliminate p \/ ~p
        returns init_label `can_flow tr` (confirmed_transcript_hash_to_init_label_aux confirmed_transcript_hash) (commit2, proposals2)
        with _. (
          commit_is_last_in_tx_hash_inj_lemma commit commit2 confirmed_transcript_hash;
          let (b1, b2) = proposal_or_refs_rel_lemma commit.proposals proposals proposals2 in
          FStar.Classical.move_requires_2 hash_injective b1 b2
        ) and _. (
          prop_to_label_false p
        )
      )
    )
#pop-options

#push-options "--ifuel 1"
val expand_usage_extractedkey_joiner: expandwithlabel_crypto_usage
let expand_usage_extractedkey_joiner = {
  get_usage = (fun prk_usage context length -> KdfExpandKey "MLS.JoinerSecret" empty);
  get_label = (fun prk_usage prk_label context length ->
    match parse (group_context_nt bytes) context with
    | Some group_context ->
      prk_label `join` confirmed_transcript_hash_to_init_label group_context.confirmed_transcript_hash
    | None -> public
  );
  get_label_lemma = (fun tr prk_usage prk_label context length -> ());
}
#pop-options

let expand_usage_extractedkey_welcome = mk_secret_expandwithlabel_usage (KdfExpandKey "MLS.WelcomeSecret" empty)
let expand_usage_welcome_key = mk_secret_expandwithlabel_usage (AeadKey "MLS.WelcomeKey" empty)
let expand_usage_welcome_nonce = mk_public_expandwithlabel_usage NoUsage

let expand_usage_extractedkey_epoch = mk_secret_expandwithlabel_usage (KdfExpandKey "MLS.EpochSecret" empty)

let expand_usage_epoch_senderdata = mk_secret_expandwithlabel_usage (KdfExpandKey "MLS.SenderDataSecret" empty) //TODO new epoch storage
let expand_usage_senderdata_key = mk_secret_expandwithlabel_usage (KdfExpandKey "MLS.SenderDataKey" empty)
let expand_usage_senderdata_nonce = mk_public_expandwithlabel_usage (KdfExpandKey "MLS.SenderDataKey" empty)

let expand_usage_epoch_encryption = mk_secret_expandwithlabel_usage (KdfExpandKey "MLS.EncryptionSecret" empty) //TODO treedem label
let expand_usage_epoch_exporter = mk_secret_expandwithlabel_usage (KdfExpandKey "MLS.ExporterSecret" empty) //TODO new epoch storage
let expand_usage_epoch_external = mk_secret_expandwithlabel_usage (mk_hpke_sk_usage ("MLS.ExternalKey", empty)) //TODO new epoch storage
let expand_usage_epoch_confirmation = mk_secret_expandwithlabel_usage (KdfExpandKey "MLS.ConfirmationKey" empty) //TODO new epoch storage, mac key
let expand_usage_epoch_membership = mk_secret_expandwithlabel_usage (KdfExpandKey "MLS.MembershipKey" empty) //TODO new epoch storage, mac key
let expand_usage_epoch_resumption = mk_secret_expandwithlabel_usage (KdfExpandKey "MLS.ResumptionSecret" empty) //TODO new epoch storage, kdf_extract key
let expand_usage_epoch_authentication = mk_secret_expandwithlabel_usage (NoUsage) //TODO what is the label of that thing?
let expand_usage_epoch_init = mk_secret_expandwithlabel_usage (KdfExpandKey "MLS.InitSecret" empty) //TODO new epoch storage, kdf_extract key
//TODO: for exporter secret?

val has_mls_keyschedule_invariants: {|crypto_usages|} -> prop
let has_mls_keyschedule_invariants #cusgs =
  has_mls_expandwithlabel_usage ("KDF.ExtractedKey", "joiner", expand_usage_extractedkey_joiner) /\

  has_mls_expandwithlabel_usage ("KDF.ExtractedKey", "welcome", expand_usage_extractedkey_welcome) /\
  has_mls_expandwithlabel_usage ("MLS.WelcomeSecret", "key", expand_usage_welcome_key) /\
  has_mls_expandwithlabel_usage ("MLS.WelcomeSecret", "nonce", expand_usage_welcome_nonce) /\

  has_mls_expandwithlabel_usage ("KDF.ExtractedKey", "epoch", expand_usage_extractedkey_epoch) /\

  has_mls_expandwithlabel_usage ("MLS.EpochSecret", "sender_data", expand_usage_epoch_senderdata) /\
  has_mls_expandwithlabel_usage ("MLS.SenderDataSecret", "key", expand_usage_senderdata_key) /\
  has_mls_expandwithlabel_usage ("MLS.SenderDataSecret", "nonce", expand_usage_senderdata_nonce) /\

  has_mls_expandwithlabel_usage ("MLS.EpochSecret", "encryption", expand_usage_epoch_encryption) /\
  has_mls_expandwithlabel_usage ("MLS.EpochSecret", "exporter", expand_usage_epoch_exporter) /\
  has_mls_expandwithlabel_usage ("MLS.EpochSecret", "external", expand_usage_epoch_external) /\
  has_mls_expandwithlabel_usage ("MLS.EpochSecret", "confirmation", expand_usage_epoch_confirmation) /\
  has_mls_expandwithlabel_usage ("MLS.EpochSecret", "membership", expand_usage_epoch_membership) /\
  has_mls_expandwithlabel_usage ("MLS.EpochSecret", "resumption", expand_usage_epoch_resumption) /\
  has_mls_expandwithlabel_usage ("MLS.EpochSecret", "authentication", expand_usage_epoch_authentication) /\
  has_mls_expandwithlabel_usage ("MLS.EpochSecret", "init", expand_usage_epoch_init)

val secret_init_to_joiner_proof:
  {|crypto_invariants|} ->
  tr:trace ->
  init_secret:bytes -> opt_commit_secret:option bytes -> group_context:group_context_nt bytes ->
  commit:commit_nt bytes -> proposals:list (proposal_nt bytes) -> // de-hash of confirmed transcript hash
  Lemma
  (requires
    commit_is_last_in_tx_hash commit group_context.confirmed_transcript_hash /\
    proposal_or_refs_rel commit.proposals proposals /\
    bytes_invariant tr init_secret /\
    (
      match opt_commit_secret with
      | None -> True
      | Some commit_secret -> bytes_invariant tr commit_secret
    ) /\
    is_well_formed _ (bytes_invariant tr) group_context /\
    has_mls_keyschedule_invariants
  )
  (ensures (
    match secret_init_to_joiner init_secret opt_commit_secret (serialize _ group_context) with
    | Success joiner_secret -> (
      bytes_invariant tr joiner_secret /\
      joiner_secret `has_usage tr` KdfExpandKey "MLS.JoinerSecret" empty /\ (
        match opt_commit_secret with
        | None ->
          get_label tr joiner_secret `equivalent tr` ((get_label tr init_secret) `join` List.Tot.fold_right join (List.Tot.map key_package_to_init_label (proposals_to_key_packages proposals)) secret)
        | Some commit_secret ->
          get_label tr joiner_secret `equivalent tr` ((get_label tr init_secret `meet` get_label tr commit_secret) `join` List.Tot.fold_right join (List.Tot.map key_package_to_init_label (proposals_to_key_packages proposals)) secret)
      )
    )
    | _ -> True
  ))
let secret_init_to_joiner_proof tr init_secret opt_commit_secret group_context commit proposals =
  match secret_init_to_joiner init_secret opt_commit_secret (serialize _ group_context) with
  | Success joiner_secret -> (
    let Success prk = kdf_extract init_secret (opt_secret_to_secret opt_commit_secret) in
    assert(Success joiner_secret == expand_with_label #bytes prk "joiner" (serialize _ group_context) (kdf_length #bytes));
    confirmed_transcript_hash_to_init_label_eq group_context.confirmed_transcript_hash commit proposals;
    serialize_wf_lemma _ (bytes_invariant tr) group_context;
    expand_with_label_lemma tr "KDF.ExtractedKey" expand_usage_extractedkey_joiner prk (KdfExpandKey "KDF.ExtractedKey" empty) "joiner" (serialize _ group_context) (kdf_length #bytes)
  )
  | _ -> ()

val secret_joiner_to_welcome_proof:
  {|crypto_invariants|} ->
  tr:trace ->
  joiner_secret:bytes ->
  opt_psk:option bytes ->
  Lemma
  (requires
    bytes_invariant tr joiner_secret /\
    (
      match opt_psk with
      | None -> True
      | Some psk -> bytes_invariant tr psk
    ) /\
    has_mls_keyschedule_invariants
  )
  (ensures (
    match secret_joiner_to_welcome joiner_secret opt_psk with
    | Success welcome_secret -> (
      bytes_invariant tr welcome_secret /\
      welcome_secret `has_usage tr` KdfExpandKey "MLS.WelcomeSecret" empty /\ (
        match opt_psk with
        | None ->
          get_label tr welcome_secret `equivalent tr` get_label tr joiner_secret
        | Some psk ->
          get_label tr welcome_secret `equivalent tr` (get_label tr joiner_secret `meet` get_label tr psk)
      )
    )
    | _ -> True
  ))
let secret_joiner_to_welcome_proof tr joiner_secret opt_psk =
  match secret_joiner_to_welcome joiner_secret opt_psk with
  | Success welcome_secret -> (
    let Success extracted_key = kdf_extract joiner_secret (opt_secret_to_secret opt_psk) in
    assert(Success welcome_secret == expand_with_label #bytes extracted_key "welcome" empty (kdf_length #bytes));
    expand_with_label_lemma tr "KDF.ExtractedKey" expand_usage_extractedkey_welcome extracted_key (KdfExpandKey "KDF.ExtractedKey" empty) "welcome" empty (kdf_length #bytes)
  )
  | _ -> ()

val welcome_secret_to_key_proof:
  {|crypto_invariants|} ->
  tr:trace ->
  welcome_secret:bytes ->
  Lemma
  (requires
    bytes_invariant tr welcome_secret /\
    welcome_secret `has_usage tr` KdfExpandKey "MLS.WelcomeSecret" empty /\
    has_mls_keyschedule_invariants
  )
  (ensures (
    match welcome_secret_to_key welcome_secret with
    | Success welcome_key -> (
      bytes_invariant tr welcome_key /\
      welcome_key `has_usage tr` AeadKey "MLS.WelcomeKey" empty /\
      get_label tr welcome_key `equivalent tr` get_label tr welcome_secret
    )
    | _ -> True
  ))
let welcome_secret_to_key_proof #cinvs tr welcome_secret =
  match welcome_secret_to_key welcome_secret with
  | Success welcome_key -> (
    assert(Success welcome_key == expand_with_label welcome_secret "key" (empty #bytes) (aead_key_length #bytes));
    expand_with_label_lemma tr "MLS.WelcomeSecret" expand_usage_welcome_key welcome_secret (KdfExpandKey "MLS.WelcomeSecret" empty) "key" empty (aead_key_length #bytes)
  )
  | _ -> ()

val welcome_secret_to_nonce_proof:
  {|crypto_invariants|} ->
  tr:trace ->
  welcome_secret:bytes ->
  Lemma
  (requires
    bytes_invariant tr welcome_secret /\
    welcome_secret `has_usage tr` KdfExpandKey "MLS.WelcomeSecret" empty /\
    has_mls_keyschedule_invariants
  )
  (ensures (
    match welcome_secret_to_nonce welcome_secret with
    | Success welcome_nonce -> (
      is_publishable tr welcome_nonce
    )
    | _ -> True
  ))
let welcome_secret_to_nonce_proof tr welcome_secret =
  match welcome_secret_to_nonce welcome_secret with
  | Success welcome_nonce -> (
    assert(Success welcome_nonce == expand_with_label welcome_secret "nonce" (empty #bytes) (aead_nonce_length #bytes));
    expand_with_label_lemma tr "MLS.WelcomeSecret" expand_usage_welcome_nonce welcome_secret (KdfExpandKey "MLS.WelcomeSecret" empty) "nonce" empty (aead_nonce_length #bytes)
  )
  | _ -> ()

//val secret_joiner_to_epoch_proof:
//  {|crypto_invariants|} ->
//  tr:trace ->
//  joiner_secret:bytes -> group_context:bytes ->
//  Lemma
//  (requires
//    bytes_invariant tr joiner_secret /\
//    has_mls_keyschedule_invariants
//  )
//  (ensures (
//    match secret_joiner_to_epoch joiner_secret None group_context with
//    | Success epoch_secret -> (
//      bytes_invariant tr epoch_secret /\
//      epoch_secret `has_usage tr` KdfExpandKey "MLS.EpochSecret" empty
//    )
//    | _ -> True
//  ))
//let secret_joiner_to_epoch_proof tr joiner_secret group_context =
//  match secret_joiner_to_welcome joiner_secret None with
//  | Success welcome_secret -> (
//    let Success extracted_key = kdf_extract joiner_secret (opt_secret_to_secret None) in
//    assert(Success welcome_secret == expand_with_label #bytes extracted_key "welcome" empty (kdf_length #bytes));
//    expand_with_label_lemma tr "KDF.ExtractedKey" expand_usage_extractedkey_welcome extracted_key (KdfExpandKey "KDF.ExtractedKey" empty) "welcome" empty (kdf_length #bytes)
//  )
//  | _ -> ()



// joiner_to_epoch
// epoch_to_*
// epoch_to_init

