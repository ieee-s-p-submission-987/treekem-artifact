module MLS.Bootstrap.Symbolic.Welcome

open Comparse
open DY.Core
open DY.Lib
open MLS.Result
open MLS.Crypto
open MLS.Crypto.Derived.Lemmas
open MLS.Bootstrap.Symbolic.KeyPackageRef
open MLS.TreeKEM.NetworkTypes
open MLS.TreeKEM.KeySchedule
open MLS.Bootstrap.NetworkTypes
open MLS.Bootstrap.Welcome
open MLS.Bootstrap.KeyPackageRef
open MLS.Bootstrap.Symbolic.KeyPackage
open MLS.Bootstrap.Symbolic.State.InitKey
open MLS.TreeKEM.Symbolic.State.NodeKey
open MLS.Symbolic
open MLS.Crypto.Derived.Symbolic.EncryptWithLabel
open MLS.TreeKEM.Symbolic.KeySchedule

#set-options "--fuel 0 --ifuel 0"

val joiner_secret_usage: usage
let joiner_secret_usage =
  KdfExpandKey "MLS.JoinerSecret" empty

#push-options "--ifuel 1"
val mls_hpke_welcome_pred: {|crypto_usages|} -> encryptwithlabel_crypto_pred
let mls_hpke_welcome_pred #cusgs = {
  pred = (fun tr usg_data msg context ->
    match parse init_key_usage_t usg_data, parse (group_secrets_nt bytes) msg with
    | _, None -> False
    | None, _ -> False
    | Some data, Some group_secrets -> (
      group_secrets.joiner_secret `has_usage tr` joiner_secret_usage /\ (
        match group_secrets.path_secret with
        | None -> True
        | Some path_secret ->
          // See MLS.TreeKEM.Symbolic.Tree.Operations.decoded_path_secret_good
          get_label tr path_secret.path_secret `can_flow tr` node_key_label data.me data.leaf_public_key /\
          (exists data. path_secret.path_secret `has_usage tr` (KdfExpandKey "MLS.PathSecret" data))
      )
    )
  );
  pred_later = (fun tr1 tr2 usg_data msg context ->
    parse_wf_lemma (group_secrets_nt bytes) (bytes_well_formed tr1) msg
  );
}
#pop-options

(*** Decryption ***)

#push-options "--ifuel 1 --z3rlimit 15"
val decrypt_with_label_welcome_lemma:
  {|crypto_invariants|} ->
  tr:trace ->
  me:principal -> my_leaf_pk:bytes ->
  skR:hpke_private_key bytes -> context:bytes -> enc:hpke_kem_output bytes -> ciphertext:bytes ->
  Lemma
  (requires
    bytes_invariant tr skR /\
    skR `has_usage tr` init_key_usage me my_leaf_pk /\
    bytes_invariant tr enc /\
    bytes_invariant tr context /\
    bytes_invariant tr ciphertext /\
    has_mls_encryptwithlabel_pred ("MLS.InitHpkeKey", "Welcome", mls_hpke_welcome_pred)
  )
  (ensures (
    match decrypt_with_label skR "Welcome" context enc ciphertext with
    | Success plaintext -> (
      is_publishable tr plaintext \/ (
        match parse (group_secrets_nt bytes) plaintext with
        | None -> False
        | Some group_secrets -> (
          bytes_invariant tr group_secrets.joiner_secret /\
          group_secrets.joiner_secret `has_usage tr` joiner_secret_usage
        )
      )
    )
    | _ -> True
  ))
let decrypt_with_label_welcome_lemma #cinvs tr me my_leaf_pk skR context enc ciphertext =
  match decrypt_with_label skR "Welcome" context enc ciphertext with
  | Success res -> (
    bytes_invariant_decrypt_with_label mls_hpke_welcome_pred "MLS.InitHpkeKey" (init_key_usage_data me my_leaf_pk) tr skR "Welcome" context enc ciphertext;
    parse_wf_lemma (group_secrets_nt bytes) (bytes_invariant tr) res
  )
  | _ -> ()
#pop-options

#push-options "--fuel 1 --ifuel 2"
val find_my_encrypted_group_secret_spec:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #a:Type ->
  kp_ref_to_kp_secrets:(bytes -> option a) -> l:list (encrypted_group_secrets_nt bytes) ->
  Lemma (
    match find_my_encrypted_group_secret kp_ref_to_kp_secrets l with
    | None -> True
    | Some (new_member, kp_secrets, encrypted_group_secrets) ->
      kp_ref_to_kp_secrets new_member == Some kp_secrets /\
      List.Tot.memP {new_member; encrypted_group_secrets} l
  )
let rec find_my_encrypted_group_secret_spec #bytes #cb kp_ref_to_kp_secrets l =
  match l with
  | [] -> ()
  | h::t -> (
    match kp_ref_to_kp_secrets h.new_member with
    | Some kp_secrets -> ()
    | None -> find_my_encrypted_group_secret_spec kp_ref_to_kp_secrets t
  )
#pop-options

#push-options "--fuel 0 --ifuel 1"
val decrypt_group_secrets_proof:
  {|crypto_invariants|} ->
  tr:trace ->
  me:principal -> my_leaf_pk:bytes ->
  my_hpke_sk:hpke_private_key bytes -> my_hpke_ciphertext:hpke_ciphertext_nt bytes -> ad:bytes ->
  Lemma
  (requires
    bytes_invariant tr my_hpke_sk /\
    my_hpke_sk `has_usage tr` init_key_usage me my_leaf_pk /\
    bytes_invariant tr my_hpke_ciphertext.kem_output /\
    bytes_invariant tr my_hpke_ciphertext.ciphertext /\
    bytes_invariant tr ad /\
    has_mls_encryptwithlabel_pred ("MLS.InitHpkeKey", "Welcome", mls_hpke_welcome_pred)
  )
  (ensures (
    match decrypt_group_secrets my_hpke_sk my_hpke_ciphertext ad with
    | Success group_secrets -> (
      bytes_invariant tr group_secrets.joiner_secret /\
      group_secrets.joiner_secret `has_usage tr` joiner_secret_usage
    )
    | _ -> True
  ))
let decrypt_group_secrets_proof tr me my_leaf_pk my_hpke_sk my_hpke_ciphertext ad =
    match decrypt_group_secrets my_hpke_sk my_hpke_ciphertext ad with
    | Success group_secrets -> (
      let Success kem_output = mk_hpke_kem_output (my_hpke_ciphertext.kem_output <: bytes) "decrypt_welcome" "kem_output" in
      assert(bytes_invariant tr kem_output);
      decrypt_with_label_welcome_lemma tr me my_leaf_pk my_hpke_sk ad kem_output my_hpke_ciphertext.ciphertext;
      let Success group_secrets_bytes = decrypt_with_label my_hpke_sk "Welcome" ad kem_output my_hpke_ciphertext.ciphertext in
      let Success group_secrets = from_option "decrypt_group_secrets: malformed group secrets" (parse (group_secrets_nt bytes) group_secrets_bytes) in
      FStar.Classical.move_requires (parse_wf_lemma (group_secrets_nt bytes) (is_publishable tr)) group_secrets_bytes;
      FStar.Classical.move_requires (parse_wf_lemma (group_secrets_nt bytes) (bytes_invariant tr)) group_secrets_bytes;
      FStar.Classical.move_requires (has_usage_publishable tr group_secrets.joiner_secret) joiner_secret_usage;
      ()
    )
    | _ -> ()
#pop-options

val decrypt_group_info_proof:
  {|crypto_invariants|} ->
  tr:trace ->
  joiner_secret:bytes -> encrypted_group_info:bytes ->
  Lemma
  (requires
    bytes_invariant tr encrypted_group_info /\
    bytes_invariant tr joiner_secret /\
    joiner_secret `has_usage tr` joiner_secret_usage /\
    has_mls_keyschedule_invariants
  )
  (ensures (
    match decrypt_group_info joiner_secret encrypted_group_info with
    | Success group_info -> (
      is_well_formed _ (bytes_invariant tr) group_info
    )
    | _ -> True
  ))
let decrypt_group_info_proof tr joiner_secret encrypted_group_info =
  match decrypt_group_info joiner_secret encrypted_group_info with
  | Success group_info -> (
    let Success welcome_secret = secret_joiner_to_welcome #bytes joiner_secret None in
    let Success welcome_key = welcome_secret_to_key #bytes welcome_secret in
    let Success welcome_nonce = welcome_secret_to_nonce welcome_secret in
    let Success group_info_bytes = aead_decrypt welcome_key welcome_nonce empty encrypted_group_info in
    assert(Success group_info == from_option "decrypt_group_info: malformed group info" (parse (group_info_nt bytes) group_info_bytes));
    secret_joiner_to_welcome_proof tr joiner_secret None;
    welcome_secret_to_key_proof tr welcome_secret;
    welcome_secret_to_nonce_proof tr welcome_secret;
    assert(bytes_invariant tr welcome_key);
    assert(bytes_invariant tr welcome_nonce);
    assert(bytes_invariant tr empty);
    assert(bytes_invariant tr encrypted_group_info);
    assert(bytes_invariant tr group_info_bytes);
    parse_wf_lemma (group_info_nt bytes) (bytes_invariant tr) group_info_bytes;
    ()
  )
  | _ -> ()

val decrypt_welcome_proof:
  {|crypto_invariants|} ->
  #a:Type ->
  tr:trace ->
  welcome:welcome_nt bytes -> kp_ref_to_kp_secrets:(bytes -> option a) -> kp_secrets_to_hpke_sk:(a -> result (hpke_private_key bytes)) ->
  Lemma
  (requires
    is_well_formed _ (bytes_invariant tr) welcome /\
    (forall kp_ref.
      let opt_kp_secrets = kp_ref_to_kp_secrets kp_ref in
      match opt_kp_secrets with
      | None -> True
      | Some kp_secrets -> (
        match kp_secrets_to_hpke_sk kp_secrets with
        | Success hpke_sk ->
          bytes_invariant tr hpke_sk /\
          (exists prin leaf_pk. hpke_sk `has_usage tr` init_key_usage prin leaf_pk)
        | _ -> True
      )
    ) /\
    has_mls_keyschedule_invariants /\
    has_mls_encryptwithlabel_pred ("MLS.InitHpkeKey", "Welcome", mls_hpke_welcome_pred)
  )
  (ensures (
    match decrypt_welcome welcome kp_ref_to_kp_secrets kp_secrets_to_hpke_sk with
    | Success (group_info, group_secrets, (my_kp_ref,  my_kp_secrets)) -> (
      is_well_formed _ (bytes_invariant tr) group_info /\
      bytes_invariant tr group_secrets.joiner_secret /\
      group_secrets.joiner_secret `has_usage tr` joiner_secret_usage /\
      kp_ref_to_kp_secrets my_kp_ref == Some my_kp_secrets
    )
    | _ -> True
  ))
let decrypt_welcome_proof tr welcome kp_ref_to_kp_secrets kp_secrets_to_hpke_sk =
  match decrypt_welcome welcome kp_ref_to_kp_secrets kp_secrets_to_hpke_sk with
  | Success _ -> (
    let Success (my_kp_ref, my_kp_secrets, my_hpke_ciphertext) = from_option "decrypt_welcome: can't find my encrypted secret" (find_my_encrypted_group_secret kp_ref_to_kp_secrets welcome.secrets) in
    let Success my_hpke_sk = kp_secrets_to_hpke_sk my_kp_secrets in
    let Success group_secrets = decrypt_group_secrets my_hpke_sk my_hpke_ciphertext welcome.encrypted_group_info in
    let Success group_info = decrypt_group_info (group_secrets.joiner_secret <: bytes) welcome.encrypted_group_info in
    assert(Success (group_info, group_secrets, (my_kp_ref, my_kp_secrets)) == decrypt_welcome welcome kp_ref_to_kp_secrets kp_secrets_to_hpke_sk);
    find_my_encrypted_group_secret_spec kp_ref_to_kp_secrets welcome.secrets;
    for_allP_eq (is_well_formed_prefix (ps_encrypted_group_secrets_nt) (bytes_invariant tr)) welcome.secrets;
    assert(is_well_formed_prefix (ps_encrypted_group_secrets_nt) (bytes_invariant tr) {new_member = my_kp_ref; encrypted_group_secrets = my_hpke_ciphertext;});
    assert(bytes_invariant tr my_hpke_sk);
    eliminate exists prin leaf_pk. my_hpke_sk `has_usage tr` init_key_usage prin leaf_pk
    returns 
      bytes_invariant tr group_secrets.joiner_secret /\
      group_secrets.joiner_secret `has_usage tr` joiner_secret_usage
    with _. (
      decrypt_group_secrets_proof tr prin leaf_pk my_hpke_sk my_hpke_ciphertext welcome.encrypted_group_info
    );
    decrypt_group_info_proof tr (group_secrets.joiner_secret <: bytes) welcome.encrypted_group_info;
    ()
  )
  | _ -> ()

(*** Encryption ***)

#push-options "--z3rlimit 25"
val encrypt_one_group_secrets_proof:
  {|protocol_invariants|} ->
  tr:trace -> me:principal ->
  key_package:key_package_nt bytes tkt -> encrypted_group_info:bytes -> group_secrets:group_secrets_nt bytes -> entropy:lbytes bytes (hpke_private_key_length #bytes) ->
  Lemma
  (requires
    Some? (key_package_to_principal key_package) /\
    is_well_formed _ (is_publishable tr) key_package /\
    is_publishable tr encrypted_group_info /\

    is_knowable_by (key_package_to_init_label key_package) tr group_secrets.joiner_secret /\
    group_secrets.joiner_secret `has_usage tr` joiner_secret_usage /\
    (
      match group_secrets.path_secret with
      | Some path_secret ->
        is_knowable_by (key_package_to_init_label key_package) tr path_secret.path_secret /\
        get_label tr path_secret.path_secret `can_flow tr` node_key_label (Some?.v (key_package_to_principal key_package)) key_package.tbs.leaf_node.data.content /\
        (exists data. path_secret.path_secret `has_usage tr` (KdfExpandKey "MLS.PathSecret" data))
      | None -> True
    ) /\
    for_allP (is_well_formed_prefix ps_pre_shared_key_id_nt (is_publishable tr)) group_secrets.psks /\

    bytes_invariant tr entropy /\
    get_label tr entropy == key_package_to_init_label key_package /\
    entropy `has_usage tr` entropy_usage_for_init_key (Some?.v (key_package_to_principal key_package)) (key_package.tbs.leaf_node.data.content) /\

    i_have_verified_key_package tr me key_package /\
    trace_invariant tr /\
    has_mls_encryptwithlabel_pred ("MLS.InitHpkeKey", "Welcome", mls_hpke_welcome_pred) /\
    has_key_package_invariant
  )
  (ensures (
    match encrypt_one_group_secrets key_package encrypted_group_info group_secrets entropy with
    | Success encrypted_group_secrets ->
      is_well_formed_prefix ps_encrypted_group_secrets_nt (is_publishable tr) encrypted_group_secrets
    | _ -> True
  ))
let encrypt_one_group_secrets_proof #invs tr me key_package encrypted_group_info group_secrets entropy =
  match encrypt_one_group_secrets key_package encrypted_group_info group_secrets entropy with
  | Success encrypted_group_secrets -> (
    let Success kp_ref = compute_key_package_ref key_package in
    compute_key_package_ref_is_knowable_by tr public key_package;
    let gs_bytes = serialize #bytes (group_secrets_nt bytes) group_secrets in
    let Success leaf_hpke_pk = mk_hpke_public_key key_package.tbs.init_key "encrypt_one_group_secrets" "leaf_hpke_pk" in
    let Success (kem_output, ciphertext) = encrypt_with_label leaf_hpke_pk "Welcome" encrypted_group_info gs_bytes entropy in

    key_package_to_init_label_lemma tr me key_package;

    for_allP_eq (is_well_formed_prefix ps_pre_shared_key_id_nt (is_publishable tr)) group_secrets.psks;
    for_allP_eq (is_well_formed_prefix ps_pre_shared_key_id_nt (is_knowable_by (key_package_to_init_label key_package) tr)) group_secrets.psks;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (is_well_formed_prefix_weaken ps_pre_shared_key_id_nt (is_publishable tr) (is_knowable_by (key_package_to_init_label key_package) tr)));
    allow_inversion (option (path_secret_nt bytes));
    assert(is_well_formed_prefix ps_group_secrets_nt (is_knowable_by (key_package_to_init_label key_package) tr) group_secrets);
    serialize_wf_lemma _ (is_knowable_by (key_package_to_init_label key_package) tr) group_secrets;

    bytes_invariant_encrypt_with_label
      mls_hpke_welcome_pred "MLS.InitHpkeKey" (init_key_usage_data (Some?.v (key_package_to_principal key_package)) (key_package.tbs.leaf_node.data.content))
      tr leaf_hpke_pk "Welcome" encrypted_group_info gs_bytes entropy
    ;
    ()
  )
  | _ -> ()
#pop-options
