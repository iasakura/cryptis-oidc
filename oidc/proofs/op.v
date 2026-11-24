From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis.examples Require Import alist.
From oidc Require Import impl game.
From oidc.proofs Require Import base tls.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*

The provider.  Its four tables are owned by the thread that runs [OP.serve];
what the rest of the system needs to know about their contents is persistent.

*)

Section OP.

Context `{!heapGS Σ, !cryptisGS Σ, !oidcParams}.
Notation iProp := (iProp Σ).

Implicit Types (C U S G : gmap term term).
Implicit Types (Ψ : val → iProp).

(* Registered clients.  The honest client's redirect URI is the relying
   party's callback; every other client belongs to the attacker. *)
Definition clients_ok C : iProp :=
  ∀ cl e, ⌜C !! cl = Some e⌝ →
    public cl ∗ public e ∗
    ⌜cl = hcid → ∃ sec, e = Spec.of_list [rp_host; rp_cb; sec]⌝.

(* Accounts.  The honest user's password is [hpw]. *)
Definition users_ok U : iProp :=
  ∀ s p, ⌜U !! s = Some p⌝ → public s ∗ ⌜s = hsub → p = hpw⌝.

Definition op_sessions_ok S : iProp :=
  ∀ c s, ⌜S !! c = Some s⌝ → op_session c s.

Definition codes_ok G : iProp :=
  ∀ code g, ⌜G !! code = Some g⌝ →
    ∃ s cl nonce ch,
      ⌜g = Spec.of_list [s; cl; nonce; ch]⌝ ∗
      code_grant code s cl ∗
      public nonce.

(* The provider's state, with the contents of its tables exposed.  This does
   not depend on who the honest user is: the game creates the provider before
   the user. *)
Definition op_state (skS : sign_key) (skT : aenc_key) (op : val) C U S G
    : iProp :=
  ∃ vc vu vs vg : val,
    ⌜op = (skS, skT, vc, vu, vs, vg)%V⌝ ∗
    tmap vc C ∗ tmap vu U ∗ tmap vs S ∗ tmap vg G.

Definition op_inv (op : val) : iProp :=
  ∃ C U S G,
    op_state skOP skOPt op C U S G ∗
    clients_ok C ∗ users_ok U ∗ op_sessions_ok S ∗ codes_ok G.

Lemma op_inv_intro (vc vu vs vg : val) C U S G :
  tmap vc C -∗ tmap vu U -∗ tmap vs S -∗ tmap vg G -∗
  clients_ok C -∗ users_ok U -∗ op_sessions_ok S -∗ codes_ok G -∗
  op_inv (skOP, skOPt, vc, vu, vs, vg)%V.
Proof.
iIntros "? ? ? ? ? ? ? ?". iExists C, U, S, G. by iFrame.
Qed.

Lemma clients_ok_empty : ⊢ clients_ok ∅.
Proof. iIntros "%x %y %lk". by rewrite lookup_empty in lk. Qed.

Lemma users_ok_empty : ⊢ users_ok ∅.
Proof. iIntros "%x %y %lk". by rewrite lookup_empty in lk. Qed.

Lemma op_sessions_ok_empty : ⊢ op_sessions_ok ∅.
Proof. iIntros "%x %y %lk". by rewrite lookup_empty in lk. Qed.

Lemma codes_ok_empty : ⊢ codes_ok ∅.
Proof. iIntros "%x %y %lk". by rewrite lookup_empty in lk. Qed.

Lemma clients_ok_insert C (cl rhost rpath sec : term) :
  clients_ok C -∗
  public cl -∗ public rhost -∗ public rpath -∗ public sec -∗
  ⌜cl = hcid → rhost = rp_host ∧ rpath = rp_cb⌝ -∗
  clients_ok (<[cl := Spec.of_list [rhost; rpath; sec]]> C).
Proof.
iIntros "#C_ok #p_cl #p_rhost #p_rpath #p_sec %cl_e %cl' %e' %lk".
case/lookup_insert_Some: lk => [[<- <-]|[_ lk]]; last by iApply "C_ok".
rewrite public_of_list /=. do !iSplit => //.
iPureIntro => /cl_e [-> ->]. by eauto.
Qed.

Lemma users_ok_insert U (s p : term) :
  users_ok U -∗
  public s -∗
  ⌜s = hsub → p = hpw⌝ -∗
  users_ok (<[s := p]> U).
Proof.
iIntros "#U_ok #p_s %s_p %s' %p' %lk".
case/lookup_insert_Some: lk => [[<- <-]|[_ lk]]; last by iApply "U_ok".
by iSplit.
Qed.

(** ** Accessors. *)

Lemma wp_op_sign_sk (a b c d e f : val) Ψ :
  Ψ a ⊢ WP OP.sign_sk (a, b, c, d, e, f)%V {{ Ψ }}.
Proof. iIntros "?". rewrite /OP.sign_sk. by wp_pures. Qed.

Lemma wp_op_clients (a b c d e f : val) Ψ :
  Ψ c ⊢ WP OP.clients (a, b, c, d, e, f)%V {{ Ψ }}.
Proof. iIntros "?". rewrite /OP.clients. by wp_pures. Qed.

Lemma wp_op_users (a b c d e f : val) Ψ :
  Ψ d ⊢ WP OP.users (a, b, c, d, e, f)%V {{ Ψ }}.
Proof. iIntros "?". rewrite /OP.users. by wp_pures. Qed.

Lemma wp_op_sessions (a b c d e f : val) Ψ :
  Ψ e ⊢ WP OP.sessions (a, b, c, d, e, f)%V {{ Ψ }}.
Proof. iIntros "?". rewrite /OP.sessions. by wp_pures. Qed.

Lemma wp_op_codes (a b c d e f : val) Ψ :
  Ψ f ⊢ WP OP.codes (a, b, c, d, e, f)%V {{ Ψ }}.
Proof. iIntros "?". rewrite /OP.codes. by wp_pures. Qed.

Lemma wp_op_iss (b c d e f : val) Ψ :
  Ψ hiss ⊢ WP OP.iss (skOP, b, c, d, e, f)%V {{ Ψ }}.
Proof.
iIntros "?". rewrite /OP.iss. wp_pures. wp_apply wp_op_sign_sk.
by wp_apply wp_pkey.
Qed.

Lemma wp_op_tls_sk op Ψ :
  op_inv op -∗ (op_inv op -∗ Ψ skOPt) -∗ WP OP.tls_sk op {{ Ψ }}.
Proof.
iIntros "inv post".
iDestruct "inv" as "(%C & %U & %S & %G &
                     (%vc & %vu & %vs & %vg & -> & HC & HU & HS & HG) & ok)".
rewrite /OP.tls_sk. wp_pures. iApply "post".
iExists C, U, S, G. by iFrame.
Qed.

(** ** Setting up. *)

Lemma wp_op_new (skS : sign_key) (skT : aenc_key) :
  {{{ True }}} OP.new skS skT {{{ op, RET op; op_state skS skT op ∅ ∅ ∅ ∅ }}}.
Proof.
iIntros "%Φ _ post". wp_lam. wp_pures.
wp_apply wp_tmap_new => //. iIntros "%vg Hg".
wp_apply wp_tmap_new => //. iIntros "%vs Hs".
wp_apply wp_tmap_new => //. iIntros "%vu Hu".
wp_apply wp_tmap_new => //. iIntros "%vc Hc".
wp_pures. iApply "post". iModIntro.
iExists vc, vu, vs, vg. by iFrame.
Qed.

Lemma wp_op_register_client_raw (skS : sign_key) (skT : aenc_key) op C U S G
    (cl rhost rpath sec : term) :
  {{{ op_state skS skT op C U S G }}}
    OP.register_client op cl rhost rpath sec
  {{{ RET #();
      op_state skS skT op (<[cl := Spec.of_list [rhost; rpath; sec]]> C)
        U S G }}}.
Proof.
iIntros "%Φ (%vc & %vu & %vs & %vg & -> & HC & HU & HS & HG) post".
wp_lam. wp_pures. wp_list. wp_tol.
wp_apply wp_op_clients. wp_apply (wp_tmap_insert with "HC"). iIntros "HC".
iApply "post". iExists vc, vu, vs, vg. by iFrame.
Qed.

Lemma wp_op_register_user_raw (skS : sign_key) (skT : aenc_key) op C U S G
    (s p : term) :
  {{{ op_state skS skT op C U S G }}}
    OP.register_user op s p
  {{{ RET #(); op_state skS skT op C (<[s := p]> U) S G }}}.
Proof.
iIntros "%Φ (%vc & %vu & %vs & %vg & -> & HC & HU & HS & HG) post".
wp_lam. wp_pures.
wp_apply wp_op_users. wp_apply (wp_tmap_insert with "HU"). iIntros "HU".
iApply "post". iExists vc, vu, vs, vg. by iFrame.
Qed.

Lemma wp_op_register_client op (cl rhost rpath sec : term) :
  public cl -∗ public rhost -∗ public rpath -∗ public sec -∗
  ⌜cl = hcid → rhost = rp_host ∧ rpath = rp_cb⌝ -∗
  {{{ op_inv op }}}
    OP.register_client op cl rhost rpath sec
  {{{ RET #(); op_inv op }}}.
Proof.
iIntros "#p_cl #p_rhost #p_rpath #p_sec %cl_e !> %Φ inv post".
iDestruct "inv" as "(%C & %U & %S & %G & st & #C_ok & #U_ok & #S_ok & #G_ok)".
wp_apply (wp_op_register_client_raw with "st"). iIntros "st".
iApply "post". iExists _, U, S, G. iFrame "∗ #".
by iApply clients_ok_insert.
Qed.

Lemma wp_op_register_user op (s p : term) :
  public s -∗
  ⌜s = hsub → p = hpw⌝ -∗
  {{{ op_inv op }}}
    OP.register_user op s p
  {{{ RET #(); op_inv op }}}.
Proof.
iIntros "#p_s %s_p !> %Φ inv post".
iDestruct "inv" as "(%C & %U & %S & %G & st & #C_ok & #U_ok & #S_ok & #G_ok)".
wp_apply (wp_op_register_user_raw with "st"). iIntros "st".
iApply "post". iExists C, _, S, G. iFrame "∗ #".
by iApply users_ok_insert.
Qed.

(** ** The endpoints.

    Each one is specified against a flag [pub] that says where the request came
    from: [pub = true] means the attacker made it, so that whatever goes into
    the response must be public; [pub = false] means an honest client did, and
    the response has to satisfy the endpoint's part of [resp_ok]. *)

Ltac op_fail :=
  by intros; wp_pures; iApply ("post" $! None); iModIntro; iSplit => //;
     iApply (op_inv_intro with "HC HU HS HG").

Lemma wp_op_handle_login op (pub : bool) params :
  cryptis_ctx -∗
  oidc_ctx -∗
  minted params -∗
  (if pub then public params else True) -∗
  {{{ op_inv op }}}
    OP.handle_login op params
  {{{ (r : option term), RET (repr r);
      op_inv op ∗
      match r with
      | Some resp =>
          minted resp ∗
          if pub then public resp else op_login_resp params resp
      | None => True
      end }}}.
Proof.
iIntros "#ctx #octx #m_params #p_params !> %Φ inv post". octx_destruct.
iDestruct "inv" as "(%C & %U & %S & %G &
                     (%vc & %vu & %vs & %vg & -> & HC & HU & HS & HG) &
                     #C_ok & #U_ok & #S_ok & #G_ok)".
wp_lam. wp_pures.
wp_list_of_term params; last op_fail.
wp_list_match => [s p ->|_]; last op_fail.
wp_apply wp_op_users. wp_apply (wp_tmap_find with "HU"). iIntros "HU".
case U_s: (U !! s) => [p0|]; last op_fail.
wp_pures.
wp_eq_term e; last op_fail. subst p0.
iPoseProof ("U_ok" $! s p with "[//]") as "[#p_s %s_p]".
wp_pures.
wp_apply (wp_mk_nonce (λ _, ⌜pub = true⌝)%I (λ _, False)%I) => //.
iIntros "%sid #m_sid #s_sid _ _ tok".
iMod (term_meta_set sessN s with "tok") as "#meta"; first solve_ndisj.
(* The cookie of the honest user is hidden: only the user knows the password,
   and the user's requests have a hidden response key. *)
iAssert (⌜s = hsub⌝ → hidden sid)%I as "#h_sid".
{ iIntros "%e". case: pub; last by iApply nonce_pub_false.
  rewrite public_of_list /=. iDestruct "p_params" as "(_ & p_p & _)".
  rewrite (s_p e). iApply hidden_false. by iApply "h_hpw". }
iAssert (op_session sid s) as "#sess". { by do !iSplit. }
wp_pures. wp_apply wp_op_sessions.
wp_apply (wp_tmap_insert with "HS"). iIntros "HS".
wp_pures. wp_apply wp_http_page. wp_pures.
iApply ("post" $! (Some (http_page sid (TInt 0)))). iModIntro.
iSplitL.
{ iApply (op_inv_intro with "HC HU HS HG") => //.
  iIntros "%c' %s' %lk".
  by case/lookup_insert_Some: lk => [[<- <-]|[_ lk]]; last by iApply "S_ok". }
iSplit.
{ term_simpl. by eauto. }
case: pub.
- term_simpl. do !iSplit => //. by iApply nonce_pub_true.
- iExists s, p, sid. do !iSplit => //. by iApply nonce_pub_false.
Qed.

Lemma wp_op_handle_authorize op (pub : bool) params cookie :
  cryptis_ctx -∗
  oidc_ctx -∗
  public params -∗
  (if pub then public cookie else True) -∗
  {{{ op_inv op }}}
    OP.handle_authorize op params cookie
  {{{ (r : option term), RET (repr r);
      op_inv op ∗
      match r with
      | Some resp =>
          minted resp ∗
          if pub then public resp
          else op_authorize_resp params cookie resp
      | None => True
      end }}}.
Proof.
iIntros "#ctx #octx #p_params #p_cookie !> %Φ inv post". octx_destruct.
iDestruct "inv" as "(%C & %U & %S & %G &
                     (%vc & %vu & %vs & %vg & -> & HC & HU & HS & HG) &
                     #C_ok & #U_ok & #S_ok & #G_ok)".
wp_lam. wp_pures.
wp_list_of_term params; last op_fail.
wp_list_match => [cl redir state nonce ch ->|_]; last op_fail.
rewrite public_of_list /=.
iDestruct "p_params" as "(p_cl & p_redir & p_state & p_nonce & p_ch & _)".
wp_apply wp_op_sessions. wp_apply (wp_tmap_find with "HS"). iIntros "HS".
case S_c: (S !! cookie) => [s|]; last op_fail.
wp_pures.
iPoseProof ("S_ok" $! cookie s with "[//]") as "#sess".
wp_apply wp_op_clients. wp_apply (wp_tmap_find with "HC"). iIntros "HC".
case C_cl: (C !! cl) => [e|]; last op_fail.
wp_pures.
iPoseProof ("C_ok" $! cl e with "[//]") as "(_ & #p_e & %cl_e)".
wp_list_of_term_eq l el; last op_fail. subst e.
wp_list_match => [rhost rpath sec el|_]; last op_fail. subst l.
rewrite public_of_list /=.
iDestruct "p_e" as "(p_rhost & p_rpath & p_sec & _)".
wp_list. wp_tol. wp_eq_term e; last op_fail.
wp_pures.
wp_apply (wp_mk_nonce (λ _, ⌜pub = true ∨ cl ≠ hcid⌝)%I (λ _, False)%I) => //.
iIntros "%code #m_code #s_code _ _ tok".
iMod (term_meta_set grantN (s, cl) with "tok") as "#meta"; first solve_ndisj.
iPoseProof "sess" as "(_ & #p_s & _ & #h_c)".
(* A code for the honest user and the honest client is hidden: it goes to
   whoever sent the user's cookie, and that cookie is hidden. *)
iAssert (⌜cl = hcid ∧ s = hsub⌝ → hidden code)%I as "#h_code".
{ iIntros "[%e_cl %e_s]". case: pub.
  - iApply hidden_false. by iApply ("h_c" with "[//]").
  - iIntros "!> #p". iPoseProof ("s_code" with "p") as "{p} p".
    iModIntro. iDestruct "p" as "%p". by case: p. }
iAssert (code_grant code s cl) as "#grant". { by do !iSplit. }
wp_pures. wp_list. wp_tol.
wp_apply wp_op_codes. wp_apply (wp_tmap_insert with "HG"). iIntros "HG".
wp_pures. wp_apply wp_op_iss. wp_list. wp_tol.
wp_apply wp_http_redirect. wp_pures.
iApply ("post" $! (Some (http_redirect (TInt 0) rhost rpath
                           (Spec.of_list [(code : term); state; hiss])))).
iModIntro. iSplitL.
{ iApply (op_inv_intro with "HC HU HS HG") => //.
  iIntros "%code' %g' %lk".
  case/lookup_insert_Some: lk => [[<- <-]|[_ lk]]; last by iApply "G_ok".
  iExists s, cl, nonce, ch. by eauto. }
iSplit.
{ term_simpl. do !iSplit => //; by iApply public_minted. }
case: pub.
- term_simpl. do !iSplit => //.
  iApply "s_code". iIntros "!> !>". by eauto.
- iExists cl, redir, state, nonce, ch, s, rhost, rpath, code.
  do !iSplit => //.
  + iPureIntro => /cl_e [sec'] /Spec.of_list_inj. by case.
  + iIntros "%ne". iApply "s_code". iIntros "!> !>". by eauto.
Qed.

Lemma wp_op_handle_token op params :
  cryptis_ctx -∗
  oidc_ctx -∗
  {{{ op_inv op }}}
    OP.handle_token op params
  {{{ (r : option term), RET (repr r);
      op_inv op ∗
      match r with
      | Some resp => public resp ∗ op_token_resp params resp
      | None => True
      end }}}.
Proof.
iIntros "#ctx #octx !> %Φ inv post". octx_destruct.
iPoseProof "octx" as "(#? & _)".
iDestruct "inv" as "(%C & %U & %S & %G &
                     (%vc & %vu & %vs & %vg & -> & HC & HU & HS & HG) &
                     #C_ok & #U_ok & #S_ok & #G_ok)".
wp_lam. wp_pures.
wp_list_of_term params; last op_fail.
wp_list_match => [cl sec code verifier ->|_]; last op_fail.
wp_apply wp_op_clients. wp_apply (wp_tmap_find with "HC"). iIntros "HC".
case C_cl: (C !! cl) => [e|]; last op_fail.
wp_pures.
wp_list_of_term_eq l el; last op_fail. subst e.
wp_list_match => [rhost rpath sec0 el|_]; last op_fail. subst l.
wp_eq_term e; last op_fail. subst sec0.
wp_pures.
wp_apply wp_op_codes. wp_apply (wp_tmap_find with "HG"). iIntros "HG".
case G_code: (G !! code) => [g|]; last op_fail.
wp_pures.
iPoseProof ("G_ok" $! code g with "[//]")
  as "(%s & %cl0 & %nonce & %ch & -> & #grant & #p_nonce)".
iAssert (codes_ok (delete code G)) as "#G_ok'".
{ iIntros "%code' %g' %lk".
  case/lookup_delete_Some: lk => [_ lk]. by iApply "G_ok". }
wp_apply wp_op_codes. wp_apply (wp_tmap_delete with "HG"). iIntros "HG".
wp_pures.
wp_list_of_term_eq l' el; last op_fail.
move/Spec.of_list_inj: el => el. subst l'.
wp_list_match => [s' cl0' nonce' ch' [<- <- <- <-]|ne]; last by case: ne.
wp_eq_term e; last op_fail. subst cl0.
wp_hash. wp_eq_term e; last op_fail.
iPoseProof "grant" as "(_ & #p_s & #p_cl & _)".
wp_pures. wp_list. wp_apply wp_op_iss. wp_list. wp_tol.
wp_apply wp_op_sign_sk. wp_bind (sign _ _ _). iApply wp_sign'. iModIntro.
wp_pures. wp_list. wp_tol. wp_apply wp_http_page. wp_pures.
iAssert (public (id_token s cl nonce)) as "#p_tok".
{ iApply public_signIS => //.
  - rewrite public_of_list /=. by eauto.
  - iModIntro. iExists code, s, cl, nonce. by eauto. }
iAssert (public (http_page (TInt 0) (Spec.of_list [id_token s cl nonce])))
  as "#p_resp".
{ rewrite /http_page public_of_list /= public_tag public_of_list /=.
  rewrite public_TInt. by eauto. }
iApply ("post" $! (Some (http_page (TInt 0)
                           (Spec.of_list [id_token s cl nonce])))).
iModIntro. iSplitL.
{ by iApply (op_inv_intro with "HC HU HS HG"). }
iSplit => //.
iExists cl, sec, code, verifier, s, nonce. by eauto.
Qed.

Lemma wp_op_handler op kResp req :
  cryptis_ctx -∗
  oidc_ctx -∗
  minted req -∗
  req_from kResp req -∗
  {{{ op_inv op }}}
    OP.handler op req
  {{{ (r : option term), RET (repr r);
      op_inv op ∗
      match r with
      | Some resp => resp_for kResp resp
      | None => True
      end }}}.
Proof.
iIntros "#ctx #octx #m_req #req !> %Φ inv post".
wp_lam. wp_pures.
wp_list_of_term req; last by wp_pures; iApply ("post" $! None); iFrame.
wp_list_match => [path params cookie ->|_];
  last by wp_pures; iApply ("post" $! None); iFrame.
iPoseProof (req_from_view with "req") as "(%pub & #view)".
rewrite minted_of_list /=. iDestruct "m_req" as "(m_path & m_params & m_cookie & _)".
wp_eq_term e.
{ subst path. wp_pures.
  wp_apply (wp_op_handle_login _ pub with "ctx octx m_params [] inv").
  { case: pub => //. by iDestruct "view" as "(_ & _ & ? & _)". }
  iIntros "%r [inv Hr]". case: r => [resp|]; last first.
  { iApply ("post" $! None). by iFrame. }
  iDestruct "Hr" as "[#m_resp #Hr]".
  iApply ("post" $! (Some resp)). iFrame.
  iApply (resp_for_intro with "view m_resp").
  case: pub => //. iLeft. by eauto. }
wp_eq_term e'.
{ subst path. wp_pures.
  iAssert (public params) as "#p_params".
  { case: pub.
    - by iDestruct "view" as "(_ & _ & ? & _)".
    - iDestruct "view" as "(%k & _ & _ & _ & _ & p & _)". by iApply "p". }
  wp_apply (wp_op_handle_authorize _ pub with "ctx octx p_params [] inv").
  { case: pub => //. by iDestruct "view" as "(_ & _ & _ & ?)". }
  iIntros "%r [inv Hr]". case: r => [resp|]; last first.
  { iApply ("post" $! None). by iFrame. }
  iDestruct "Hr" as "[#m_resp #Hr]".
  iApply ("post" $! (Some resp)). iFrame.
  iApply (resp_for_intro with "view m_resp").
  case: pub => //. iRight. iLeft. by eauto. }
wp_eq_term e''.
{ subst path. wp_pures.
  wp_apply (wp_op_handle_token with "ctx octx inv").
  iIntros "%r [inv Hr]". case: r => [resp|]; last first.
  { iApply ("post" $! None). by iFrame. }
  iDestruct "Hr" as "[#p_resp #Hr]".
  iApply ("post" $! (Some resp)). iFrame.
  iApply (resp_for_intro with "view"); first by iApply public_minted.
  case: pub => //. iRight. iRight. iLeft. by eauto. }
wp_pures. iApply ("post" $! None). by iFrame.
Qed.

Lemma wp_op_listen c op :
  channel c -∗
  cryptis_ctx -∗
  oidc_ctx -∗
  {{{ op_inv op }}} OP.listen c op {{{ RET #(); op_inv op }}}.
Proof.
iIntros "#chan #ctx #octx !> %Φ inv post".
wp_lam. wp_pures.
wp_apply (wp_op_tls_sk with "inv"). iIntros "inv".
wp_apply (wp_tls_listen with "chan octx").
iIntros "%kResp %req #m_k #m_req #req".
wp_pures.
wp_apply (wp_op_handler with "ctx octx m_req req inv").
iIntros "%r [inv Hr]". case: r => [resp|]; wp_pures; last by iApply "post".
wp_apply (wp_tls_respond with "chan octx Hr"). by iApply "post".
Qed.

Lemma wp_op_serve c op :
  channel c -∗
  cryptis_ctx -∗
  oidc_ctx -∗
  op_inv op -∗
  WP OP.serve c op {{ _, True }}.
Proof.
iIntros "#chan #ctx #octx inv". iLöb as "IH".
wp_rec. wp_pures.
wp_apply (wp_op_listen with "chan ctx octx inv"). iIntros "inv".
wp_pures. by iApply "IH".
Qed.

End OP.
