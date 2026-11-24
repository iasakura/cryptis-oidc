From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.heap_lang Require Import notation proofmode adequacy.
From iris.heap_lang.lib Require Import assert.
From cryptis Require Import lib term cryptis primitives tactics adequacy.
From cryptis.examples Require Import alist.
From oidc Require Import impl game.
From oidc.proofs Require Import base tls op rp browser.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*

The security game of [game.v] is won: [oidc_is_secure], at the end of this
file.

*)

Section Game.

Context `{!heapGS Σ, !cryptisGS Σ, !oidcParams}.
Notation iProp := (iProp Σ).

Implicit Types (J : gmap term term).

(** ** The honest user. *)

Lemma wp_browse c b J :
  channel c -∗
  cryptis_ctx -∗
  oidc_ctx -∗
  jar_ok J -∗
  browser b J -∗
  WP browse c b {{ _, ∃ J', browser b J' ∗ jar_ok J' }}.
Proof.
iIntros "#chan #ctx #octx". iLöb as "IH" forall (J). iIntros "#jar Hb".
wp_rec. wp_pures.
wp_apply wp_recv => //. iIntros "%url #p_url".
wp_list_of_term url; last first.
{ wp_pures. iExists J. by iFrame. }
wp_list_match => [host path params ->|_]; last first.
{ wp_pures. iExists J. by iFrame. }
rewrite public_of_list /=.
iDestruct "p_url" as "(p_host & p_path & p_params & _)".
wp_apply (wp_browser_navigate with "chan ctx octx"). iIntros "%f #step".
wp_bind (f _ _ _). iApply (wp_wand with "[Hb]").
{ iApply (wp_nav_generic with "octx step jar [] Hb").
  by iApply nav_ok_public. }
iIntros "%v (%J' & Hb & #jar')". wp_pures.
wp_bind (browse _ _). iApply (wp_wand with "[Hb]").
{ by iApply ("IH" with "jar' Hb"). }
iIntros "%v' (%J'' & Hb & #jar'')". wp_pures. iExists J''. by iFrame.
Qed.

(* W2.  The user's login at the relying party is three requests.  Each
   response is bound to its request by TLS, which is what links the page at
   the end to the cookie the provider handed out for the user's own
   password. *)
Lemma wp_user c b :
  channel c -∗
  cryptis_ctx -∗
  oidc_ctx -∗
  browser b ∅ -∗
  WP user c b hsub hpw hiss {{ _, True }}.
Proof.
iIntros "#chan #ctx #octx Hb". octx_destruct.
wp_lam. wp_pures.
(* The attacker sends the browser around. *)
wp_bind (browse _ _). iApply (wp_wand with "[Hb]").
{ iApply (wp_browse with "chan ctx octx [] Hb"). by iApply jar_ok_empty. }
iIntros "%v0 (%J1 & Hb & #jar1)". wp_pures.
(* The user logs in at the provider, and gets a cookie for [hsub]. *)
wp_list. wp_tol.
wp_apply (wp_browser_navigate with "chan ctx octx"). iIntros "%f #step".
wp_bind (f _ _ _).
iApply (wp_wand _ _ _
          (λ _, ∃ J2 opsid, browser b J2 ∗ jar_ok J2 ∗
                            ⌜J2 !! op_host = Some opsid⌝ ∗
                            op_session opsid hsub)%I with "[Hb]").
{ iApply ("step" with "jar1 [] Hb").
  { rewrite /nav_ok !constsE. term_simpl.
    do !iSplit => //; first by iApply public_minted.
    iRight. by iLeft. }
  iIntros "!> %resp #fp".
  iPoseProof "fp" as "[_ [[_ resp]|[%nhon _]]]"; last by case: nhon; left.
  iPoseProof (resp_ok_op_login with "resp")
    as "(%s & %p & %sid & %e_params & -> & #h_sid & #sess)".
  case/Spec.of_list_inj: e_params => <- _.
  iPoseProof (fetch_post_gen with "octx jar1 fp") as "[#jar2 _]".
  rewrite /nav_cont /http_page Spec.of_listK /= untag_redirect_page.
  iIntros "Hb". iExists _, sid. iFrame "Hb jar2 sess".
  iDestruct "sess" as "(_ & _ & %ne & _)". iPureIntro.
  exact: jar_store_lookup. }
iIntros "%v1 (%J2 & %opsid & Hb & #jar2 & %J2_op & #sess)". wp_pures.
(* The user starts a login at the relying party. *)
wp_list. wp_tol.
wp_apply (wp_browser_navigate with "chan ctx octx"). iIntros "%f' #step'".
wp_bind (f' _ _ _).
iApply (wp_wand _ _ _
          (λ v, ∃ J', browser b J' ∗ jar_ok J' ∗
                      ⌜v = SOMEV (Spec.of_list [hiss; hsub])⌝)%I with "[Hb]").
{ (* /login at the relying party: a redirect to the honest provider. *)
  iApply ("step'" with "jar2 [] Hb").
  { iApply nav_ok_public; rewrite ?constsE //. term_simpl. by iSplit. }
  iIntros "!> %resp #fp".
  iPoseProof "fp" as "[_ [[_ resp]|[%nhon _]]]"; last by case: nhon; right.
  iPoseProof (resp_ok_rp_login with "resp")
    as "(%i & %sid & %ophost & %state & %nonce & %ch & %e_params & -> &
         #h_sid & #p_ophost & #p_state & #p_nonce & #p_ch & %i_host)".
  case/Spec.of_list_inj: e_params => e_i.
  have ? := i_host (eq_sym e_i). subst ophost.
  iPoseProof (fetch_post_gen with "octx jar2 fp") as "[#jar3 #nav3]".
  rewrite /nav_cont /http_redirect Spec.of_listK /= Spec.tagK Spec.of_listK /=.
  iIntros "Hb".
  set J3 := jar_store J2 rp_host sid.
  have J3_op : J3 !! op_host = Some opsid.
  { rewrite /J3 jar_store_lookup_ne //. exact: not_eq_sym op_host_rp_host. }
  (* /authorize at the provider, with the user's cookie: a code for the
     user. *)
  iApply ("step'" with "jar3 [] Hb"); first by iApply "nav3".
  iIntros "!> %resp #fp'".
  iPoseProof "fp'" as "[_ [[_ resp']|[%nhon _]]]"; last by case: nhon; left.
  rewrite /cookie_of J3_op /=.
  iPoseProof (resp_ok_op_authorize with "resp'")
    as "(%cl & %redir & %state' & %nonce' & %ch' & %s & %rhost & %rpath &
         %code & %e_params & -> & #sess' & #grant & #p_rhost & #p_rpath &
         #p_state' & %cl_e & #p_code)".
  case/Spec.of_list_inj: e_params => e_cl _ _ _ _.
  case: (cl_e (eq_sym e_cl)) => ? ?. subst rhost rpath.
  iPoseProof (op_session_agree with "sess sess'") as "%e_s". subst s.
  iPoseProof (fetch_post_gen with "octx jar3 fp'") as "[#jar4 #nav4]".
  rewrite /nav_cont /http_redirect Spec.of_listK /= Spec.tagK Spec.of_listK /=.
  iIntros "Hb".
  (* /cb at the relying party, with that code: a page for the user. *)
  iApply ("step'" with "jar4 [] Hb"); first by iApply "nav4".
  iIntros "!> %resp #fp''".
  iPoseProof "fp''" as "[_ [[_ resp'']|[%nhon _]]]";
    last by case: nhon; right.
  iPoseProof (resp_ok_rp_cb with "resp''")
    as "(%code' & %state'' & %i' & %s' & %e_params & -> & #grant')".
  case/Spec.of_list_inj: e_params => ? _ ?. subst code' i'.
  iPoseProof ("grant'" with "[//]") as "{grant'} grant'".
  iPoseProof (code_grant_agree with "grant grant'") as "%e".
  case: e => ? _. subst s'.
  iPoseProof (fetch_post_gen with "octx jar4 fp''") as "[#jar5 _]".
  rewrite /nav_cont /http_page Spec.of_listK /= untag_redirect_page Spec.tagK.
  iIntros "Hb". iExists _. by iFrame "Hb jar5". }
iIntros "%v2 (%J' & Hb & #jar' & ->)". wp_pures.
(* W2 *)
wp_apply wp_assert. wp_list. wp_tol. wp_eq_term e; last by case: e.
iModIntro. iSplit => //. iModIntro. wp_pures.
iApply (wp_wand with "[Hb]").
{ by iApply (wp_browse with "chan ctx octx jar' Hb"). }
by iIntros.
Qed.

(** ** The relying party, with the W1 check. *)

Lemma wp_check_session c rp :
  channel c -∗
  {{{ rp_inv rp }}}
    check_session c rp (Spec.of_list [hiss; hsub])
  {{{ RET #(); rp_inv rp }}}.
Proof.
iIntros "#chan !> %Φ inv post". wp_lam. wp_pures.
wp_apply wp_recv => //. iIntros "%guess #p_guess". wp_pures.
wp_apply (wp_rp_find_login with "inv"). iIntros "%r inv #Hr".
case: r => [id'|]; wp_pures; last by iApply "post".
wp_apply wp_assert. wp_eq_term e.
- (* W1: a cookie logged in as the honest user is hidden, and the attacker
     has just sent this one. *)
  iPoseProof ("Hr" with "[//]") as "h".
  iPoseProof ("h" with "p_guess") as "contra".
  wp_pures. by iDestruct "contra" as "[]".
- wp_pures. iModIntro. iSplit => //. by iApply "post".
Qed.

Lemma wp_rp_loop c rp :
  channel c -∗
  cryptis_ctx -∗
  oidc_ctx -∗
  rp_inv rp -∗
  WP rp_loop c rp (Spec.of_list [hiss; hsub]) {{ _, True }}.
Proof.
iIntros "#chan #ctx #octx inv". iLöb as "IH". wp_rec. wp_pures.
wp_apply (wp_rp_listen with "chan ctx octx inv"). iIntros "inv". wp_pures.
wp_apply (wp_check_session with "chan inv"). iIntros "inv". wp_pures.
by iApply "IH".
Qed.

(** ** What the attacker registers. *)

Lemma wp_register_attacker c op rp :
  channel c -∗
  cryptis_ctx -∗
  oidc_ctx -∗
  {{{ op_inv op ∗ rp_inv rp }}}
    register_attacker c op rp hsub hcid hiss
  {{{ RET #(); op_inv op ∗ rp_inv rp }}}.
Proof.
iIntros "#chan #ctx #octx !> %Φ [Hop Hrp] post".
wp_lam. wp_pures.
(* An account, but not the honest user's. *)
wp_apply wp_recv => //. iIntros "%subA #p_subA". wp_pures.
wp_apply wp_recv => //. iIntros "%pwA #p_pwA". wp_pures.
wp_bind (if: _ then _ else _)%E.
iApply (wp_wand _ _ _ (λ _, op_inv op)%I with "[Hop]").
{ wp_eq_term e; wp_pures; first by iFrame.
  wp_apply (wp_op_register_user with "p_subA [] Hop"); first by iPureIntro.
  by iIntros "Hop". }
iIntros "%v Hop". wp_pures.
(* A client, but not the honest one. *)
wp_apply wp_recv => //. iIntros "%cidA #p_cidA". wp_pures.
wp_apply wp_recv => //. iIntros "%rhostA #p_rhostA". wp_pures.
wp_apply wp_recv => //. iIntros "%rpathA #p_rpathA". wp_pures.
wp_apply wp_recv => //. iIntros "%secretA #p_secretA". wp_pures.
wp_bind (if: _ then _ else _)%E.
iApply (wp_wand _ _ _ (λ _, op_inv op)%I with "[Hop]").
{ wp_eq_term e; wp_pures; first by iFrame.
  wp_apply (wp_op_register_client
              with "p_cidA p_rhostA p_rpathA p_secretA [] Hop");
    first by iPureIntro.
  by iIntros "Hop". }
iIntros "%v' Hop". wp_pures.
(* A provider, but not the honest issuer. *)
wp_apply wp_recv => //. iIntros "%issA #p_issA". wp_pures.
wp_apply wp_recv => //. iIntros "%ophostA #p_ophostA". wp_pures.
wp_apply wp_recv => //. iIntros "%optlsA #p_optlsA". wp_pures.
wp_apply wp_recv => //. iIntros "%secretP #p_secretP". wp_pures.
wp_apply wp_is_verify_key; first by iApply public_minted.
iSplit; last by wp_pures; iApply "post"; iFrame.
iIntros "%skV -> #m_skV". wp_pures.
wp_apply wp_is_aenc_key; first by iApply public_minted.
iSplit; last by wp_pures; iApply "post"; iFrame.
iIntros "%skT -> #m_skT". wp_pures.
wp_eq_term e; wp_pures; first by iApply "post"; iFrame.
wp_apply (wp_rp_register_provider
            with "m_skV p_ophostA m_skT p_secretP [] Hrp");
  first by iPureIntro.
iIntros "Hrp". iApply "post". by iFrame.
Qed.

End Game.

(** ** The game. *)

Section Main.

Context `{!heapGS Σ, !cryptisGS Σ}.
Notation iProp := (iProp Σ).

Lemma wp_game c :
  cryptis_ctx -∗
  channel c -∗
  seal_pred_token AENC ⊤ -∗
  seal_pred_token SIGN ⊤ -∗
  seal_pred_token SENC ⊤ -∗
  WP game c {{ _, True }}.
Proof.
iIntros "#ctx #chan aenc_tok sign_tok senc_tok". rewrite /game. wp_pures.
wp_apply (wp_mk_sign_key with "ctx"). iIntros "%skOP0 #mOP secOP _".
wp_pures. wp_apply (wp_mk_aenc_key with "ctx").
iIntros "%skOPt0 #mOPt secOPt _".
wp_pures. wp_apply (wp_mk_aenc_key with "ctx").
iIntros "%skRP0 #mRP secRP _".
iMod (freeze_secret with "secOP") as "#sOP".
iMod (freeze_secret with "secOPt") as "#sOPt".
iMod (freeze_secret with "secRP") as "#sRP".
wp_pures. wp_apply wp_pkey. wp_pures. wp_apply wp_pkey.
wp_pures. wp_apply wp_pkey. wp_pures.
wp_apply wp_send => //; first by iApply public_verify_key.
wp_pures. wp_apply wp_send => //; first by iApply public_aenc_key.
wp_pures. wp_apply wp_send => //; first by iApply public_aenc_key.
wp_pures. wp_apply wp_op_new => //. iIntros "%op Hop".
wp_pures. wp_apply wp_rp_new => //. iIntros "%rp Hrp".
wp_pures. wp_apply (wp_mk_nonce (λ _, True)%I (λ _, False)%I) => //.
iIntros "%csec #m_csec #s_csec _ _ _".
wp_pures. wp_apply (wp_op_register_client_raw with "Hop"). iIntros "Hop".
wp_pures. wp_apply (wp_rp_register_provider_raw with "Hrp"). iIntros "Hrp".
wp_pures. wp_apply (wp_mk_nonce (λ _, True)%I (λ _, False)%I) => //.
iIntros "%sub #m_sub #s_sub _ _ _".
wp_pures. wp_apply (wp_mk_nonce (λ _, False)%I (λ _, False)%I) => //.
iIntros "%pw #m_pw #s_pw _ _ _".
(* From here on the honest principals are fixed: state everything in terms of
   an abstract [oidcParams]. *)
pose (PR := OidcParams skOP0 skOPt0 skRP0 sub pw).
have e1 : skOP0 = @skOP PR by [].
have e2 : skOPt0 = @skOPt PR by [].
have e3 : skRP0 = @skRP PR by [].
have e4 : TNonce sub = @hsub PR by [].
have e5 : TNonce pw = @hpw PR by [].
clearbody PR. subst skOP0 skOPt0 skRP0. rewrite e4 e5 {e4 e5}.
iAssert (public csec) as "#p_csec". { iApply "s_csec". by iIntros "!> !>". }
iAssert (public hsub) as "#p_sub". { iApply "s_sub". by iIntros "!> !>". }
iAssert (hidden hpw) as "#h_pw".
{ iIntros "!> #p". iPoseProof ("s_pw" with "p") as "{p} p".
  iModIntro. by iDestruct "p" as "#[]". }
iAssert (hidden skOP) as "#hOP". { iIntros "!> #p". by iApply "sOP". }
iAssert (hidden skOPt) as "#hOPt". { iIntros "!> #p". by iApply "sOPt". }
iAssert (hidden skRP) as "#hRP". { iIntros "!> #p". by iApply "sRP". }
iMod (oidc_alloc with "sign_tok aenc_tok senc_tok mOP hOP mOPt hOPt mRP hRP
                       p_sub m_pw h_pw") as "#octx"; try solve_ndisj.
iPoseProof (oidc_ctx_public with "octx") as "(#p_iss & #p_cid & #p_oppk)".
iAssert (op_inv op) with "[Hop]" as "Hop".
{ iExists _, ∅, ∅, ∅. iFrame "Hop". do !iSplit.
  - iApply clients_ok_insert; rewrite ?constsE //.
    by iApply clients_ok_empty.
  - by iApply users_ok_empty.
  - by iApply op_sessions_ok_empty.
  - by iApply codes_ok_empty. }
iAssert (rp_inv rp) with "[Hrp]" as "Hrp".
{ iExists _, ∅, ∅. iFrame "Hrp". do !iSplit.
  - iApply providers_ok_insert; rewrite ?constsE //.
    by iApply providers_ok_empty.
  - by iApply rp_sessions_ok_empty.
  - by iApply logins_ok_empty. }
wp_pures. wp_apply wp_send => //.
wp_pures. wp_apply (wp_op_register_user with "p_sub [] Hop") => //.
iIntros "Hop".
wp_pures. wp_apply (wp_register_attacker with "chan ctx octx [$Hop $Hrp]").
iIntros "[Hop Hrp]".
wp_pures. wp_apply wp_browser_new => //. iIntros "%b Hb".
wp_pures. wp_apply (wp_browser_register with "Hb"). iIntros "Hb".
wp_pures. wp_apply (wp_browser_register with "Hb"). iIntros "Hb".
wp_pures. wp_apply (wp_fork with "[Hop]").
{ iModIntro. by iApply (wp_op_serve with "chan ctx octx Hop"). }
wp_pures. wp_apply (wp_fork with "[Hrp]").
{ iModIntro. wp_list. wp_tol.
  by iApply (wp_rp_loop with "chan ctx octx Hrp"). }
wp_pures. wp_apply (wp_fork with "[Hb]") => //.
iModIntro. by iApply (wp_user with "chan ctx octx Hb").
Qed.

End Main.

Definition oidcΣ : gFunctors := #[heapΣ; cryptisΣ].

Theorem oidc_is_secure : oidc_secure.
Proof.
move=> σ₁ σ₂ t₂ e₂.
have ? : heapGpreS oidcΣ by apply _.
apply (adequate_not_stuck NotStuck _ _ (λ v _, True)) => //.
apply: cryptis_adequacy.
iIntros (? ? c) "#ctx #chan (aenc & sign & senc & _)".
by iApply (wp_game with "ctx chan aenc sign senc").
Qed.

Print Assumptions oidc_is_secure.
