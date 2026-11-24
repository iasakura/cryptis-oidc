From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis.examples Require Import alist.
From oidc Require Import impl game.
From oidc.proofs Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*

Specifications for the [HTTP] and [TLS] modules.

A TLS client has two ways of making a request.  Towards a server it knows to be
honest it keeps the response key hidden, and gets back [resp_ok] for the request
it made ([wp_tls_request_honest]).  Towards anybody else it gives the response
key away, and learns nothing beyond the response being public
([wp_tls_request_public]).

*)

Section HTTP.

Context `{!heapGS Σ}.

Implicit Types (Ψ : val → iProp Σ) (E : coPset).

Lemma wp_http_req E (path params cookie : term) Ψ :
  Ψ (http_req path params cookie) ⊢
  WP HTTP.req path params cookie @ E {{ Ψ }}.
Proof.
iIntros "post". wp_lam. wp_pures. wp_list. by wp_tol.
Qed.

Lemma wp_http_redirect E (sc host path params : term) Ψ :
  Ψ (http_redirect sc host path params) ⊢
  WP HTTP.redirect sc host path params @ E {{ Ψ }}.
Proof.
iIntros "post". wp_lam. wp_pures. wp_list. wp_tol. wp_tag.
wp_list. by wp_tol.
Qed.

Lemma wp_http_page E (sc body : term) Ψ :
  Ψ (http_page sc body) ⊢
  WP HTTP.page sc body @ E {{ Ψ }}.
Proof.
iIntros "post". wp_lam. wp_pures. wp_tag. wp_list. by wp_tol.
Qed.

End HTTP.

Section TLS.

Context `{!heapGS Σ, !cryptisGS Σ, !oidcParams}.
Notation iProp := (iProp Σ).

Implicit Types (path params cookie req resp kResp : term).
Implicit Types (skS : aenc_key) (Ψ : val → iProp).

Lemma wp_tls_request_honest_aux c skS path params cookie :
  channel c -∗
  cryptis_ctx -∗
  oidc_ctx -∗
  minted skS -∗
  hidden skS -∗
  minted path -∗
  minted params -∗
  minted cookie -∗
  req_ok path params cookie -∗
  WP TLS.request c (Spec.pkey skS) (http_req path params cookie)
    {{ v, ∃ resp, ⌜v = (resp : val)⌝ ∗ minted resp ∗
                  resp_ok path params cookie resp }}.
Proof.
iIntros "#chan #ctx (#? & #? & #? & _) #m_sk #h_sk #m_path #m_params".
iIntros "#m_cookie #req".
wp_lam. wp_pures.
wp_apply (wp_mk_senc_key with "ctx"). iIntros "%k #m_k sec tok".
iMod (freeze_secret with "sec") as "#s_k".
iMod (term_meta_set reqN (path, params, cookie) with "tok") as "#meta";
  first solve_ndisj.
iAssert (hidden k) as "#h_k". { iIntros "!> #p". by iApply "s_k". }
wp_pures. wp_list. wp_tol.
wp_apply wp_aenc => //.
- rewrite minted_of_list /= /http_req minted_of_list /=. by iFrame "#".
- iRight. iSplit.
  + iModIntro. iExists k, path, params, cookie. by iFrame "#".
  + iApply (hidden_guard with "h_sk").
    rewrite minted_of_list /= /http_req minted_of_list /=. by iFrame "#".
iIntros "%m #p_m". wp_pures. wp_apply wp_send => //.
wp_pures. wp_apply wp_do_until'. iIntros "!>".
wp_pure _ credit:"c". wp_pures.
wp_apply wp_recv => //. iIntros "%m' #p_m'".
iApply wp_fupd. wp_apply wp_sdec => //. iSplit; last by eauto.
iIntros "%resp #m_resp #inv _".
iDestruct "inv" as "[p_k|#inv]".
{ iPoseProof ("h_k" with "p_k") as "contra".
  by iMod (lc_fupd_elim_later with "c contra") as "[]". }
iDestruct "inv" as "(%path' & %params' & %cookie' & #meta' & #resp)".
iPoseProof (term_meta_agree with "meta meta'") as "%e".
case: e => <- <- <-.
iModIntro. iRight. iExists resp. iSplit => //. iExists resp. by eauto.
Qed.

Lemma wp_tls_request_public_aux c skS req :
  channel c -∗
  cryptis_ctx -∗
  oidc_ctx -∗
  minted skS -∗
  public req -∗
  WP TLS.request c (Spec.pkey skS) req
    {{ v, ∃ resp, ⌜v = (resp : val)⌝ ∗ public resp }}.
Proof.
iIntros "#chan #ctx (#? & #? & #? & _) #m_sk #p_req".
wp_lam. wp_pures.
wp_apply (wp_mk_senc_key with "ctx"). iIntros "%k #m_k sec tok".
iMod (secret_public with "sec") as "#p_k".
wp_pures. wp_list. wp_tol.
wp_apply wp_aenc => //.
- rewrite minted_of_list /=. do !iSplit => //. by iApply public_minted.
- iLeft. rewrite public_of_list /=. by eauto.
iIntros "%m #p_m". wp_pures. wp_apply wp_send => //.
wp_pures. wp_apply wp_do_until'. iIntros "!>". wp_pures.
wp_apply wp_recv => //. iIntros "%m' #p_m'".
wp_apply wp_sdec => //. iSplit; last by eauto.
iIntros "%resp #m_resp _ #p_resp".
iRight. iExists resp. iSplit => //. iExists resp. iSplit => //.
by iApply "p_resp".
Qed.

Lemma wp_tls_listen_aux c skS :
  channel c -∗
  oidc_ctx -∗
  WP TLS.listen c skS
    {{ v, ∃ kResp req, ⌜v = (kResp, req)%V⌝ ∗
                       minted kResp ∗ minted req ∗ req_from kResp req }}.
Proof.
iIntros "#chan (#? & #? & #? & _)".
wp_lam. wp_pures. wp_apply wp_do_until'. iIntros "!>". wp_pures.
wp_apply wp_recv => //. iIntros "%m #p_m".
wp_apply wp_adec => //. iSplit; last by wp_pures; eauto.
iIntros "%t #m_t #inv". wp_pures.
wp_list_of_term t; last by wp_pures; eauto.
wp_list_match => [kResp req ->|_]; last by wp_pures; eauto.
wp_pures. iModIntro. iRight. iExists (kResp, req)%V. iSplit => //.
iExists kResp, req. rewrite minted_of_list /=.
iDestruct "m_t" as "(? & ? & _)". do !iSplit => //.
iDestruct "inv" as "[p_t|[#inv _]]".
- rewrite public_of_list /=. iDestruct "p_t" as "(? & ? & _)".
  iLeft. by eauto.
- iDestruct "inv" as "(%k & %path & %params & %cookie & %e & ? & ? & ?)".
  case/Spec.of_list_inj: e => -> ->.
  iRight. iExists k, path, params, cookie. by eauto.
Qed.

Lemma wp_tls_request_honest c skS path params cookie Ψ :
  channel c -∗
  cryptis_ctx -∗
  oidc_ctx -∗
  minted skS -∗
  hidden skS -∗
  minted path -∗
  minted params -∗
  minted cookie -∗
  req_ok path params cookie -∗
  (∀ resp, minted resp -∗ resp_ok path params cookie resp -∗ Ψ resp) -∗
  WP TLS.request c (Spec.pkey skS) (http_req path params cookie) {{ Ψ }}.
Proof.
iIntros "#? #? #? #? #? #? #? #? #? post".
iApply (wp_wand with "[]"); first by iApply wp_tls_request_honest_aux.
iIntros "%v (%resp & -> & m_resp & resp)".
by iApply ("post" with "m_resp resp").
Qed.

Lemma wp_tls_request_public c skS req Ψ :
  channel c -∗
  cryptis_ctx -∗
  oidc_ctx -∗
  minted skS -∗
  public req -∗
  (∀ resp, public resp -∗ Ψ resp) -∗
  WP TLS.request c (Spec.pkey skS) req {{ Ψ }}.
Proof.
iIntros "#? #? #? #? #? post".
iApply (wp_wand with "[]"); first by iApply wp_tls_request_public_aux.
iIntros "%v (%resp & -> & ?)". by iApply "post".
Qed.

Lemma wp_tls_listen c skS Ψ :
  channel c -∗
  oidc_ctx -∗
  (∀ kResp req,
     minted kResp -∗ minted req -∗ req_from kResp req -∗
     Ψ (kResp, req)%V) -∗
  WP TLS.listen c skS {{ Ψ }}.
Proof.
iIntros "#? #? post".
iApply (wp_wand with "[]"); first by iApply wp_tls_listen_aux.
iIntros "%v (%kResp & %req & -> & m_k & m_req & req)".
by iApply ("post" with "m_k m_req req").
Qed.

Lemma wp_tls_respond c kResp resp Ψ :
  channel c -∗
  oidc_ctx -∗
  resp_for kResp resp -∗
  Ψ #() -∗
  WP TLS.respond c kResp resp {{ Ψ }}.
Proof.
iIntros "#chan (#? & #? & #? & _) [#m_resp #resp] post".
wp_lam. wp_pures.
iDestruct "resp" as "[[p_k p_resp]|resp]".
- wp_bind (senc _ _ _). iApply wp_senc'. iModIntro.
  wp_apply wp_send => //.
  iApply public_TSealIP => //. by rewrite public_tag.
- iDestruct "resp" as "(%k & %path & %params & %cookie & -> & h_k & meta & resp)".
  wp_apply wp_senc => //.
  + by iApply (term_meta_minted with "meta").
  + iRight. iModIntro. iExists path, params, cookie. by eauto.
  + by iApply hidden_guard.
  iIntros "%m #p_m". by wp_apply wp_send.
Qed.

End TLS.
