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

The honest browser.

The browser goes wherever it is told, so what it guarantees is stated about
*where a request goes* rather than about what it is for:

  - [nav_ok]: parameters are public, except for the two navigations that carry
    a secret, and those only ever go to the host the secret belongs to;
  - [jar_ok]: a cookie set by an honest host is hidden and only goes back to
    that host; a cookie set by anybody else is public.

[Browser.navigate] is a loop over redirects.  Rather than one specification for
the whole loop, [nav_step] describes a single iteration and leaves the next one
to the caller.  The generic consequence ([wp_nav_generic], by Löb induction) is
what the attacker-driven navigations use; the user's own login in [security.v]
steps through its three requests one at a time, which is how W2 is proved.

*)

Section Browser.

Context `{!heapGS Σ, !cryptisGS Σ, !oidcParams}.
Notation iProp := (iProp Σ).

Implicit Types (J : gmap term term).
Implicit Types (host path params cookie resp sc payload : term).
Implicit Types (Ψ : val → iProp).

(* The hosts the browser has a TLS key for.  Everything else is the
   attacker's. *)
Definition honest_host host : Prop := host = op_host ∨ host = rp_host.

Definition hosts_map : gmap term term :=
  <[rp_host := hcid]> (<[op_host := op_pk]> ∅).

Lemma hosts_map_lookup host :
  hosts_map !! host =
  if decide (host = rp_host) then Some hcid
  else if decide (host = op_host) then Some op_pk
  else None.
Proof.
rewrite /hosts_map. case: decide => [->|ne]; first by rewrite lookup_insert_eq.
rewrite lookup_insert_ne; last by auto.
case: decide => [->|ne']; first by rewrite lookup_insert_eq.
by rewrite lookup_insert_ne; last by auto.
Qed.

Definition cookie_of J host : term := default (TInt 0) (J !! host).

Definition jar_store J host sc : gmap term term :=
  if decide (sc = TInt 0) then J else <[host := sc]> J.

Definition jar_ok J : iProp :=
  ∀ host c, ⌜J !! host = Some c⌝ →
    minted c ∗
    (⌜honest_host host⌝ → hidden c) ∗
    (⌜¬ honest_host host⌝ → public c).

Definition browser_gen (b : val) J (HM : gmap term term) : iProp :=
  ∃ vj vh : val, ⌜b = (vj, vh)%V⌝ ∗ tmap vj J ∗ tmap vh HM.

Definition browser b J : iProp := browser_gen b J hosts_map.

Lemma jar_ok_empty : ⊢ jar_ok ∅.
Proof. iIntros "%host %c %lk". by rewrite lookup_empty in lk. Qed.

(* Where the browser may go, and with what. *)
Definition nav_ok host path params : iProp :=
  public host ∗ public path ∗ minted params ∗
  (public params ∨
   ⌜host = op_host ∧ path = op_login ∧ params = Spec.of_list [hsub; hpw]⌝ ∨
   ⌜host = rp_host ∧ path = rp_cb ∧
    ∃ code state, params = Spec.of_list [code; state; hiss]⌝).

Lemma nav_ok_public host path params :
  public host -∗ public path -∗ public params -∗ nav_ok host path params.
Proof.
iIntros "#? #? #?". do !iSplit => //; first by iApply public_minted.
by iLeft.
Qed.

(* What the browser learns from a response. *)
Definition fetch_post J host path params resp : iProp :=
  minted resp ∗
  (⌜honest_host host⌝ ∗ resp_ok path params (cookie_of J host) resp ∨
   ⌜¬ honest_host host⌝ ∗ public resp).

Lemma cookie_of_minted J host : jar_ok J -∗ minted (cookie_of J host).
Proof.
iIntros "#jar". rewrite /cookie_of.
case J_h: (J !! host) => [c|] /=; last by rewrite minted_TInt.
by iDestruct ("jar" $! host c with "[//]") as "(? & _)".
Qed.

Lemma nav_ok_req_ok J host path params :
  honest_host host →
  jar_ok J -∗
  nav_ok host path params -∗
  req_ok path params (cookie_of J host).
Proof.
move=> hon. iIntros "#jar (#p_host & #p_path & #m_params & #nav)".
iSplit; last iSplit.
- rewrite /cookie_of. case J_h: (J !! host) => [c|] /=; last by iLeft.
  iRight. iDestruct ("jar" $! host c with "[//]") as "(_ & h & _)".
  by iApply "h".
- iIntros "%e". subst path. iDestruct "nav" as "[?|[%e|%e]]" => //.
  + case: e => _ [e _]. tag_discr.
  + case: e => _ [e _]. tag_discr.
- iIntros "%e". subst path. iDestruct "nav" as "[?|[%e|%e]]"; first by eauto.
  + case: e => _ [e _]. tag_discr.
  + case: e => _ [_ e]. by iRight.
Qed.

(** ** What an honest response means for the browser, whatever the request. *)

Definition resp_gen resp : iProp :=
  ∀ sc payload, ⌜resp = Spec.of_list [sc; payload]⌝ →
    cookie_ok sc ∗
    ∀ h p q,
      ⌜payload = Spec.tag (Tag redirectN) (Spec.of_list [h; p; q])⌝ →
      nav_ok h p q.

Lemma resp_ok_gen path params cookie resp :
  oidc_ctx -∗
  resp_ok path params cookie resp -∗
  resp_gen resp.
Proof.
iIntros "#octx #resp %sc %payload %e_resp". octx_destruct.
iDestruct "resp" as "[[_ resp]|[[_ resp]|[[_ resp]|[[_ resp]|[_ resp]]]]]".
- iDestruct "resp" as "(%s & %p & %sid & _ & %e & #h_sid & _)".
  rewrite e in e_resp. case/Spec.of_list_inj: e_resp => ? ?. subst sc payload.
  iSplit; first by iRight.
  iIntros "%h %p' %q %e'". by case: (redirect_page_ne (eq_sym e')).
- iDestruct "resp"
    as "(%cl & %redir & %state & %nonce & %ch & %s & %rhost & %rpath & %code &
         _ & %e & _ & #grant & #p_rhost & #p_rpath & #p_state & %cl_e &
         #p_code)".
  rewrite e in e_resp. case/Spec.of_list_inj: e_resp => ? ?. subst sc payload.
  iSplit; first by iLeft.
  iIntros "%h %p' %q %e'".
  case/Spec.tag_inj: e' => _ /Spec.of_list_inj [<- <- <-].
  iPoseProof (code_grant_minted with "grant") as "m_code".
  do !iSplit => //.
  { term_simpl. do !iSplit => //; by iApply public_minted. }
  case: (decide (cl = hcid)) => [/cl_e [-> ->]|ne].
  + iRight. iRight. iPureIntro. by eauto.
  + iLeft. term_simpl. do !iSplit => //. by iApply "p_code".
- iDestruct "resp"
    as "(%cl & %sec & %code & %verifier & %s & %nonce & _ & %e & _)".
  rewrite e in e_resp. case/Spec.of_list_inj: e_resp => ? ?. subst sc payload.
  iSplit; first by iLeft.
  iIntros "%h %p' %q %e'". by case: (redirect_page_ne (eq_sym e')).
- iDestruct "resp"
    as "(%i & %sid & %ophost & %state & %nonce & %ch & _ & %e & #h_sid &
         #p_ophost & #p_state & #p_nonce & #p_ch & _)".
  rewrite e in e_resp. case/Spec.of_list_inj: e_resp => ? ?. subst sc payload.
  iSplit; first by iRight.
  iIntros "%h %p' %q %e'".
  case/Spec.tag_inj: e' => _ /Spec.of_list_inj [<- <- <-].
  iApply nav_ok_public => //; first by rewrite constsE.
  term_simpl. by do !iSplit.
- iDestruct "resp" as "(%code & %state & %i & %s & _ & %e & _)".
  rewrite e in e_resp. case/Spec.of_list_inj: e_resp => ? ?. subst sc payload.
  iSplit; first by iLeft.
  iIntros "%h %p' %q %e'". by case: (redirect_page_ne (eq_sym e')).
Qed.

(* After any response: the jar is still fine, and so is following a
   redirect. *)
Lemma fetch_post_gen J host path params sc payload :
  oidc_ctx -∗
  jar_ok J -∗
  fetch_post J host path params (Spec.of_list [sc; payload]) -∗
  jar_ok (jar_store J host sc) ∗
  ∀ h p q,
    ⌜payload = Spec.tag (Tag redirectN) (Spec.of_list [h; p; q])⌝ →
    nav_ok h p q.
Proof.
iIntros "#octx #jar [#m_resp #fp]".
rewrite minted_of_list /=. iDestruct "m_resp" as "(m_sc & m_payload & _)".
iAssert (⌜sc ≠ TInt 0⌝ → ⌜honest_host host⌝ → hidden sc)%I as "#h_sc".
{ iIntros "%ne %hon". iDestruct "fp" as "[[_ resp]|[%nhon _]]" => //.
  iPoseProof (resp_ok_gen with "octx resp") as "gen".
  by iDestruct ("gen" $! sc payload with "[//]") as "[[%|?] _]". }
iAssert (⌜¬ honest_host host⌝ → public sc)%I as "#p_sc".
{ iIntros "%nhon". iDestruct "fp" as "[[%hon _]|[_ p_resp]]" => //.
  rewrite public_of_list /=. by iDestruct "p_resp" as "(? & _)". }
iSplit.
- rewrite /jar_store. case: decide => [_|ne] //.
  iIntros "%host' %c' %lk".
  case/lookup_insert_Some: lk => [[<- <-]|[_ lk]]; last by iApply "jar".
  do !iSplit => //. by iApply "h_sc".
- iIntros "%h %p %q %e". subst payload.
  iDestruct "fp" as "[[_ resp]|[_ p_resp]]".
  + iPoseProof (resp_ok_gen with "octx resp") as "gen".
    iDestruct ("gen" $! sc _ with "[//]") as "[_ nav]". by iApply "nav".
  + term_simpl. iDestruct "p_resp" as "(_ & (? & ? & ? & _) & _)".
    by iApply nav_ok_public.
Qed.

(** ** The code. *)

Lemma wp_browser_jar (vj vh : val) Ψ :
  Ψ vj ⊢ WP Browser.jar (vj, vh)%V {{ Ψ }}.
Proof. iIntros "?". rewrite /Browser.jar. by wp_pures. Qed.

Lemma wp_browser_hosts (vj vh : val) Ψ :
  Ψ vh ⊢ WP Browser.hosts (vj, vh)%V {{ Ψ }}.
Proof. iIntros "?". rewrite /Browser.hosts. by wp_pures. Qed.

Lemma wp_browser_new :
  {{{ True }}} Browser.new #() {{{ b, RET b; browser_gen b ∅ ∅ }}}.
Proof.
iIntros "%Φ _ post". wp_lam. wp_pures.
wp_apply wp_tmap_new => //. iIntros "%vh Hh".
wp_apply wp_tmap_new => //. iIntros "%vj Hj".
wp_pures. iApply "post". iExists vj, vh. by iFrame.
Qed.

Lemma wp_browser_register b J HM (host pk : term) :
  {{{ browser_gen b J HM }}}
    Browser.register b host pk
  {{{ RET #(); browser_gen b J (<[host := pk]> HM) }}}.
Proof.
iIntros "%Φ (%vj & %vh & -> & Hj & Hh) post". wp_lam. wp_pures.
wp_apply wp_browser_hosts. wp_apply (wp_tmap_insert with "Hh"). iIntros "Hh".
iApply "post". iExists vj, vh. by iFrame.
Qed.

Lemma wp_browser_cookie_for b J HM host Ψ :
  browser_gen b J HM -∗
  (browser_gen b J HM -∗ Ψ (cookie_of J host)) -∗
  WP Browser.cookie_for b host {{ Ψ }}.
Proof.
iIntros "(%vj & %vh & -> & Hj & Hh) post". wp_lam. wp_pures.
wp_apply wp_browser_jar. wp_apply (wp_tmap_find with "Hj"). iIntros "Hj".
rewrite /cookie_of.
case J_h: (J !! host) => [c|] /=; wp_pures; iApply "post";
iExists vj, vh; by iFrame.
Qed.

Lemma wp_browser_store_cookie b J HM host sc Ψ :
  browser_gen b J HM -∗
  (browser_gen b (jar_store J host sc) HM -∗ Ψ #()) -∗
  WP Browser.store_cookie b host sc {{ Ψ }}.
Proof.
iIntros "(%vj & %vh & -> & Hj & Hh) post". wp_lam. wp_pures.
rewrite /jar_store. wp_eq_term e.
- wp_pures. iApply "post". rewrite decide_True //. iExists vj, vh. by iFrame.
- wp_pures. wp_apply wp_browser_jar.
  wp_apply (wp_tmap_insert with "Hj"). iIntros "Hj".
  iApply "post". rewrite decide_False //. iExists vj, vh. by iFrame.
Qed.

Lemma wp_browser_fetch c b J host path params Ψ :
  channel c -∗
  cryptis_ctx -∗
  oidc_ctx -∗
  jar_ok J -∗
  nav_ok host path params -∗
  browser b J -∗
  (∀ resp, browser b J -∗ fetch_post J host path params resp -∗
           Ψ (SOMEV resp)) -∗
  WP Browser.fetch c b host path params {{ Ψ }}.
Proof.
iIntros "#chan #ctx #octx #jar #nav Hb post". octx_destruct.
iPoseProof "nav" as "(#p_host & #p_path & #m_params & #nav')".
iPoseProof (cookie_of_minted J host with "jar") as "#m_cookie".
wp_lam. wp_pures.
wp_apply (wp_browser_cookie_for with "Hb"). iIntros "Hb".
wp_apply wp_http_req. wp_pures.
iDestruct "Hb" as "(%vj & %vh & -> & Hj & Hh)".
wp_apply wp_browser_hosts. wp_apply (wp_tmap_find with "Hh"). iIntros "Hh".
iAssert (browser (vj, vh)%V J) with "[Hj Hh]" as "Hb".
{ iExists vj, vh. by iFrame. }
rewrite hosts_map_lookup.
case: decide => [e_rp|ne_rp]; last case: decide => [e_op|ne_op].
- have hon : honest_host host by right.
  wp_pures.
  wp_apply (wp_tls_request_honest with "chan ctx octx m_skRP h_skRP")
    => //; first by iApply public_minted.
  { by iApply nav_ok_req_ok. }
  iIntros "%resp #m_resp #resp". wp_pures.
  iApply ("post" with "Hb"). iModIntro. iSplit => //. iLeft. by iSplit.
- have hon : honest_host host by left.
  wp_pures.
  wp_apply (wp_tls_request_honest with "chan ctx octx m_skOPt h_skOPt")
    => //; first by iApply public_minted.
  { by iApply nav_ok_req_ok. }
  iIntros "%resp #m_resp #resp". wp_pures.
  iApply ("post" with "Hb"). iModIntro. iSplit => //. iLeft. by iSplit.
- have nhon : ¬ honest_host host by case.
  wp_pures. wp_list. wp_tol. wp_apply wp_send => //.
  { term_simpl. do !iSplit => //.
    - iDestruct "nav'" as "[?|[%e|%e]]" => //.
      + case: e => e _. by case: nhon; left.
      + case: e => e _. by case: nhon; right.
    - rewrite /cookie_of.
      case J_h: (J !! host) => [ck|] /=; last by rewrite public_TInt.
      iDestruct ("jar" $! host ck with "[//]") as "(_ & _ & p)".
      by iApply "p". }
  wp_pures. wp_apply wp_recv => //. iIntros "%resp #p_resp". wp_pures.
  iApply ("post" with "Hb"). iModIntro.
  iSplit; first by iApply public_minted.
  iRight. by iSplit.
Qed.

(** ** One iteration of [Browser.navigate]. *)

(* What is left to do once the response [resp] is in.  The loop parses it and
   then fails, or follows a redirect by calling itself ([f]) again, or ends with
   a page.  Which of the three happens is determined by [resp], so a caller
   that knows the response only has to deal with the case at hand. *)
Definition nav_cont (f b : val) J host resp Ψ : iProp :=
  match Spec.to_list resp with
  | Some [sc; payload] =>
      browser b (jar_store J host sc) -∗
      match Spec.untag (Tag redirectN) payload with
      | Some r =>
          match Spec.to_list r with
          | Some [h2; p2; q2] => WP f h2 p2 q2 {{ Ψ }}
          | _ => Ψ NONEV
          end
      | None => Ψ (repr (Spec.untag (Tag pageN) payload))
      end
  | _ => browser b J -∗ Ψ NONEV
  end.

Definition nav_step (b f : val) : iProp :=
  □ ∀ J host path params Ψ,
      jar_ok J -∗
      nav_ok host path params -∗
      browser b J -∗
      ▷ (∀ resp, fetch_post J host path params resp -∗
                 nav_cont f b J host resp Ψ) -∗
      WP f host path params {{ Ψ }}.

Lemma wp_browser_navigate c b Ψ :
  channel c -∗
  cryptis_ctx -∗
  oidc_ctx -∗
  (∀ f, nav_step b f -∗ Ψ f) -∗
  WP Browser.navigate c b {{ Ψ }}.
Proof.
iIntros "#chan #ctx #octx post". wp_lam. wp_pures. iApply "post".
iIntros "!> !> %J %host %path %params %Ψ' #jar #nav Hb cont".
wp_pures.
wp_apply (wp_browser_fetch with "chan ctx octx jar nav Hb").
iIntros "%resp Hb #fp". iSpecialize ("cont" with "fp"). wp_pures.
rewrite /nav_cont.
wp_list_of_term_eq l el; last first.
{ rewrite el. wp_pures. by iApply "cont". }
subst resp. rewrite Spec.of_listK.
wp_list_match => [sc payload el|ne]; last first.
{ case: l ne => [|x1 [|x2 [|x3 l]]] //= _; wp_pures; by iApply "cont". }
subst l.
wp_apply (wp_browser_store_cookie with "Hb"). iIntros "Hb".
iSpecialize ("cont" with "Hb").
wp_pures. wp_untag_eq r e_r; last first.
{ rewrite e_r. wp_pures. wp_apply wp_untag. by iApply "cont". }
subst payload. rewrite Spec.tagK. wp_pures.
wp_list_of_term_eq l el; last first.
{ rewrite el. wp_pures. by iApply "cont". }
subst r. rewrite Spec.of_listK.
wp_list_match => [h2 p2 q2 el|ne]; last first.
{ case: l ne => [|x1 [|x2 [|x3 [|x4 l]]]] //= _; wp_pures;
  by iApply "cont". }
subst l. by iApply "cont".
Qed.

(** ** Any navigation at all: the browser survives it. *)

Lemma wp_nav_generic b f J host path params :
  oidc_ctx -∗
  nav_step b f -∗
  jar_ok J -∗
  nav_ok host path params -∗
  browser b J -∗
  WP f host path params {{ _, ∃ J', browser b J' ∗ jar_ok J' }}.
Proof.
iIntros "#octx #step". iLöb as "IH" forall (J host path params).
iIntros "#jar #nav Hb".
iApply ("step" with "jar nav Hb"). iIntros "!> %resp #fp".
rewrite /nav_cont.
case e_resp: (Spec.to_list resp) => [[|sc [|payload [|x l]]]|];
  try by iIntros "Hb"; iExists J; iFrame.
move/Spec.to_listK in e_resp. subst resp.
iIntros "Hb".
iPoseProof (fetch_post_gen with "octx jar fp") as "[#jar' #nav']".
case e_r: (Spec.untag (Tag redirectN) payload) => [r|]; last first.
{ iExists _. by iFrame. }
move/Spec.untagK in e_r. subst payload.
case e_r: (Spec.to_list r) => [[|h2 [|p2 [|q2 [|x l]]]]|];
  try by iExists _; iFrame.
move/Spec.to_listK in e_r. subst r.
iApply ("IH" with "jar' [] Hb"). by iApply "nav'".
Qed.

(* The cookie of another host is not touched. *)
Lemma jar_store_lookup_ne J host host' sc :
  host ≠ host' → jar_store J host sc !! host' = J !! host'.
Proof.
move=> ne. rewrite /jar_store. case: decide => // _.
by rewrite lookup_insert_ne.
Qed.

Lemma jar_store_lookup J host sc :
  sc ≠ TInt 0 → jar_store J host sc !! host = Some sc.
Proof.
move=> ne. by rewrite /jar_store decide_False // lookup_insert_eq.
Qed.

End Browser.
