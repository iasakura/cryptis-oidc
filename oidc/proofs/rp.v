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

The relying party.  Its tables are owned by the thread that runs it; the
invariant on [logins] is the first winning condition of the game.

*)

Section RP.

Context `{!heapGS Σ, !cryptisGS Σ, !oidcParams}.
Notation iProp := (iProp Σ).

Implicit Types (P S L : gmap term term).
Implicit Types (Ψ : val → iProp).

(* Trusted providers.  The entry of the honest issuer points at the honest
   provider; every other entry belongs to the attacker and is public. *)
Definition providers_ok P : iProp :=
  ∀ i e, ⌜P !! i = Some e⌝ →
    public i ∗ public e ∗
    ⌜∃ skV : sign_key, i = Spec.pkey skV⌝ ∗
    ⌜∃ ophost (skT : aenc_key) sec,
        e = Spec.of_list [ophost; Spec.pkey skT; sec]⌝ ∗
    ⌜i = hiss → ∃ sec, e = Spec.of_list [op_host; op_pk; sec]⌝.

(* Logins in flight.  Nothing in a session is secret. *)
Definition rp_sessions_ok S : iProp :=
  ∀ c e, ⌜S !! c = Some e⌝ → ⌜c ≠ TInt 0⌝ ∗ public e.

(* W1: a cookie that is logged in as the honest user is hidden. *)
Definition logins_ok L : iProp :=
  ∀ c id, ⌜L !! c = Some id⌝ → ⌜id = Spec.of_list [hiss; hsub]⌝ → hidden c.

(* The relying party's state, with the contents of its tables exposed. *)
Definition rp_state (skT : aenc_key) (host : term) (rp : val) P S L : iProp :=
  ∃ vp vs vl : val,
    ⌜rp = (skT, host, vp, vs, vl)%V⌝ ∗
    tmap vp P ∗ tmap vs S ∗ tmap vl L.

Definition rp_inv (rp : val) : iProp :=
  ∃ P S L,
    rp_state skRP rp_host rp P S L ∗
    providers_ok P ∗ rp_sessions_ok S ∗ logins_ok L.

Lemma rp_inv_intro (vp vs vl : val) P S L :
  tmap vp P -∗ tmap vs S -∗ tmap vl L -∗
  providers_ok P -∗ rp_sessions_ok S -∗ logins_ok L -∗
  rp_inv (skRP, rp_host, vp, vs, vl)%V.
Proof.
iIntros "? ? ? ? ? ?". iExists P, S, L. by iFrame.
Qed.

Lemma providers_ok_empty : ⊢ providers_ok ∅.
Proof. iIntros "%x %y %lk". by rewrite lookup_empty in lk. Qed.

Lemma rp_sessions_ok_empty : ⊢ rp_sessions_ok ∅.
Proof. iIntros "%x %y %lk". by rewrite lookup_empty in lk. Qed.

Lemma logins_ok_empty : ⊢ logins_ok ∅.
Proof. iIntros "%x %y %lk". by rewrite lookup_empty in lk. Qed.

Lemma providers_ok_insert P (skV : sign_key) (ophost : term)
    (skT : aenc_key) (sec : term) :
  providers_ok P -∗
  minted skV -∗
  public ophost -∗
  minted skT -∗
  public sec -∗
  ⌜Spec.pkey skV = hiss → ophost = op_host ∧ skT = skOPt⌝ -∗
  providers_ok (<[Spec.pkey skV :=
                    Spec.of_list [ophost; Spec.pkey skT; sec]]> P).
Proof.
iIntros "#P_ok #m_skV #p_ophost #m_skT #p_sec %honest %i' %e' %lk".
case/lookup_insert_Some: lk => [[<- <-]|[_ lk]]; last by iApply "P_ok".
rewrite public_of_list /= public_verify_key public_aenc_key.
do !iSplit => //.
- iPureIntro. by eauto.
- iPureIntro. by eauto.
- iPureIntro => /honest [-> ->]. by eauto.
Qed.

(** ** Accessors. *)

Lemma wp_rp_host (a b c d e : val) Ψ :
  Ψ b ⊢ WP RP.host (a, b, c, d, e)%V {{ Ψ }}.
Proof. iIntros "?". rewrite /RP.host. by wp_pures. Qed.

Lemma wp_rp_providers (a b c d e : val) Ψ :
  Ψ c ⊢ WP RP.providers (a, b, c, d, e)%V {{ Ψ }}.
Proof. iIntros "?". rewrite /RP.providers. by wp_pures. Qed.

Lemma wp_rp_sessions (a b c d e : val) Ψ :
  Ψ d ⊢ WP RP.sessions (a, b, c, d, e)%V {{ Ψ }}.
Proof. iIntros "?". rewrite /RP.sessions. by wp_pures. Qed.

Lemma wp_rp_logins (a b c d e : val) Ψ :
  Ψ e ⊢ WP RP.logins (a, b, c, d, e)%V {{ Ψ }}.
Proof. iIntros "?". rewrite /RP.logins. by wp_pures. Qed.

Lemma wp_rp_client_id (b c d e : val) Ψ :
  Ψ hcid ⊢ WP RP.client_id (skRP, b, c, d, e)%V {{ Ψ }}.
Proof.
iIntros "?". rewrite /RP.client_id /RP.tls_sk. wp_pures.
by wp_apply wp_pkey.
Qed.

Lemma wp_rp_redirect_uri (a c d e : val) Ψ :
  Ψ (Spec.of_list [rp_host; rp_cb]) ⊢
  WP RP.redirect_uri (a, rp_host, c, d, e)%V {{ Ψ }}.
Proof.
iIntros "?". rewrite /RP.redirect_uri. wp_pures. wp_list.
wp_apply wp_rp_host. wp_list. by wp_tol.
Qed.

Lemma wp_rp_tls_sk rp Ψ :
  rp_inv rp -∗ (rp_inv rp -∗ Ψ skRP) -∗ WP RP.tls_sk rp {{ Ψ }}.
Proof.
iIntros "inv post".
iDestruct "inv" as "(%P & %S & %L & (%vp & %vs & %vl & -> & HP & HS & HL) & ok)".
rewrite /RP.tls_sk. wp_pures. iApply "post".
iExists P, S, L. by iFrame.
Qed.

(* Looking a cookie up in [logins]: the W1 invariant comes with the answer. *)
Lemma wp_rp_find_login rp (c : term) Ψ :
  rp_inv rp -∗
  (∀ r : option term,
     rp_inv rp -∗
     match r with
     | Some id => ⌜id = Spec.of_list [hiss; hsub]⌝ → hidden c
     | None => True
     end -∗
     Ψ (repr r)) -∗
  WP AList.find (RP.logins rp) c {{ Ψ }}.
Proof.
iIntros "inv post".
iDestruct "inv" as "(%P & %S & %L & (%vp & %vs & %vl & -> & HP & HS & HL) &
                     #P_ok & #S_ok & #L_ok)".
wp_apply wp_rp_logins. wp_apply (wp_tmap_find with "HL"). iIntros "HL".
iApply ("post" with "[HP HS HL]").
{ by iApply (rp_inv_intro with "HP HS HL"). }
case L_c: (L !! c) => [id|] //. by iApply "L_ok".
Qed.

(** ** Setting up. *)

Lemma wp_rp_new (skT : aenc_key) (host : term) :
  {{{ True }}} RP.new skT host {{{ rp, RET rp; rp_state skT host rp ∅ ∅ ∅ }}}.
Proof.
iIntros "%Φ _ post". wp_lam. wp_pures.
wp_apply wp_tmap_new => //. iIntros "%vl Hl".
wp_apply wp_tmap_new => //. iIntros "%vs Hs".
wp_apply wp_tmap_new => //. iIntros "%vp Hp".
wp_pures. iApply "post". iModIntro. iExists vp, vs, vl. by iFrame.
Qed.

Lemma wp_rp_register_provider_raw (skT : aenc_key) (host : term) rp P S L
    (i ophost optls sec : term) :
  {{{ rp_state skT host rp P S L }}}
    RP.register_provider rp i ophost optls sec
  {{{ RET #();
      rp_state skT host rp (<[i := Spec.of_list [ophost; optls; sec]]> P)
        S L }}}.
Proof.
iIntros "%Φ (%vp & %vs & %vl & -> & HP & HS & HL) post".
wp_lam. wp_pures. wp_list. wp_tol.
wp_apply wp_rp_providers. wp_apply (wp_tmap_insert with "HP"). iIntros "HP".
iApply "post". iExists vp, vs, vl. by iFrame.
Qed.

Lemma wp_rp_register_provider rp (skV : sign_key) (ophost : term)
    (skT : aenc_key) (sec : term) :
  minted skV -∗
  public ophost -∗
  minted skT -∗
  public sec -∗
  ⌜Spec.pkey skV = hiss → ophost = op_host ∧ skT = skOPt⌝ -∗
  {{{ rp_inv rp }}}
    RP.register_provider rp (Spec.pkey skV) ophost (Spec.pkey skT) sec
  {{{ RET #(); rp_inv rp }}}.
Proof.
iIntros "#m_skV #p_ophost #m_skT #p_sec %honest !> %Φ inv post".
iDestruct "inv" as "(%P & %S & %L & st & #P_ok & #S_ok & #L_ok)".
wp_apply (wp_rp_register_provider_raw with "st"). iIntros "st".
iApply "post". iExists _, S, L. iFrame "∗ #".
by iApply providers_ok_insert.
Qed.

(** ** The endpoints. *)

Ltac rp_fail :=
  by intros; wp_pures; iApply ("post" $! None); iModIntro; iSplit => //;
     iApply (rp_inv_intro with "HP HS HL").

Lemma wp_rp_handle_login rp (pub : bool) params :
  cryptis_ctx -∗
  oidc_ctx -∗
  {{{ rp_inv rp }}}
    RP.handle_login rp params
  {{{ (r : option term), RET (repr r);
      rp_inv rp ∗
      match r with
      | Some resp =>
          minted resp ∗
          if pub then public resp else rp_login_resp params resp
      | None => True
      end }}}.
Proof.
iIntros "#ctx #octx !> %Φ inv post". octx_destruct.
iDestruct "inv" as "(%P & %S & %L & (%vp & %vs & %vl & -> & HP & HS & HL) &
                     #P_ok & #S_ok & #L_ok)".
wp_lam. wp_pures.
wp_list_of_term params; last rp_fail.
wp_list_match => [i ->|_]; last rp_fail.
wp_apply wp_rp_providers. wp_apply (wp_tmap_find with "HP"). iIntros "HP".
case P_i: (P !! i) => [e|]; last rp_fail.
wp_pures.
iPoseProof ("P_ok" $! i e with "[//]") as "(#p_i & #p_e & _ & _ & %i_e)".
wp_list_of_term_eq l el; last rp_fail. subst e.
wp_list_match => [ophost optls sec el|_]; last rp_fail. subst l.
rewrite !public_of_list /=.
iDestruct "p_e" as "(p_ophost & p_optls & p_sec & _)".
wp_apply (wp_mk_nonce (λ _, ⌜pub = true⌝)%I (λ _, False)%I) => //.
iIntros "%sid #m_sid #s_sid _ _ _".
wp_pures. wp_apply (wp_mk_nonce (λ _, True)%I (λ _, False)%I) => //.
iIntros "%state #m_state #s_state _ _ _".
wp_pures. wp_apply (wp_mk_nonce (λ _, True)%I (λ _, False)%I) => //.
iIntros "%nonce #m_nonce #s_nonce _ _ _".
wp_pures. wp_apply (wp_mk_nonce (λ _, True)%I (λ _, False)%I) => //.
iIntros "%verifier #m_verifier #s_verifier _ _ _".
(* [state], [nonce] and the PKCE verifier are public from the start. *)
iAssert (public state) as "#p_state". { iApply "s_state". by iIntros "!> !>". }
iAssert (public nonce) as "#p_nonce". { iApply "s_nonce". by iIntros "!> !>". }
iAssert (public verifier) as "#p_verifier".
{ iApply "s_verifier". by iIntros "!> !>". }
iAssert (public (THash verifier)) as "#p_ch".
{ rewrite public_THash. by iLeft. }
wp_pures. wp_list. wp_tol.
wp_apply wp_rp_sessions. wp_apply (wp_tmap_insert with "HS"). iIntros "HS".
wp_pures. wp_hash. wp_list. wp_apply wp_rp_redirect_uri. wp_list.
wp_apply wp_rp_client_id. wp_list. wp_tol.
wp_apply wp_http_redirect. wp_pures.
iApply ("post" $! (Some (http_redirect sid ophost op_authorize
   (Spec.of_list [hcid; Spec.of_list [rp_host; rp_cb];
                  (state : term); (nonce : term); THash verifier])))).
iModIntro. iSplitL.
{ iApply (rp_inv_intro with "HP HS HL") => //.
  iIntros "%c' %e' %lk".
  case/lookup_insert_Some: lk => [[<- <-]|[_ lk]]; last by iApply "S_ok".
  iSplit => //. term_simpl. by do !iSplit. }
iSplit.
{ term_simpl. do !iSplit => //; by iApply public_minted. }
case: pub.
- term_simpl. do !iSplit => //. by iApply nonce_pub_true.
- iExists i, sid, ophost, state, nonce, (THash verifier).
  do !iSplit => //; first by iApply nonce_pub_false.
  iPureIntro => /i_e [sec'] /Spec.of_list_inj. by case.
Qed.

(* The token request, in its two flavours: towards the honest provider it is a
   request like any other honest one, and its answer tells us what the code was
   granted for; towards a provider of the attacker everything in it is
   public. *)
Lemma wp_rp_token_request c (i : term) (skT : aenc_key)
    (sec code verifier : term) Ψ :
  channel c -∗
  cryptis_ctx -∗
  oidc_ctx -∗
  minted skT -∗
  public sec -∗
  minted code -∗
  public verifier -∗
  ⌜i = hiss → skT = skOPt⌝ -∗
  (⌜i ≠ hiss⌝ → public code) -∗
  (∀ tresp,
     public tresp -∗
     (⌜i = hiss⌝ → ∃ s nonce,
        ⌜tresp = http_page (TInt 0) (Spec.of_list [id_token s hcid nonce])⌝ ∗
        code_grant code s hcid) -∗
     Ψ tresp) -∗
  WP TLS.request c (Spec.pkey skT)
       (http_req op_token (Spec.of_list [hcid; sec; code; verifier]) (TInt 0))
    {{ Ψ }}.
Proof.
iIntros "#chan #ctx #octx #m_skT #p_sec #m_code #p_verifier %i_skT #p_code".
iIntros "post". octx_destruct.
case: (decide (i = hiss)) => [e|ne].
- rewrite (i_skT e).
  wp_apply (wp_tls_request_honest with "chan ctx octx m_skOPt h_skOPt").
  + by term_simpl.
  + term_simpl. do !iSplit => //; by iApply public_minted.
  + by term_simpl.
  + iSplit; first by iLeft. iSplit; iIntros "%"; tag_discr.
  iIntros "%tresp #m_tresp #resp".
  iPoseProof (resp_ok_op_token with "resp")
    as "(%cl & %sec' & %code' & %verifier' & %s & %nonce &
         %e_params & -> & #p_tresp & #grant)".
  case/Spec.of_list_inj: e_params => <- _ <- _.
  iApply "post" => //. iIntros "_". iExists s, nonce. by eauto.
- wp_apply (wp_tls_request_public with "chan ctx octx m_skT").
  + term_simpl. do !iSplit => //. by iApply "p_code".
  iIntros "%tresp #p_tresp". iApply "post" => //. by iIntros "%".
Qed.

Lemma wp_rp_handle_cb c rp (pub : bool) params cookie :
  channel c -∗
  cryptis_ctx -∗
  oidc_ctx -∗
  minted params -∗
  (⌜pub = true⌝ → public params ∗ public cookie) -∗
  (⌜pub = false⌝ →
     cookie_ok cookie ∗
     (public params ∨
      ⌜∃ code state, params = Spec.of_list [code; state; hiss]⌝)) -∗
  {{{ rp_inv rp }}}
    RP.handle_cb c rp params cookie
  {{{ (r : option term), RET (repr r);
      rp_inv rp ∗
      match r with
      | Some resp =>
          minted resp ∗
          if pub then public resp else rp_cb_resp params resp
      | None => True
      end }}}.
Proof.
iIntros "#chan #ctx #octx #m_params #req_pub #req_hon !> %Φ inv post".
octx_destruct.
iPoseProof "octx" as "(#? & _)".
iDestruct "inv" as "(%P & %S & %L & (%vp & %vs & %vl & -> & HP & HS & HL) &
                     #P_ok & #S_ok & #L_ok)".
wp_lam. wp_pures.
wp_list_of_term params; last rp_fail.
wp_list_match => [code state i ->|_]; last rp_fail.
term_simpl.
iDestruct "m_params" as "(m_code & m_state & m_i & _)".
(* Outside the honest issuer's flow, the code is public. *)
iAssert (⌜i ≠ hiss⌝ → public code)%I as "#p_code".
{ iIntros "%ne". case: pub.
  - by iDestruct ("req_pub" with "[//]") as "[(? & _) _]".
  - iDestruct ("req_hon" with "[//]") as "[_ [(? & _)|%e]]" => //.
    case: e => code' [state'] /Spec.of_list_inj [_ _ e]. by case: ne. }
wp_apply wp_rp_sessions. wp_apply (wp_tmap_find with "HS"). iIntros "HS".
case S_c: (S !! cookie) => [e|]; last rp_fail.
wp_pures.
iPoseProof ("S_ok" $! cookie e with "[//]") as "(%c_ne & #p_e)".
wp_list_of_term_eq l el; last rp_fail. subst e.
wp_list_match => [iss0 state0 nonce0 verifier el|_]; last rp_fail. subst l.
rewrite !public_of_list /=.
iDestruct "p_e" as "(p_iss0 & p_state0 & p_nonce0 & p_verifier & _)".
wp_eq_term e; last rp_fail. subst state0.
wp_eq_term e; last rp_fail. subst iss0.
wp_pures. wp_apply wp_rp_sessions.
wp_apply (wp_tmap_delete with "HS"). iIntros "HS".
iAssert (rp_sessions_ok (delete cookie S)) as "#S_ok'".
{ iIntros "%c' %e' %lk".
  case/lookup_delete_Some: lk => [_ lk]. by iApply "S_ok". }
wp_pures. wp_apply wp_rp_providers.
wp_apply (wp_tmap_find with "HP"). iIntros "HP".
case P_i: (P !! i) => [e|]; last rp_fail.
wp_pures.
iPoseProof ("P_ok" $! i e with "[//]")
  as "(_ & #p_e & %i_key & %e_shape & %i_e)".
case: e_shape => ophost [skT] [sec] e_e. subst e.
case: i_key => skV e_i. subst i.
wp_list_of_term_eq l el; last rp_fail.
move/Spec.of_list_inj: el => el. subst l.
wp_list_match => [ophost' optls' sec' [<- <- <-]|ne]; last by case: ne.
rewrite !public_of_list /=.
iDestruct "p_e" as "(p_ophost & p_optls & p_sec & _)".
iAssert (minted skT) as "#m_skT". { by rewrite public_aenc_key. }
wp_pures. wp_list. wp_apply wp_rp_client_id. wp_list. wp_tol.
wp_apply wp_http_req. wp_pures.
wp_apply (wp_rp_token_request _ (Spec.pkey skV)
            with "chan ctx octx m_skT p_sec m_code p_verifier [] p_code").
{ iPureIntro => /i_e [sec''] /Spec.of_list_inj [_ /Spec.aenc_pkey_inj -> _].
  done. }
iIntros "%tresp #p_tresp #honest".
wp_list_of_term_eq l el; last rp_fail. subst tresp.
wp_list_match => [sc payload el|_]; last rp_fail. subst l.
wp_untag_eq body e_payload; last rp_fail. subst payload.
wp_list_of_term_eq l el; last rp_fail. subst body.
wp_list_match => [tok el|_]; last rp_fail. subst l.
wp_verify_eq claims e_tok; last rp_fail. subst tok.
wp_list_of_term_eq l el; last rp_fail. subst claims.
wp_list_match => [iss2 s aud nonce2 el|_]; last rp_fail. subst l.
wp_eq_term e; last rp_fail. subst iss2.
wp_pures. wp_apply wp_rp_client_id.
wp_eq_term e; last rp_fail. subst aud.
wp_eq_term e; last rp_fail. subst nonce2.
(* Everything in the id_token is public. *)
iAssert (public s) as "#p_s".
{ term_simpl. iDestruct "p_tresp" as "(_ & (p_tok & _) & _)".
  iPoseProof (public_signE with "p_tok [//]") as "[p_claims _]".
  term_simpl. by iDestruct "p_claims" as "(_ & ? & _)". }
(* From the honest provider, the token response is about our code. *)
iAssert (⌜Spec.pkey skV = hiss⌝ → code_grant code s hcid)%I as "#grant".
{ iIntros "%e".
  iDestruct ("honest" with "[//]") as "(%s' & %nonce' & %e_resp & #grant)".
  move: e_resp; rewrite /http_page /id_token.
  case/Spec.of_list_inj => _ /Spec.tag_inj [_] /Spec.of_list_inj [].
  move=> _ /Spec.tag_inj [_] /Spec.of_list_inj [_ <- _].
  done. }
(* W1. *)
iAssert (logins_ok (<[cookie := Spec.of_list [Spec.pkey skV; s]]> L))
  as "#L_ok'".
{ iIntros "%c' %id' %lk %e_id".
  case/lookup_insert_Some: lk => [[<- e_id']|[_ lk]]; last by iApply "L_ok".
  subst id'. case/Spec.of_list_inj: e_id' => e_i e_s.
  iPoseProof ("grant" with "[//]") as "(_ & _ & _ & #h_code)".
  iPoseProof ("h_code" with "[//]") as "{h_code} h_code".
  case: pub.
  - iDestruct ("req_pub" with "[//]") as "[(p_code' & _) _]".
    iApply hidden_false. by iApply "h_code".
  - by iDestruct ("req_hon" with "[//]") as "[[%e0|h] _]". }
wp_pures. wp_list. wp_tol. wp_pures.
wp_apply wp_rp_logins. wp_apply (wp_tmap_insert with "HL"). iIntros "HL".
wp_pures. wp_apply wp_http_page. wp_pures.
iApply ("post" $! (Some (http_page (TInt 0)
                           (Spec.of_list [Spec.pkey skV; s])))).
iModIntro. iSplitL.
{ by iApply (rp_inv_intro with "HP HS HL"). }
iSplit.
{ term_simpl. do !iSplit => //. by iApply public_minted. }
case: pub.
- term_simpl. iDestruct ("req_pub" with "[//]") as "[(_ & _ & ? & _) _]".
  by do !iSplit.
- iExists code, state, (Spec.pkey skV), s. by do !iSplit.
Qed.

Lemma wp_rp_handler c rp kResp req :
  channel c -∗
  cryptis_ctx -∗
  oidc_ctx -∗
  minted req -∗
  req_from kResp req -∗
  {{{ rp_inv rp }}}
    RP.handler c rp req
  {{{ (r : option term), RET (repr r);
      rp_inv rp ∗
      match r with
      | Some resp => resp_for kResp resp
      | None => True
      end }}}.
Proof.
iIntros "#chan #ctx #octx #m_req #req !> %Φ inv post".
wp_lam. wp_pures.
wp_list_of_term req; last by wp_pures; iApply ("post" $! None); iFrame.
wp_list_match => [path params cookie ->|_];
  last by wp_pures; iApply ("post" $! None); iFrame.
iPoseProof (req_from_view with "req") as "(%pub & #view)".
rewrite minted_of_list /=.
iDestruct "m_req" as "(m_path & m_params & m_cookie & _)".
wp_eq_term e.
{ subst path. wp_pures.
  wp_apply (wp_rp_handle_login _ pub with "ctx octx inv").
  iIntros "%r [inv Hr]". case: r => [resp|]; last first.
  { iApply ("post" $! None). by iFrame. }
  iDestruct "Hr" as "[#m_resp #Hr]".
  iApply ("post" $! (Some resp)). iFrame.
  iApply (resp_for_intro with "view m_resp").
  case: pub => //. do 3!iRight. iLeft. by eauto. }
wp_eq_term e'.
{ subst path. wp_pures.
  wp_apply (wp_rp_handle_cb _ _ pub
              with "chan ctx octx m_params [] [] inv").
  { iIntros "->". iDestruct "view" as "(_ & _ & ? & ?)". by iSplit. }
  { iIntros "->". iDestruct "view" as "(%k & _ & _ & _ & ? & _ & p)".
    iSplit => //. by iApply "p". }
  iIntros "%r [inv Hr]". case: r => [resp|]; last first.
  { iApply ("post" $! None). by iFrame. }
  iDestruct "Hr" as "[#m_resp #Hr]".
  iApply ("post" $! (Some resp)). iFrame.
  iApply (resp_for_intro with "view m_resp").
  case: pub => //. do 4!iRight. by eauto. }
wp_pures. iApply ("post" $! None). by iFrame.
Qed.

Lemma wp_rp_listen c rp :
  channel c -∗
  cryptis_ctx -∗
  oidc_ctx -∗
  {{{ rp_inv rp }}} RP.listen c rp {{{ RET #(); rp_inv rp }}}.
Proof.
iIntros "#chan #ctx #octx !> %Φ inv post".
wp_lam. wp_pures.
wp_apply (wp_rp_tls_sk with "inv"). iIntros "inv".
wp_apply (wp_tls_listen with "chan octx").
iIntros "%kResp %req #m_k #m_req #req".
wp_pures.
wp_apply (wp_rp_handler with "chan ctx octx m_req req inv").
iIntros "%r [inv Hr]". case: r => [resp|]; wp_pures; last by iApply "post".
wp_apply (wp_tls_respond with "chan octx Hr"). by iApply "post".
Qed.

End RP.
