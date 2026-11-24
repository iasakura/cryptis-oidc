From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis.examples Require Import alist.
From oidc Require Import impl game.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*

Proof infrastructure for the security game in [game.v]: the invariants that the
honest parties maintain, and the predicates attached to the messages they
exchange.  The specifications of the code live in the files that follow.

** The shape of the argument

Every value in the model is either public from the start or [hidden] for good.
What is hidden:

  - the long-term keys of the provider and the relying party, and the user's
    password;
  - the response key [kResp] of every TLS request made by an honest client;
  - a cookie handed out in the response to such a request;
  - an authorization code handed out in the response to such a request, when it
    is issued to the honest client.

Everything else is public, including [state], [nonce], the PKCE verifier and
the client secret: the proof never needs them to be secret, which is the formal
content of the "not needed here" list in [game.v].

Two facts carry the proof.

  TLS binds a response to its request.  [kResp] is fresh for every request and
  records, as term metadata, the request it was created for.  Whoever decrypts a
  response under a hidden [kResp] learns [resp_ok] for *that* request.

  Codes and provider sessions are immutable.  A provider cookie records the
  subject it belongs to ([op_session]), a code records the subject and client
  it was issued for ([code_grant]).  Both are term metadata, so any two parties
  that hold the same term agree on them.

W1 then reads: the relying party logs a cookie in as ⟨iss, sub⟩ only after
redeeming a code granted to the honest client for the honest user.  Such a code
is hidden, so the callback that carried it came from the honest browser, and
the cookies the honest browser sends are hidden.

W2 reads: the page the user sees answers the callback request, which carried
the code that answered the authorization request, which carried the provider
cookie that answered the user's own login.

*)

(* ------------------------------------------------------------------ *)
(** ** The honest principals of the game. *)

Class oidcParams := OidcParams {
  skOP  : sign_key;   (* the provider's id_token signing key *)
  skOPt : aenc_key;   (* the provider's TLS key              *)
  skRP  : aenc_key;   (* the relying party's TLS key         *)
  hsub  : term;       (* the honest user's identifier ...    *)
  hpw   : term;       (* ... and password                    *)
}.

Definition hiss  `{!oidcParams} : term := Spec.pkey skOP.
Definition hcid  `{!oidcParams} : term := Spec.pkey skRP.
Definition op_pk `{!oidcParams} : term := Spec.pkey skOPt.

(* ------------------------------------------------------------------ *)
(** ** Constants: tags are pairwise distinct. *)

Lemma oidc_tag_ne (s1 s2 : string) :
  s1 ≠ s2 → Tag (oidcN.@s1) ≠ Tag (oidcN.@s2).
Proof. move=> ne /Tag_inj e. apply: ne. by case: (ndot_inj _ _ _ _ e). Qed.

(* Close a goal that has two different endpoint constants equated in the
   context. *)
Ltac tag_discr :=
  exfalso;
  match goal with
  | H : _ = _ |- _ =>
    move: H;
    rewrite /op_login /op_authorize /op_token /rp_login /rp_cb
            /op_host /rp_host;
    by apply: oidc_tag_ne
  end.

(* Evaluate the innermost [term_of_list] whose argument is already a value. *)
Ltac wp_tol :=
  wp_pures; wp_bind (term_of_list (Val _)); iApply wp_term_of_list.

Lemma op_host_rp_host : op_host ≠ rp_host.
Proof. by apply: oidc_tag_ne. Qed.

(* ------------------------------------------------------------------ *)
(** ** HTTP messages as terms. *)

Definition redirectN := oidcN.@"redirect".
Definition pageN     := oidcN.@"page".

Definition http_req (path params cookie : term) : term :=
  Spec.of_list [path; params; cookie].

Definition http_redirect (sc host path params : term) : term :=
  Spec.of_list [sc; Spec.tag (Tag redirectN) (Spec.of_list [host; path; params])].

Definition http_page (sc body : term) : term :=
  Spec.of_list [sc; Spec.tag (Tag pageN) body].

Lemma redirect_page_ne t1 t2 :
  Spec.tag (Tag redirectN) t1 ≠ Spec.tag (Tag pageN) t2.
Proof. move=> /Spec.tag_inj [] e _. by move: e; apply: oidc_tag_ne. Qed.

Lemma untag_redirect_page t :
  Spec.untag (Tag redirectN) (Spec.tag (Tag pageN) t) = None.
Proof.
apply: Spec.untag_tag_ne. by apply: oidc_tag_ne.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Association lists whose values are terms. *)

Section TMap.

Context `{!heapGS Σ, !cryptisGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (v : val) (m : gmap term term) (k t : term).

Definition tmap v m : iProp := AList.is_alist v (repr <$> m).

Lemma wp_tmap_new E :
  {{{ True }}} AList.new #() @ E {{{ v, RET v; tmap v ∅ }}}.
Proof.
iIntros "%Φ _ post". wp_apply AList.wp_empty; first done.
iIntros "%v Hv". iApply "post". by rewrite /tmap fmap_empty.
Qed.

Lemma wp_tmap_find E v m k :
  {{{ tmap v m }}} AList.find v k @ E {{{ RET (repr (m !! k)); tmap v m }}}.
Proof.
iIntros "%Φ Hv post". wp_apply (AList.wp_find with "Hv").
iIntros "Hv". rewrite lookup_fmap.
have -> : repr (repr <$> m !! k) = repr (m !! k) by case: (m !! k).
by iApply "post".
Qed.

Lemma wp_tmap_insert E v m k t :
  {{{ tmap v m }}}
    AList.insert v k t @ E
  {{{ RET #(); tmap v (<[k := t]> m) }}}.
Proof.
iIntros "%Φ Hv post". wp_apply (AList.wp_insert with "Hv").
iIntros "Hv". iApply "post". by rewrite /tmap fmap_insert.
Qed.

Lemma wp_tmap_delete E v m k :
  {{{ tmap v m }}}
    AList.delete v k @ E
  {{{ RET #(); tmap v (delete k m) }}}.
Proof.
iIntros "%Φ Hv post". wp_apply (AList.wp_delete with "Hv").
iIntros "Hv". iApply "post". by rewrite /tmap fmap_delete.
Qed.

End TMap.

(* ------------------------------------------------------------------ *)
(** ** Secrecy. *)

Section Hidden.

Context `{!heapGS Σ, !cryptisGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (t : term).

(* [t] never becomes known to the attacker. *)
Definition hidden t : iProp := □ (public t → ▷ False).

Global Instance hidden_persistent t : Persistent (hidden t).
Proof. apply _. Qed.

Lemma hidden_public t : hidden t -∗ public t -∗ ▷ False.
Proof. iIntros "#h #p". by iApply "h". Qed.

(* Once a contradiction is one step away, anything is hidden. *)
Lemma hidden_false t : ▷ False -∗ hidden t.
Proof. by iIntros "#contra !> _". Qed.

(* A hidden key protects everything. *)
Lemma hidden_guard t t' : hidden t -∗ minted t' -∗ □ (public t → public t').
Proof.
iIntros "#h #m !> #p". iApply False_public => //. by iApply "h".
Qed.

(* A nonce created with [mk_nonce (λ _, ⌜pub = true⌝)]. *)
Lemma nonce_pub_true t :
  □ (public t ↔ ▷ □ ⌜true = true⌝) -∗ public t.
Proof. iIntros "#s". by iApply "s". Qed.

Lemma nonce_pub_false t :
  □ (public t ↔ ▷ □ ⌜false = true⌝) -∗ hidden t.
Proof.
iIntros "#s !> #p". iPoseProof ("s" with "p") as "{p} p".
iModIntro. by iDestruct "p" as "%".
Qed.

End Hidden.

(* ------------------------------------------------------------------ *)
(** ** Protocol predicates. *)

Definition reqN   := oidcN.@"meta".@"req".
Definition sessN  := oidcN.@"meta".@"op_sess".
Definition grantN := oidcN.@"meta".@"grant".

Section Preds.

Context `{!heapGS Σ, !cryptisGS Σ, !oidcParams}.
Notation iProp := (iProp Σ).

Implicit Types (t path params cookie resp host code : term).
Implicit Types (k : senc_key).

(* [c] is a session cookie of the provider, for subject [s]. *)
Definition op_session (c s : term) : iProp :=
  term_meta c sessN s ∗
  public s ∗
  ⌜c ≠ TInt 0⌝ ∗
  (⌜s = hsub⌝ → hidden c).

(* [code] was issued by the provider for subject [s] and client [cl]. *)
Definition code_grant (code s cl : term) : iProp :=
  term_meta code grantN (s, cl) ∗
  public s ∗
  public cl ∗
  (⌜cl = hcid ∧ s = hsub⌝ → hidden code).

Lemma op_session_agree c s1 s2 :
  op_session c s1 -∗ op_session c s2 -∗ ⌜s1 = s2⌝.
Proof.
iIntros "(#m1 & _) (#m2 & _)". iApply (term_meta_agree with "m1 m2").
Qed.

Lemma code_grant_agree code s1 cl1 s2 cl2 :
  code_grant code s1 cl1 -∗ code_grant code s2 cl2 -∗ ⌜s1 = s2 ∧ cl1 = cl2⌝.
Proof.
iIntros "(#m1 & _) (#m2 & _)".
iPoseProof (term_meta_agree with "m1 m2") as "%e". by case: e => -> ->.
Qed.

Lemma code_grant_minted code s cl : code_grant code s cl -∗ minted code.
Proof. iIntros "(#m & _)". by iApply (term_meta_minted with "m"). Qed.

(** *** What an honest client promises about a request. *)

Definition cookie_ok (c : term) : iProp := ⌜c = TInt 0⌝ ∨ hidden c.

Definition req_ok path params cookie : iProp :=
  cookie_ok cookie ∗
  (⌜path = op_authorize⌝ → public params) ∗
  (⌜path = rp_cb⌝ →
     public params ∨
     ⌜∃ code state, params = Spec.of_list [code; state; hiss]⌝).

(** *** What an honest server promises about its response. *)

Definition op_login_resp params resp : iProp :=
  ∃ s p sid,
    ⌜params = Spec.of_list [s; p]⌝ ∗
    ⌜resp = http_page sid (TInt 0)⌝ ∗
    hidden sid ∗
    op_session sid s.

Definition op_authorize_resp params cookie resp : iProp :=
  ∃ cl redir state nonce ch s rhost rpath code,
    ⌜params = Spec.of_list [cl; redir; state; nonce; ch]⌝ ∗
    ⌜resp = http_redirect (TInt 0) rhost rpath
              (Spec.of_list [code; state; hiss])⌝ ∗
    op_session cookie s ∗
    code_grant code s cl ∗
    public rhost ∗ public rpath ∗ public state ∗
    ⌜cl = hcid → rhost = rp_host ∧ rpath = rp_cb⌝ ∗
    (⌜cl ≠ hcid⌝ → public code).

Definition id_token (s cl nonce : term) : term :=
  TSeal skOP (Spec.tag (Tag (oidcN.@"id_token"))
                (Spec.of_list [hiss; s; cl; nonce])).

Definition op_token_resp params resp : iProp :=
  ∃ cl sec code verifier s nonce,
    ⌜params = Spec.of_list [cl; sec; code; verifier]⌝ ∗
    ⌜resp = http_page (TInt 0) (Spec.of_list [id_token s cl nonce])⌝ ∗
    public resp ∗
    code_grant code s cl.

Definition rp_login_resp params resp : iProp :=
  ∃ i sid ophost state nonce ch,
    ⌜params = Spec.of_list [i]⌝ ∗
    ⌜resp = http_redirect sid ophost op_authorize
              (Spec.of_list [hcid; Spec.of_list [rp_host; rp_cb];
                             state; nonce; ch])⌝ ∗
    hidden sid ∗
    public ophost ∗ public state ∗ public nonce ∗ public ch ∗
    ⌜i = hiss → ophost = op_host⌝.

Definition rp_cb_resp params resp : iProp :=
  ∃ code state i s,
    ⌜params = Spec.of_list [code; state; i]⌝ ∗
    ⌜resp = http_page (TInt 0) (Spec.of_list [i; s])⌝ ∗
    (⌜i = hiss⌝ → code_grant code s hcid).

Definition resp_ok path params cookie resp : iProp :=
  ⌜path = op_login⌝ ∗ op_login_resp params resp ∨
  ⌜path = op_authorize⌝ ∗ op_authorize_resp params cookie resp ∨
  ⌜path = op_token⌝ ∗ op_token_resp params resp ∨
  ⌜path = rp_login⌝ ∗ rp_login_resp params resp ∨
  ⌜path = rp_cb⌝ ∗ rp_cb_resp params resp.

Global Instance resp_ok_persistent path params cookie resp :
  Persistent (resp_ok path params cookie resp).
Proof. apply _. Qed.

Lemma resp_ok_op_login params cookie resp :
  resp_ok op_login params cookie resp -∗ op_login_resp params resp.
Proof.
by iIntros "[[_ ?]|[[% _]|[[% _]|[[% _]|[% _]]]]]" => //; tag_discr.
Qed.

Lemma resp_ok_op_authorize params cookie resp :
  resp_ok op_authorize params cookie resp -∗
  op_authorize_resp params cookie resp.
Proof.
by iIntros "[[% _]|[[_ ?]|[[% _]|[[% _]|[% _]]]]]" => //; tag_discr.
Qed.

Lemma resp_ok_op_token params cookie resp :
  resp_ok op_token params cookie resp -∗ op_token_resp params resp.
Proof.
by iIntros "[[% _]|[[% _]|[[_ ?]|[[% _]|[% _]]]]]" => //; tag_discr.
Qed.

Lemma resp_ok_rp_login params cookie resp :
  resp_ok rp_login params cookie resp -∗ rp_login_resp params resp.
Proof.
by iIntros "[[% _]|[[% _]|[[% _]|[[_ ?]|[% _]]]]]" => //; tag_discr.
Qed.

Lemma resp_ok_rp_cb params cookie resp :
  resp_ok rp_cb params cookie resp -∗ rp_cb_resp params resp.
Proof.
by iIntros "[[% _]|[[% _]|[[% _]|[[% _]|[_ ?]]]]]" => //; tag_discr.
Qed.

(** *** The predicates attached to the cryptographic messages. *)

(* client → server : aenc pkS ⟨kResp, ⟨path, params, cookie⟩⟩.  The response
   key is hidden and remembers the request it was created for. *)
Definition tls_req_pred (skS : aenc_key) t : iProp :=
  ∃ k path params cookie,
    ⌜t = Spec.of_list [(k : term); http_req path params cookie]⌝ ∗
    hidden k ∗
    term_meta k reqN (path, params, cookie) ∗
    req_ok path params cookie.

(* server → client : senc kResp resp. *)
Definition tls_resp_pred k resp : iProp :=
  ∃ path params cookie,
    term_meta k reqN (path, params, cookie) ∗
    resp_ok path params cookie resp.

(* An id_token names a subject and a client some code was granted for.  The
   proof of the game does not use this: the relying party gets the id_token
   over TLS from the token endpoint, and relies on that instead. *)
Definition id_token_pred (sk : sign_key) t : iProp :=
  ∃ code s aud nonce,
    ⌜t = Spec.of_list [Spec.pkey sk; s; aud; nonce]⌝ ∗
    code_grant code s aud.

Definition oidc_ctx : iProp :=
  sign_pred (oidcN.@"id_token") id_token_pred ∗
  aenc_pred (oidcN.@"tls_req") tls_req_pred ∗
  senc_pred (oidcN.@"tls_resp") tls_resp_pred ∗
  minted skOP ∗ hidden skOP ∗
  minted skOPt ∗ hidden skOPt ∗
  minted skRP ∗ hidden skRP ∗
  public hsub ∗
  minted hpw ∗ hidden hpw.

Global Instance oidc_ctx_persistent : Persistent oidc_ctx.
Proof. apply _. Qed.

Lemma oidc_ctx_public :
  oidc_ctx -∗ public hiss ∗ public hcid ∗ public op_pk.
Proof.
iIntros "(_ & _ & _ & #? & _ & #? & _ & #? & _)".
rewrite /hiss /hcid /op_pk public_verify_key !public_aenc_key. by eauto.
Qed.

Lemma oidc_alloc E1 E2 E3 :
  ↑oidcN ⊆ E1 →
  ↑oidcN ⊆ E2 →
  ↑oidcN ⊆ E3 →
  seal_pred_token SIGN E1 -∗
  seal_pred_token AENC E2 -∗
  seal_pred_token SENC E3 -∗
  minted skOP -∗ hidden skOP -∗
  minted skOPt -∗ hidden skOPt -∗
  minted skRP -∗ hidden skRP -∗
  public hsub -∗
  minted hpw -∗ hidden hpw ==∗
  oidc_ctx.
Proof.
iIntros (???) "sign_tok aenc_tok senc_tok #? #? #? #? #? #? #? #? #?".
iMod (sign_pred_set (N := oidcN.@"id_token") id_token_pred with "sign_tok")
  as "[#? _]"; first solve_ndisj.
iMod (aenc_pred_set (N := oidcN.@"tls_req") tls_req_pred with "aenc_tok")
  as "[#? _]"; first solve_ndisj.
iMod (senc_pred_set (N := oidcN.@"tls_resp") tls_resp_pred with "senc_tok")
  as "[#? _]"; first solve_ndisj.
iModIntro. rewrite /oidc_ctx. by do !iSplit.
Qed.

Lemma oidc_ctx_unfold :
  oidc_ctx -∗
  minted skOP ∗ hidden skOP ∗
  minted skOPt ∗ hidden skOPt ∗
  minted skRP ∗ hidden skRP ∗
  public hsub ∗
  minted hpw ∗ hidden hpw.
Proof. by iIntros "(_ & _ & _ & ?)". Qed.

(** *** Requests and responses as the servers see them. *)

(* What a server knows about a request it has decrypted: the attacker made it,
   or an honest client did. *)
Definition req_from (kResp req : term) : iProp :=
  public kResp ∗ public req ∨
  ∃ k path params cookie,
    ⌜kResp = k⌝ ∗ ⌜req = http_req path params cookie⌝ ∗
    hidden k ∗
    term_meta k reqN (path, params, cookie) ∗
    req_ok path params cookie.

(* What a server owes for a response it sends. *)
Definition resp_for (kResp resp : term) : iProp :=
  minted resp ∗
  (public kResp ∗ public resp ∨
   ∃ k path params cookie,
     ⌜kResp = k⌝ ∗
     hidden k ∗
     term_meta k reqN (path, params, cookie) ∗
     resp_ok path params cookie resp).

(* The same, with the case distinction as a flag: [pub] says that the request
   came from the attacker. *)
Definition req_view (pub : bool) (kResp path params cookie : term) : iProp :=
  if pub then
    (public kResp ∗ public path ∗ public params ∗ public cookie)%I
  else
    (∃ k, ⌜kResp = k⌝ ∗
          hidden k ∗
          term_meta k reqN (path, params, cookie) ∗
          req_ok path params cookie)%I.

Global Instance req_view_persistent pub kResp path params cookie :
  Persistent (req_view pub kResp path params cookie).
Proof. case: pub; apply _. Qed.

Lemma req_from_view kResp path params cookie :
  req_from kResp (http_req path params cookie) -∗
  ∃ pub, req_view pub kResp path params cookie.
Proof.
iIntros "[[#p_k #p_req]|#req]".
- iExists true. rewrite /http_req public_of_list /=.
  iDestruct "p_req" as "(? & ? & ? & _)". by eauto.
- iDestruct "req" as "(%k & %path' & %params' & %cookie' & -> & %e & ?)".
  case/Spec.of_list_inj: e => <- <- <-.
  iExists false. iExists k. by eauto.
Qed.

Lemma resp_for_intro pub kResp path params cookie resp :
  req_view pub kResp path params cookie -∗
  minted resp -∗
  (if pub then public resp else resp_ok path params cookie resp) -∗
  resp_for kResp resp.
Proof.
iIntros "#view #m_resp #resp". iSplit => //. case: pub.
- iLeft. iDestruct "view" as "(? & _)". by eauto.
- iRight. iDestruct "view" as "(%k & -> & ? & ? & _)".
  iExists k, path, params, cookie. by eauto.
Qed.

End Preds.

(* The endpoint constants are public. *)
Section Consts.

Context `{!heapGS Σ, !cryptisGS Σ}.

Lemma minted_TagE N : minted (Tag N) ⊣⊢ True.
Proof. iSplit; first by eauto. iIntros "_". by iApply minted_Tag. Qed.

Lemma public_op_login : public op_login ⊣⊢ True.
Proof. exact: public_Tag. Qed.
Lemma public_op_authorize : public op_authorize ⊣⊢ True.
Proof. exact: public_Tag. Qed.
Lemma public_op_token : public op_token ⊣⊢ True.
Proof. exact: public_Tag. Qed.
Lemma public_rp_login : public rp_login ⊣⊢ True.
Proof. exact: public_Tag. Qed.
Lemma public_rp_cb : public rp_cb ⊣⊢ True.
Proof. exact: public_Tag. Qed.
Lemma public_op_host : public op_host ⊣⊢ True.
Proof. exact: public_Tag. Qed.
Lemma public_rp_host : public rp_host ⊣⊢ True.
Proof. exact: public_Tag. Qed.

Lemma minted_op_login : minted op_login ⊣⊢ True.
Proof. exact: minted_TagE. Qed.
Lemma minted_op_authorize : minted op_authorize ⊣⊢ True.
Proof. exact: minted_TagE. Qed.
Lemma minted_op_token : minted op_token ⊣⊢ True.
Proof. exact: minted_TagE. Qed.
Lemma minted_rp_login : minted rp_login ⊣⊢ True.
Proof. exact: minted_TagE. Qed.
Lemma minted_rp_cb : minted rp_cb ⊣⊢ True.
Proof. exact: minted_TagE. Qed.
Lemma minted_op_host : minted op_host ⊣⊢ True.
Proof. exact: minted_TagE. Qed.
Lemma minted_rp_host : minted rp_host ⊣⊢ True.
Proof. exact: minted_TagE. Qed.

End Consts.

Definition constsE :=
  (@public_op_login, @public_op_authorize, @public_op_token,
   @public_rp_login, @public_rp_cb, @public_op_host, @public_rp_host,
   @minted_op_login, @minted_op_authorize, @minted_op_token,
   @minted_rp_login, @minted_rp_cb, @minted_op_host, @minted_rp_host).

(* Push [minted] and [public] through the term constructors, everywhere. *)
Ltac term_simpl :=
  rewrite /http_req /http_redirect /http_page;
  repeat (progress (rewrite ?minted_of_list ?public_of_list
                            ?minted_tag ?public_tag
                            ?minted_TInt ?public_TInt ?constsE /=)).

(* Name the pieces of ["octx" : oidc_ctx]. *)
Ltac octx_destruct :=
  iPoseProof (oidc_ctx_public with "octx") as "(#p_iss & #p_cid & #p_oppk)";
  iPoseProof (oidc_ctx_unfold with "octx")
    as "(#m_skOP & #h_skOP & #m_skOPt & #h_skOPt & #m_skRP & #h_skRP &
         #p_hsub & #m_hpw & #h_hpw)".
