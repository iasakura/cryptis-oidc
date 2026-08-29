From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics.
From oidc Require Import impl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*

Proof infrastructure for the OIDC model.  This file sets up the ghost state and
protocol invariants; the WP specs for the endpoints live in later files.

The security goal we are aiming at is *authentication*:

  if the honest relying party completes a login for subject [sub] against an
  honest provider [skOP], then [sub] really did authenticate at that provider.

The chain that carries this guarantee is

    OP.handle_login   mints   authenticated skOP sub
      └─ OP.handle_authorize  moves it into the authorization [code]
           └─ OP.handle_token  signs an id_token carrying it
                └─ RP.handle_cb  verifies the id_token and recovers it.

[authenticated skOP sub] is the persistent fact at the head of that chain; the
id_token signing predicate is what transports it across the network. *)

(* ------------------------------------------------------------------ *)
(** ** Ghost state: the set of completed logins.

    A single authoritative [gset (sign_key * term)]: the pair [(skOP, sub)] is in
    the set once [sub] has authenticated at provider [skOP].  Elements of a
    [gset] are core-id, so the fragment [authenticated skOP sub] is persistent
    and freely duplicable — exactly right for an "it happened" fact. *)

Definition oidc_authUR : ucmra := authUR (gsetUR (sign_key * term)).

Class oidcGpreS Σ := OidcGpreS {
  oidcGpreS_auth : inG Σ oidc_authUR;
}.

Class oidcGS Σ := OidcGS {
  oidcGS_auth  : inG Σ oidc_authUR;
  oidc_name    : gname;
}.

Local Existing Instances oidcGpreS_auth oidcGS_auth.

Definition oidcΣ : gFunctors := #[GFunctor oidc_authUR].

Global Instance subG_oidcGpreS Σ : subG oidcΣ Σ → oidcGpreS Σ.
Proof. solve_inG. Qed.

Section Base.

Context `{!heapGS Σ, !cryptisGS Σ, !oidcGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (skOP : sign_key) (sub aud nonce t : term).

(* The authoritative view; lives inside [oidc_ctx]. *)
Definition login_auth (S : gset (sign_key * term)) : iProp :=
  own oidc_name (● S).

(* The persistent witness that a login happened. *)
Definition authenticated skOP sub : iProp :=
  own oidc_name (◯ {[ (skOP, sub) ]}).

Global Instance authenticated_persistent skOP sub :
  Persistent (authenticated skOP sub).
Proof. apply _. Qed.

Global Instance authenticated_timeless skOP sub :
  Timeless (authenticated skOP sub).
Proof. apply _. Qed.

Lemma login_auth_agree S skOP sub :
  login_auth S -∗ authenticated skOP sub -∗ ⌜(skOP, sub) ∈ S⌝.
Proof.
iIntros "Hfull Hfrag".
iDestruct (own_valid_2 with "Hfull Hfrag") as %Hvalid.
rewrite auth_both_valid_discrete in Hvalid.
destruct Hvalid as [Hincl _].
iPureIntro. by apply gset_included, singleton_subseteq_l in Hincl.
Qed.

Lemma login_auth_mint S skOP sub :
  login_auth S ==∗ login_auth (S ∪ {[ (skOP, sub) ]}) ∗ authenticated skOP sub.
Proof.
iIntros "Hfull".
rewrite -own_op.
iApply (own_update with "Hfull").
apply auth_update_alloc.
apply local_update_unital_discrete => z _ Hz.
split; first done.
rewrite Hz left_id. set_solver.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The id_token signing predicate.

    An id_token is [sign skOP ⟨iss, sub, aud, nonce⟩] with [iss = pkey skOP].
    The invariant attached to the signature is that the subject really
    authenticated at this provider.  A holder of a verifiable id_token from an
    honest [skOP] can therefore conclude [authenticated skOP sub]. *)

Definition id_token_pred skOP t : iProp :=
  ∃ sub aud nonce,
    ⌜t = Spec.of_list [Spec.pkey skOP; sub; aud; nonce]⌝ ∗
    authenticated skOP sub.

(* ------------------------------------------------------------------ *)
(** ** Abstract TLS predicates.

    TODO: these are placeholders.  To get confidentiality of the token request
    (which is what protects [client_secret] and the authorization [code] in
    transit) and authenticity of the token response, the request/response
    predicates must pin the response key [kResp] to the server and mark the
    request body secret.  For now they are trivial, so the TLS layer is modelled
    as a plain public channel and only the id_token signature carries weight. *)

Definition tls_req_pred (pkS t : term) : iProp := True.
Definition tls_resp_pred (kResp t : term) : iProp := True.

(* ------------------------------------------------------------------ *)
(** ** The security context and its allocation. *)

Definition oidc_ctx : iProp :=
  sign_pred (oidcN.@"id_token") id_token_pred ∗
  aenc_pred (oidcN.@"tls_req") tls_req_pred ∗
  senc_pred (oidcN.@"tls_resp") tls_resp_pred.

Global Instance oidc_ctx_persistent : Persistent oidc_ctx.
Proof. apply _. Qed.

End Base.

(* Allocation happens before the ghost name is fixed, so it is stated over
   [oidcGpreS] and produces the [oidcGS] instance together with the context. *)

Lemma oidc_alloc `{!heapGS Σ, !cryptisGS Σ, !oidcGpreS Σ} E1 E2 E3 :
  ↑oidcN.@"id_token" ⊆ E1 →
  ↑oidcN.@"tls_req"  ⊆ E2 →
  ↑oidcN.@"tls_resp" ⊆ E3 →
  seal_pred_token SIGN E1 -∗
  seal_pred_token AENC E2 -∗
  seal_pred_token SENC E3 ==∗
  ∃ _ : oidcGS Σ,
    oidc_ctx ∗
    login_auth ∅ ∗
    seal_pred_token SIGN (E1 ∖ ↑oidcN.@"id_token") ∗
    seal_pred_token AENC (E2 ∖ ↑oidcN.@"tls_req") ∗
    seal_pred_token SENC (E3 ∖ ↑oidcN.@"tls_resp").
Proof.
iIntros (?? ?) "sign_tok aenc_tok senc_tok".
iMod (own_alloc (● (∅ : gset (sign_key * term)))) as (γ) "Hauth".
{ by apply auth_auth_valid. }
pose (HG := {| oidcGS_auth := oidcGpreS_auth; oidc_name := γ |} : oidcGS Σ).
iMod (sign_pred_set (N := oidcN.@"id_token") id_token_pred with "sign_tok")
  as "[#Hsign sign_tok]"; first done.
iMod (aenc_pred_set (N := oidcN.@"tls_req") tls_req_pred with "aenc_tok")
  as "[#Haenc aenc_tok]"; first done.
iMod (senc_pred_set (N := oidcN.@"tls_resp") tls_resp_pred with "senc_tok")
  as "[#Hsenc senc_tok]"; first done.
iModIntro. iExists HG. iFrame. by iSplit; [|iSplit].
Qed.

(* ------------------------------------------------------------------ *)
(** ** The core authentication guarantee.

    From a verifiable id_token signed by an honest (uncorrupted) provider, and
    given that we know which subject the token names, recover the fact that the
    subject authenticated. *)

Section Guarantee.

Context `{!heapGS Σ, !cryptisGS Σ, !oidcGS Σ}.
Notation iProp := (iProp Σ).

Lemma id_token_authentic (skOP : sign_key) sub aud nonce :
  oidc_ctx -∗
  public (TSeal skOP
            (Spec.tag (Tag (oidcN.@"id_token"))
               (Spec.of_list [Spec.pkey skOP; sub; aud; nonce]))) -∗
  public (Spec.of_list [Spec.pkey skOP; sub; aud; nonce]) ∗
  (public skOP ∨ ▷ authenticated skOP sub).
Proof.
iIntros "(#Hsign & _ & _) #Htoken".
iPoseProof (public_signE with "Htoken Hsign") as "[$ Hcase]".
iDestruct "Hcase" as "[Hcorrupt | #Hinv]".
{ iLeft. by iApply "Hcorrupt". }
iRight. iNext. iDestruct "Hinv" as "(%sub' & %aud' & %nonce' & %He & Hauth)".
move: He => /Spec.of_list_inj [] <- _ _.
by iExact "Hauth".
Qed.

End Guarantee.
