From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.heap_lang Require Import notation proofmode adequacy.
From iris.heap_lang.lib Require Import assert.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis.examples Require Import alist.
From oidc Require Import impl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*

The security game.  It fixes what "secure" means for the model in [impl.v]: the
game is a HeapLang program that runs the honest parties next to the attacker and
[assert]s the properties we care about, so that

    security  =  no thread of [run_network game] ever gets stuck

(see [oidc_secure] at the end).  This file only *states* the goal; it is proved
in [proofs/security.v] ([oidc_is_secure]).

** Parties

  - an honest provider OP at [op_host] and an honest relying party RP at
    [rp_host], registered with each other;
  - an honest user with an account ⟨sub, pw⟩ at the OP, driving an honest
    browser that knows the TLS keys of exactly those two hosts;
  - the attacker, who
      . controls the network (the Cryptis Dolev–Yao attacker),
      . owns every other host: a host the browser has no key for is reached in
        the clear, and the attacker chooses the reply,
      . has an account, and a client with a redirect URI of its choice, at the
        honest OP,
      . is a provider trusted by the honest RP (a malicious IdP, with an
        authorization endpoint of its choice — possibly [op_host] itself),
      . can make the honest browser navigate anywhere, before the user logs in
        and after ([browse]).

** Winning conditions

  W1, authentication.  The attacker never holds an RP session that is logged in
      as the honest user: no cookie the attacker can produce is mapped to
      ⟨iss, sub⟩ in the RP's [logins] table.  Checked by [check_session] after
      every request the RP serves.

  W2, session integrity.  When the honest user logs in at the RP through the
      honest OP, the session they end up in is their own: the page the RP
      serves them says ⟨iss, sub⟩ and not, say, the attacker's account.
      Checked by the [assert] in [user].

** What this game can and cannot tell apart

The README asks that removing any single defence should make the proof fail.
For this game that is only true for some of them, and the proof in [proofs/]
says which.

  Used by the proof.  By a pen-and-paper argument each of these is needed on its
  own: dropping one gives an attack on W1.
    - the password check at the OP;
    - TLS: confidentiality of requests and responses, and the binding of a
      response to its request;
    - the origin-scoped cookie jar (the RP cookie would go to attacker hosts);
    - the RP looking its session up by the browser's cookie;
    - the OP sending the code to the redirect URI *registered* for the client
      (otherwise it would hand the honest user's code to an attacker host);
    - the code being bound to the client it was issued to (the attacker has
      the user authorize the *attacker's* client, with the nonce and PKCE
      challenge of the attacker's own session at the RP, and then has the RP
      redeem that code).

  Not used.  The proof treats [state], [nonce], the PKCE verifier and the
  client secret as public from the start, and never uses what the following
  checks establish:
    - the [state] comparison, the [nonce] comparison and PKCE, which all guard
      against a code turning up in the wrong session;
    - [client_secret] and single-use codes, which limit what a leaked code is
      worth;
    - the [iss]/[aud] claims of the id_token.  Its signature is verified, but
      the proof learns who logged in from the TLS connection to the token
      endpoint and never opens the signing predicate;
    - the [iss] comparison in the callback (RFC 9207): the RP picks the token
      endpoint from the callback's own [iss], so without the comparison it
      would still talk to the right provider;
    - the comparison of the [redirect_uri] parameter with the registered one:
      [OP.handle_authorize] redirects to the registered URI whatever the request
      says, so the comparison decides nothing.
  With the defences above in place the authorization code never reaches the
  attacker, and these only matter once it does, or once two flows overlap in
  one browser.

So the proof of this game does not, by itself, show that those defences do
anything.  Making them matter needs a stronger attacker, for instance:
  - leaking the authorization response of flows the user started (Referer,
    history, logs), which is what PKCE, [nonce] and [client_secret] are for.
    Leaking it for flows the *attacker* started is fatal whatever the RP does:
    the attacker lets the RP redeem the leaked code in the attacker's session;
  - letting attacker-driven navigations overlap with the user's own login
    (needs servers that answer failed requests instead of staying silent, so
    that a navigation always ends), which is what [state] is for;
  - an RP variant that picks the token endpoint from its session rather than
    from the callback, which is what RFC 9207 is for;
  - an OP variant that redirects to the [redirect_uri] of the request, which is
    what the comparison with the registered one is for.

** Simplifications

  - One attacker account, one attacker client and one attacker provider, all
    registered before the servers start: the tables in [impl.v] are not
    thread-safe.
  - The registrations refuse to overwrite the honest entries ([AList.find]
    returns the most recent binding), and the attacker's provider must come
    with well-formed keys.
  - The browser is sequential, and a navigation that gets no answer never
    returns, so the attacker's navigations cannot interleave with the user's
    two steps.

*)

Definition op_host : term := Tag (oidcN.@"op_host").
Definition rp_host : term := Tag (oidcN.@"rp_host").

(* ------------------------------------------------------------------ *)
(** ** The honest user. *)

(* Visit whatever URLs the attacker suggests, until the attacker sends something
   that is not a URL. *)
Definition browse : val := rec: "loop" "c" "b" :=
  (bind: "url" := list_of_term (recv "c") in
   list_match: ["host"; "path"; "params"] := "url" in
   Browser.navigate "c" "b" "host" "path" "params";;
   "loop" "c" "b");;
  #().

Definition user : val := λ: "c" "b" "sub" "pw" "iss",
  browse "c" "b";;
  Browser.navigate "c" "b" op_host op_login (term_of_list ["sub"; "pw"]);;
  let: "res" :=
    Browser.navigate "c" "b" rp_host rp_login (term_of_list ["iss"]) in
  match: "res" with
    NONE => #()
  | SOME "page" =>
    (* W2 *)
    assert: eq_term "page" (term_of_list ["iss"; "sub"])
  end;;
  browse "c" "b".

(* ------------------------------------------------------------------ *)
(** ** The honest relying party, with the W1 check. *)

(* The attacker names a cookie; it must not be logged in as [id]. *)
Definition check_session : val := λ: "c" "rp" "id",
  let: "guess" := recv "c" in
  match: AList.find (RP.logins "rp") "guess" with
    NONE => #()
  | SOME "id'" => assert: (~ eq_term "id'" "id")
  end.

Definition rp_loop : val := rec: "loop" "c" "rp" "id" :=
  RP.listen "c" "rp";;
  check_session "c" "rp" "id";;
  "loop" "c" "rp" "id".

(* ------------------------------------------------------------------ *)
(** ** What the attacker gets to register. *)

Definition register_attacker : val := λ: "c" "op" "rp" "sub" "cid" "iss",
  (* An account at the honest provider. *)
  let: "subA" := recv "c" in
  let: "pwA"  := recv "c" in
  (if: eq_term "subA" "sub" then #()
   else OP.register_user "op" "subA" "pwA");;
  (* A client at the honest provider, with any redirect URI. *)
  let: "cidA"    := recv "c" in
  let: "rhostA"  := recv "c" in
  let: "rpathA"  := recv "c" in
  let: "secretA" := recv "c" in
  (if: eq_term "cidA" "cid" then #()
   else OP.register_client "op" "cidA" "rhostA" "rpathA" "secretA");;
  (* A provider trusted by the honest relying party. *)
  let: "issA"    := recv "c" in
  let: "ophostA" := recv "c" in
  let: "optlsA"  := recv "c" in
  let: "secretP" := recv "c" in
  if: is_verify_key "issA" && is_aenc_key "optlsA" && ~ eq_term "issA" "iss"
  then RP.register_provider "rp" "issA" "ophostA" "optlsA" "secretP"
  else #().

(* ------------------------------------------------------------------ *)
(** ** The game. *)

Definition game : val := λ: "c",
  (* Honest keys; the public halves go to the attacker. *)
  let: "skOP"  := mk_sign_key #() in
  let: "skOPt" := mk_aenc_key #() in
  let: "skRP"  := mk_aenc_key #() in
  let: "iss"   := pkey "skOP" in
  let: "pkOPt" := pkey "skOPt" in
  let: "cid"   := pkey "skRP" in
  send "c" "iss";;
  send "c" "pkOPt";;
  send "c" "cid";;
  (* The honest servers, registered with each other. *)
  let: "op" := OP.new "skOP" "skOPt" in
  let: "rp" := RP.new "skRP" rp_host in
  let: "secret" := mk_nonce #() in
  OP.register_client "op" "cid" rp_host rp_cb "secret";;
  RP.register_provider "rp" "iss" op_host "pkOPt" "secret";;
  (* The honest user: a public identifier and a secret password. *)
  let: "sub" := mk_nonce #() in
  let: "pw"  := mk_nonce #() in
  send "c" "sub";;
  OP.register_user "op" "sub" "pw";;
  register_attacker "c" "op" "rp" "sub" "cid" "iss";;
  (* The honest browser knows the two honest hosts and nothing else. *)
  let: "b" := Browser.new #() in
  Browser.register "b" op_host "pkOPt";;
  Browser.register "b" rp_host "cid";;
  Fork (OP.serve "c" "op");;
  Fork (rp_loop "c" "rp" (term_of_list ["iss"; "sub"]));;
  Fork (user "c" "b" "sub" "pw" "iss").

(* The goal.  [run_network] starts the attacker next to the game; an [assert]
   that fails is a stuck thread. *)
Definition oidc_secure : Prop :=
  ∀ σ₁ σ₂ t₂ e₂,
    rtc erased_step ([run_network game], σ₁) (t₂, σ₂) →
    e₂ ∈ t₂ →
    not_stuck e₂ σ₂.
