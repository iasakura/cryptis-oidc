From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis.examples Require Import alist.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*

OpenID Connect, authorization code flow with PKCE.  Skeleton only: this file
defines the executable HeapLang layer, no proofs yet.

Parties: an end user driving a Browser, a Relying Party (RP, the OIDC client)
and an OpenID Provider (OP).  Every RP/OP endpoint is reached over an abstract
server-authenticated TLS connection (module TLS below); the browser additionally
follows redirects and keeps an origin-scoped cookie jar, which is where most of
the interesting attack surface of this protocol lives.

  U -->  B : (user script) log in at the OP, then start a login at the RP
  B -->  OP: /login   ⟨sub, pw⟩
  OP -->  B: page, Set-Cookie: opsid                       (OP session)
  B -->  RP: /login   ⟨iss⟩
  RP -->  B: 303 → op_host /authorize
               ⟨client_id, redirect_uri, state, nonce, hash verifier⟩
             Set-Cookie: sid                               (RP session)
  B -->  OP: /authorize ⟨…⟩, Cookie: opsid
  OP -->  B: 303 → rp_host /cb ⟨code, state, iss⟩
  B -->  RP: /cb ⟨code, state, iss⟩, Cookie: sid
  RP -->  OP: /token ⟨client_id, secret, code, verifier⟩   (direct, not via B)
  OP -->  RP: ⟨id_token⟩
  RP -->  B : page ⟨sub⟩

  id_token = sign skOP ⟨iss, sub, aud, nonce⟩

Defences modelled explicitly, because each one is what rules out a known attack:
  - `state`, bound to the RP's cookie          → login CSRF
  - `iss` in the authorization response        → IdP mix-up (RFC 9207)
  - `nonce`, bound into the id_token           → id_token replay / injection
  - PKCE `hash verifier` / `verifier`          → authorization code injection
  - registered redirect_uri, exact match       → open redirect / code leak
  - single-use `code`, bound to `client_id`    → code replay
  - `client_secret` at the token endpoint      → client impersonation
  - origin-scoped cookie jar in the browser    → cross-site cookie leakage

*)

Definition oidcN := nroot.@"oidc".

(* Endpoint paths, as public constants. *)
Definition rp_login     : term := Tag (oidcN.@"rp_login").
Definition rp_cb        : term := Tag (oidcN.@"rp_cb").
Definition op_login     : term := Tag (oidcN.@"op_login").
Definition op_authorize : term := Tag (oidcN.@"op_authorize").
Definition op_token     : term := Tag (oidcN.@"op_token").

(* ------------------------------------------------------------------ *)
(** ** Abstract TLS: a server-authenticated confidential channel.

    client → server : aenc pkS ⟨kResp, req⟩
    server → client : senc kResp resp

    Only the holder of skS can read a request, and only somebody who learned the
    freshly generated kResp — that is, the server — can produce a response the
    client will accept.  This is deliberately weaker than [tls13]: no forward
    secrecy, no replay protection, no client authentication.  It is the piece to
    replace once [examples/tls13] closes. *)

Module TLS.

Definition request : val := λ: "c" "pkS" "req",
  let: "kResp" := mk_senc_key #() in
  send "c" (aenc "pkS" (Tag $ oidcN.@"tls_req")
                 (term_of_list ["kResp"; "req"]));;
  do_until (λ: <>, sdec "kResp" (Tag $ oidcN.@"tls_resp") (recv "c")).

Definition listen : val := λ: "c" "skS",
  do_until (λ: <>,
    bind: "m" := adec "skS" (Tag $ oidcN.@"tls_req") (recv "c") in
    bind: "m" := list_of_term "m" in
    list_match: ["kResp"; "req"] := "m" in
    SOME ("kResp", "req")).

Definition respond : val := λ: "c" "kResp" "resp",
  send "c" (senc "kResp" (Tag $ oidcN.@"tls_resp") "resp").

End TLS.

(* ------------------------------------------------------------------ *)
(** ** HTTP messages as terms.

    request  = ⟨path, params, cookie⟩
    response = ⟨set_cookie, payload⟩
    payload  = redirect ⟨host, path, params⟩ | page body

    "no cookie" is the integer 0. *)

Module HTTP.

Definition no_cookie : term := TInt 0.

Definition req : val := λ: "path" "params" "cookie",
  term_of_list ["path"; "params"; "cookie"].

Definition redirect : val := λ: "set_cookie" "host" "path" "params",
  term_of_list ["set_cookie";
                tag (Tag $ oidcN.@"redirect")
                    (term_of_list ["host"; "path"; "params"])].

Definition page : val := λ: "set_cookie" "body",
  term_of_list ["set_cookie"; tag (Tag $ oidcN.@"page") "body"].

End HTTP.

(* ------------------------------------------------------------------ *)
(** ** The browser.

    A browser is a pair of association lists:
      jar   : host ↦ cookie.  Origin-scoped — a cookie set by host H is only
              ever attached to a request going back to H.
      hosts : host ↦ TLS public key.  A host absent from this table models an
              attacker-controlled site that nevertheless has a valid
              certificate: the request goes out in the clear and the response is
              whatever the attacker chooses to send back. *)

Module Browser.

Definition new : val := λ: <>, (AList.new #(), AList.new #()).

Definition jar   : val := λ: "b", Fst "b".
Definition hosts : val := λ: "b", Snd "b".

Definition register : val := λ: "b" "host" "pk",
  AList.insert (hosts "b") "host" "pk".

Definition cookie_for : val := λ: "b" "host",
  match: AList.find (jar "b") "host" with
    NONE => HTTP.no_cookie
  | SOME "v" => "v"
  end.

Definition store_cookie : val := λ: "b" "host" "set_cookie",
  if: eq_term "set_cookie" HTTP.no_cookie then #()
  else AList.insert (jar "b") "host" "set_cookie".

Definition fetch : val := λ: "c" "b" "host" "path" "params",
  let: "req" := HTTP.req "path" "params" (cookie_for "b" "host") in
  match: AList.find (hosts "b") "host" with
    SOME "pk" => SOME (TLS.request "c" "pk" "req")
  | NONE =>
    send "c" (term_of_list ["host"; "req"]);;
    SOME (recv "c")
  end.

(* Follow redirects until a page comes back. *)
Definition navigate : val := λ: "c" "b",
  rec: "loop" "host" "path" "params" :=
    bind: "resp" := fetch "c" "b" "host" "path" "params" in
    bind: "resp" := list_of_term "resp" in
    list_match: ["set_cookie"; "payload"] := "resp" in
    store_cookie "b" "host" "set_cookie";;
    match: untag (Tag $ oidcN.@"redirect") "payload" with
      SOME "r" =>
        bind: "r" := list_of_term "r" in
        list_match: ["host2"; "path2"; "params2"] := "r" in
        "loop" "host2" "path2" "params2"
    | NONE => untag (Tag $ oidcN.@"page") "payload"
    end.

End Browser.

(* ------------------------------------------------------------------ *)
(** ** Relying party.

    State ⟨skTLS, host, providers, sessions, logins⟩ where
      skTLS     : TLS decryption key; [pkey skTLS] doubles as the client_id
      host      : the RP's own origin (used to build redirect_uri)
      providers : iss ↦ ⟨host, tls_pk, client_secret⟩ for each trusted OP
      sessions  : browser cookie ↦ ⟨iss, state, nonce, verifier⟩ (in flight)
      logins    : browser cookie ↦ sub                            (completed) *)

Module RP.

Definition new : val := λ: "skTLS" "host",
  ("skTLS", "host", AList.new #(), AList.new #(), AList.new #()).

Definition tls_sk    : val := λ: "s", Fst (Fst (Fst (Fst "s"))).
Definition host      : val := λ: "s", Snd (Fst (Fst (Fst "s"))).
Definition providers : val := λ: "s", Snd (Fst (Fst "s")).
Definition sessions  : val := λ: "s", Snd (Fst "s").
Definition logins    : val := λ: "s", Snd "s".

Definition client_id : val := λ: "s", pkey (tls_sk "s").

Definition redirect_uri : val := λ: "s",
  term_of_list [host "s"; rp_cb].

Definition register_provider : val := λ: "s" "iss" "ophost" "optls" "secret",
  AList.insert (providers "s") "iss"
    (term_of_list ["ophost"; "optls"; "secret"]).

(* GET /login ⟨iss⟩ — start a login at the provider [iss]. *)
Definition handle_login : val := λ: "s" "params",
  bind: "params" := list_of_term "params" in
  list_match: ["iss"] := "params" in
  bind: "prov" := AList.find (providers "s") "iss" in
  bind: "prov" := list_of_term "prov" in
  list_match: ["ophost"; "optls"; "secret"] := "prov" in
  let: "sid"      := mk_nonce #() in
  let: "state"    := mk_nonce #() in
  let: "nonce"    := mk_nonce #() in
  let: "verifier" := mk_nonce #() in
  AList.insert (sessions "s") "sid"
    (term_of_list ["iss"; "state"; "nonce"; "verifier"]);;
  SOME (HTTP.redirect "sid" "ophost" op_authorize
          (term_of_list [client_id "s"; redirect_uri "s";
                         "state"; "nonce"; hash "verifier"])).

(* GET /cb ⟨code, state, iss⟩ — the authorization response. *)
Definition handle_cb : val := λ: "c" "s" "params" "cookie",
  bind: "params" := list_of_term "params" in
  list_match: ["code"; "state"; "iss"] := "params" in
  bind: "sess" := AList.find (sessions "s") "cookie" in
  bind: "sess" := list_of_term "sess" in
  list_match: ["iss0"; "state0"; "nonce0"; "verifier"] := "sess" in
  (* CSRF defence, and the RFC 9207 issuer check against mix-up. *)
  guard: eq_term "state" "state0" && eq_term "iss" "iss0" in
  AList.delete (sessions "s") "cookie";;
  bind: "prov" := AList.find (providers "s") "iss" in
  bind: "prov" := list_of_term "prov" in
  list_match: ["ophost"; "optls"; "secret"] := "prov" in
  let: "treq" := HTTP.req op_token
                   (term_of_list [client_id "s"; "secret"; "code"; "verifier"])
                   HTTP.no_cookie in
  bind: "tresp" := list_of_term (TLS.request "c" "optls" "treq") in
  list_match: ["sc"; "payload"] := "tresp" in
  bind: "body" := untag (Tag $ oidcN.@"page") "payload" in
  bind: "body" := list_of_term "body" in
  list_match: ["id_token"] := "body" in
  bind: "claims" := verify "iss" (Tag $ oidcN.@"id_token") "id_token" in
  bind: "claims" := list_of_term "claims" in
  list_match: ["iss2"; "sub"; "aud"; "nonce2"] := "claims" in
  guard: eq_term "iss2" "iss"
      && eq_term "aud" (client_id "s")
      && eq_term "nonce2" "nonce0" in
  AList.insert (logins "s") "cookie" "sub";;
  SOME (HTTP.page HTTP.no_cookie "sub").

Definition handler : val := λ: "c" "s" "req",
  bind: "req" := list_of_term "req" in
  list_match: ["path"; "params"; "cookie"] := "req" in
  if: eq_term "path" rp_login then handle_login "s" "params"
  else if: eq_term "path" rp_cb then handle_cb "c" "s" "params" "cookie"
  else NONE.

Definition listen : val := λ: "c" "s",
  let: "res" := TLS.listen "c" (tls_sk "s") in
  match: handler "c" "s" (Snd "res") with
    SOME "resp" => TLS.respond "c" (Fst "res") "resp"
  | NONE => #()
  end.

Definition serve : val := rec: "loop" "c" "s" := listen "c" "s";; "loop" "c" "s".

End RP.

(* ------------------------------------------------------------------ *)
(** ** OpenID provider.

    State ⟨skSign, skTLS, clients, users, sessions, codes⟩ where
      skSign   : id_token signing key; [pkey skSign] is the issuer identifier
      skTLS    : TLS decryption key
      clients  : client_id ↦ ⟨redirect_host, redirect_path, client_secret⟩
      users    : sub ↦ password
      sessions : OP cookie ↦ sub          (users already authenticated here)
      codes    : code ↦ ⟨sub, client_id, nonce, challenge⟩ *)

Module OP.

Definition new : val := λ: "skSign" "skTLS",
  ("skSign", "skTLS", AList.new #(), AList.new #(), AList.new #(),
   AList.new #()).

Definition sign_sk  : val := λ: "s", Fst (Fst (Fst (Fst (Fst "s")))).
Definition tls_sk   : val := λ: "s", Snd (Fst (Fst (Fst (Fst "s")))).
Definition clients  : val := λ: "s", Snd (Fst (Fst (Fst "s"))).
Definition users    : val := λ: "s", Snd (Fst (Fst "s")).
Definition sessions : val := λ: "s", Snd (Fst "s").
Definition codes    : val := λ: "s", Snd "s".

Definition iss : val := λ: "s", pkey (sign_sk "s").

Definition register_client : val := λ: "s" "client_id" "rhost" "rpath" "secret",
  AList.insert (clients "s") "client_id"
    (term_of_list ["rhost"; "rpath"; "secret"]).

Definition register_user : val := λ: "s" "sub" "pw",
  AList.insert (users "s") "sub" "pw".

(* GET /login ⟨sub, pw⟩ — authenticate the end user, hand out an OP cookie. *)
Definition handle_login : val := λ: "s" "params",
  bind: "params" := list_of_term "params" in
  list_match: ["sub"; "pw"] := "params" in
  bind: "pw0" := AList.find (users "s") "sub" in
  guard: eq_term "pw" "pw0" in
  let: "sid" := mk_nonce #() in
  AList.insert (sessions "s") "sid" "sub";;
  SOME (HTTP.page "sid" (TInt 0)).

(* GET /authorize ⟨client_id, redirect_uri, state, nonce, challenge⟩. *)
Definition handle_authorize : val := λ: "s" "params" "cookie",
  bind: "params" := list_of_term "params" in
  list_match: ["client_id"; "redirect"; "state"; "nonce"; "challenge"]
    := "params" in
  bind: "sub" := AList.find (sessions "s") "cookie" in
  bind: "cl"  := AList.find (clients "s") "client_id" in
  bind: "cl"  := list_of_term "cl" in
  list_match: ["rhost"; "rpath"; "secret"] := "cl" in
  (* Exact match against the registered redirect URI. *)
  guard: eq_term "redirect" (term_of_list ["rhost"; "rpath"]) in
  let: "code" := mk_nonce #() in
  AList.insert (codes "s") "code"
    (term_of_list ["sub"; "client_id"; "nonce"; "challenge"]);;
  SOME (HTTP.redirect HTTP.no_cookie "rhost" "rpath"
          (term_of_list ["code"; "state"; iss "s"])).

(* POST /token ⟨client_id, secret, code, verifier⟩, straight from the RP. *)
Definition handle_token : val := λ: "s" "params",
  bind: "params" := list_of_term "params" in
  list_match: ["client_id"; "secret"; "code"; "verifier"] := "params" in
  bind: "cl" := AList.find (clients "s") "client_id" in
  bind: "cl" := list_of_term "cl" in
  list_match: ["rhost"; "rpath"; "secret0"] := "cl" in
  guard: eq_term "secret" "secret0" in            (* client authentication *)
  bind: "grant" := AList.find (codes "s") "code" in
  AList.delete (codes "s") "code";;               (* codes are single use *)
  bind: "grant" := list_of_term "grant" in
  list_match: ["sub"; "client_id0"; "nonce"; "challenge"] := "grant" in
  guard: eq_term "client_id" "client_id0" in      (* code bound to the client *)
  guard: eq_term (hash "verifier") "challenge" in (* PKCE *)
  let: "id_token" :=
    sign (sign_sk "s") (Tag $ oidcN.@"id_token")
      (term_of_list [iss "s"; "sub"; "client_id"; "nonce"]) in
  SOME (HTTP.page HTTP.no_cookie (term_of_list ["id_token"])).

Definition handler : val := λ: "s" "req",
  bind: "req" := list_of_term "req" in
  list_match: ["path"; "params"; "cookie"] := "req" in
  if: eq_term "path" op_login then handle_login "s" "params"
  else if: eq_term "path" op_authorize then handle_authorize "s" "params" "cookie"
  else if: eq_term "path" op_token then handle_token "s" "params"
  else NONE.

Definition listen : val := λ: "c" "s",
  let: "res" := TLS.listen "c" (tls_sk "s") in
  match: handler "s" (Snd "res") with
    SOME "resp" => TLS.respond "c" (Fst "res") "resp"
  | NONE => #()
  end.

Definition serve : val := rec: "loop" "c" "s" := listen "c" "s";; "loop" "c" "s".

End OP.

(* ------------------------------------------------------------------ *)
(** ** The honest end user.

    Authenticate at the provider, then start a login at the relying party.  The
    user's *intent* is the pair ⟨rphost, iss⟩; session integrity is the property
    that the RP never ends up with a session the user did not intend. *)

Definition user_script : val := λ: "c" "b" "ophost" "sub" "pw" "rphost" "iss",
  Browser.navigate "c" "b" "ophost" op_login (term_of_list ["sub"; "pw"]);;
  Browser.navigate "c" "b" "rphost" rp_login (term_of_list ["iss"]).
