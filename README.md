# cryptis-oidc

A symbolic (Dolev–Yao) model of **OpenID Connect**, authorization code flow with
PKCE, built on [Cryptis](https://github.com/arthuraa/cryptis) — a separation
logic for cryptographic protocols on top of Iris and HeapLang.

Status: **skeleton**. `oidc/impl.v` defines the executable HeapLang layer
(browser, relying party, provider) and compiles. No proofs yet.

## Why this is not just a crypto proof

The known attacks on OIDC — IdP mix-up, authorization code injection, login
CSRF, open-redirect code leakage — come from the *web platform*, not from misuse
of cryptographic primitives. So the model has to include a browser: an
origin-scoped cookie jar, redirect following, and hosts that may be
attacker-controlled. That is what `Browser` in `oidc/impl.v` is for.

## The flow

```
U  →  B : (user_script) log in at the OP, then start a login at the RP
B  →  OP: /login   ⟨sub, pw⟩
OP →  B : page,  Set-Cookie: opsid
B  →  RP: /login   ⟨iss⟩
RP →  B : 303 → op_host /authorize ⟨client_id, redirect_uri, state, nonce, hash verifier⟩
          Set-Cookie: sid
B  →  OP: /authorize ⟨…⟩, Cookie: opsid
OP →  B : 303 → rp_host /cb ⟨code, state, iss⟩
B  →  RP: /cb ⟨code, state, iss⟩, Cookie: sid
RP →  OP: /token ⟨client_id, secret, code, verifier⟩     (direct, not via B)
OP →  RP: ⟨id_token⟩
RP →  B : page ⟨sub⟩

id_token = sign skOP ⟨iss, sub, aud, nonce⟩
```

## Term encoding

| OIDC concept | Cryptis term |
| --- | --- |
| host / origin, endpoint path | `Tag (oidcN.@"rp_login")` etc., public constants |
| `client_id` | `pkey skRP_tls` (the RP's TLS public key doubles as its client id) |
| `iss` | `pkey skOP_sign` |
| `state`, `nonce`, `code_verifier`, `code`, cookies | `mk_nonce #()` |
| `code_challenge` | `hash verifier` |
| `id_token` | `sign skOP (Tag $ oidcN.@"id_token") ⟨iss, sub, aud, nonce⟩` |
| HTTP request | `⟨path, params, cookie⟩` |
| HTTP response | `⟨set_cookie, payload⟩`, `payload = redirect⟨host,path,params⟩ \| page body` |
| absent cookie | `TInt 0` |
| cookie jar / session tables | `AList` (from `cryptis.examples.alist`) |

## Defences modelled explicitly

Each one is what rules out a specific known attack.

| Defence | Attack it blocks |
| --- | --- |
| `state`, bound to the RP's cookie | login CSRF |
| `iss` in the authorization response | IdP mix-up (RFC 9207) |
| `nonce`, bound into the id_token | id_token replay / injection |
| PKCE `hash verifier` / `verifier` | authorization code injection |
| registered redirect_uri, exact match | open redirect / code leak |
| single-use `code`, bound to `client_id` | code replay |
| `client_secret` at the token endpoint | client impersonation |
| origin-scoped cookie jar | cross-site cookie leakage |

## Deliberately out of scope (for now)

- Referer headers / URL leakage; JavaScript, XSS, `postMessage`
- Cookie path scoping and the `Secure` / `HttpOnly` / `SameSite` attributes
  (one cookie per origin)
- DNS and subdomain relationships — origins are opaque constants
- Time, hence `exp` / `iat`
- One browser tab, so no attack needing two concurrent navigations

The `TLS` module is an abstract server-authenticated confidential channel
(`aenc pkS ⟨kResp, req⟩` / `senc kResp resp`), not a real handshake: no forward
secrecy, no replay protection, no client authentication. Replace it once
`cryptis`'s own `examples/tls13` closes.

## Next step

The proofs. The centre of gravity is the provider's signing predicate:

```coq
sign_pred (oidcN.@"id_token") (λ skOP m,
  ∃ sub aud nonce, ⌜m = Spec.of_list [Spec.pkey skOP; sub; aud; nonce]⌝ ∗
    authorized skOP sub aud nonce)
```

Before proving anything, write the game and check that removing any single
defence above makes the proof *fail* — otherwise a closed proof may only mean
the model is too weak to express the attack.

## Building

```bash
nix develop        # or: nix develop .#ai   (adds rocq-mcp)
make
```

`cryptis` comes in as a flake input, so `nix flake update cryptis` is what bumps
the dependency, and `flake.lock` records which revision the proofs were checked
against. The first build compiles all of cryptis and takes a while.
