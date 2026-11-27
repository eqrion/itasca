# Working on itasca proofs

## Keep the statement independent

Define Wasm binary syntax and exact byte encodings in `WebAssembly.Binary`. Keep reader spans, scalar conversions, and implementation limits in Itasca. For each grammar change, check reader soundness and completeness against the canonical production. Use the byte round trips to transport the original span, including nonminimal LEB spellings. Prove prefix uniqueness in WebAssembly so the module uniqueness proof builds independently of Itasca. Put Itasca-specific public semantic vocabulary in `Itasca/Itasca/Results/Definitions/` and public theorem statements in `Results/*.lean`. A reader should be able to inspect the premises of a completeness theorem without following the validator's control flow. In particular, state acceptance premises using the independent encoding and typing relations.

Keep implementation proofs out of the transitive imports of public definitions.

## Layer proofs by dependency

Each layer proves facts that the next layer can use through named lemmas or certificates. The import graph, including transitive imports, determines the boundary. Body proofs compose handler effects with decoding and typing facts. Entry validation uses body correctness and code framing. The streaming driver combines entry, environment, and tail evidence. A fact about an entry's size prefix should therefore be usable before importing the driver.

Put a new lemma with the definitions and contracts that suffice to prove it. If two layers need the same fact, import its narrowest owner in both. If a proof needs facts from two independent branches, place their composition above both branches.

## Put the Rust body behind one contract

For each extracted function you reason about, give its fully qualified name a single `.spec` theorem tagged `@[step]`. Unfold the function there. Callers use the contract via `step` or direct application. For an existing successful-call equation, recover its postcondition with:

```lean
have post := f.spec args
rw [called, WP.spec_ok] at post
```

Distinguish Aeneas normal return from Rust success. Match on the Rust result in the postcondition and describe the resulting state in each branch, including effects committed before an error. Prove invariant preservation from that effect. When a caller needs another fact about the body, strengthen the contract and update its callers together.

## Make re-extraction local

Name the witnesses introduced by `step` and split on named discriminants. Generated binder names and numbered match arms can change on re-extraction. Use explicit rewrites or `simp only` in intermediate steps. For large dispatches, prove one instruction family at a time using classifier equations.

After re-extraction, start with the contracts for functions in the generated diff. A changed bind sequence should require work only inside its contract. If elaboration becomes expensive, isolate the arithmetic fact or dispatch family responsible before raising a resource limit. Scope any necessary increase to the theorem.
