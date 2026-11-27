# Typing and declared references

The generated Wasm typing judgments omit the additional declaration condition on `ref.func`. The validation certificate carries that condition explicitly. [Typing](Typing.lean) supplies the declared-reference lemmas and inversions of generated typing derivations used when proving instruction acceptance.
