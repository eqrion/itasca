# Decoding uniqueness

A byte sequence can determine a unique module even though a module can have several encodings. For example, Wasm permits some nonminimal LEB128 encodings. The reader proofs preserve the consumed bytes and the remaining suffix, so instruction and section boundaries can be recovered when composing readers. See the [LEB128 proofs](LebReaders.lean) and [module uniqueness proof](ModuleUnique.lean).
