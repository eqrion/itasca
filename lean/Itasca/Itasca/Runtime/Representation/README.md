# Decoding slots and stores

[Values](Values.lean) relates slot contents to source values. Decoding a store also requires knowing which source body each compiled function represents. [Store](Store.lean) uses that code interpretation to recover source objects. These facts are shared by the compiler that establishes the interpretation and the interpreter that relies on it.
