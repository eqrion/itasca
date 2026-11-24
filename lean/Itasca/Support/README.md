# Shared validation foundations

[Translation](Translation.lean) proves agreement between extracted types and
SpecTec types, well-formed translated contexts, environment lookups and control
frames. It also provides the shared Aeneas-result inversion used by handlers.
The semantic translations themselves live in the narrow
[Interface translation owner](../Results/Definitions/Foundations.lean#L49).

[LiteralDispatch](Translation.lean) provides simplifier procedures for literal
byte dispatch. They reduce only concrete scalar discriminants and supply kernel
reduction proofs. They add no logical assumptions and must remain separate from
operation correctness.

Handlers and higher constructions consume these foundations. Support cannot
import validator orchestration or runtime implementation proofs, including through
Interface. Shared lemmas belong here only when their dependencies respect that
boundary.
