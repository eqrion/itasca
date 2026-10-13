import Itasca.Module.Code.Encoding

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

/-- The implementation caps apply to flattened declared locals and the exact
instruction bytes after the local-declaration vector, including the final end.
The size prefix and locals bytes are not counted as instruction-body bytes. -/
def CodeEncodingWithinLimits (entry : Code) (bytes : List U8) : Prop :=
  entry.declared.length ≤ limits.MAX_LOCALS.val ∧
  ∃ size locals body, Leb128.Encoding size (locals.length + body.length) ∧
    VecEncoding LocalEncoding entry.locals locals ∧ BodyEncoding entry.body body ∧
    body.length ≤ limits.MAX_FUNCTION_BYTES.val ∧ bytes = size ++ locals ++ body

theorem CodeEncodingWithinLimits.encoding {entry bytes} (h : CodeEncodingWithinLimits entry bytes) :
    CodeEncoding entry bytes := by
  obtain ⟨_, size, locals, body, hs, hl, hb, _, he⟩ := h
  exact ⟨size, locals, body, hs, hl, hb, he⟩

theorem CodeEncodingWithinLimits.local_bound {entry bytes} (h : CodeEncodingWithinLimits entry bytes) :
    entry.declared.length ≤ limits.MAX_LOCALS.val := h.1

end Itasca.ModuleBinary
