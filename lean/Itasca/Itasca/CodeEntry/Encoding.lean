import Itasca.Module.Definitions
import Itasca.Results.Definitions.Validation
import Itasca.Body.LoopDispatch
import Itasca.Binary.Body.Encoding
import Itasca.Module.Code.ContextTransport

open WebAssembly

/-! ## CodeEntry -/

section

/-!
# Code entries

Specification of a code entry: `CodeEncoding` (size prefix, local declarations
and `BodyBytes`), `Typed` (declarative typing and declared references)
and `Entry`, which combines them for the entry an accepted validation run describes. Also relates
the Wasm 2.0 token consumption to `Binary.Rep`, and `Typed` to `CodeEntry.Typed`.
-/

open Aeneas Aeneas.Std

namespace Itasca.CodeEntry

/-- A bounded code entry encoding is a code entry encoding. -/
theorem CodeEncodingWithinLimits.encoding {entry bytes}
    (h : CodeEncodingWithinLimits entry bytes) : CodeEncoding entry bytes := by
  obtain ⟨_, size, locals, body, hs, hl, ⟨hb, _⟩, he⟩ := h
  exact ⟨size, locals, body, hs, hl, hb, he⟩

/-- The specification of the code entry for function `index` between byte offsets `start` and
`finish`: it parses as a `CodeEncoding`, satisfies `Typed` against the function's type, and
stays within the local limit. -/
def Entry (data : Slice U8) (env : metadata.Env)
    (index start finish : Usize) : Prop :=
  ∃ entry, Binary.At (CodeEncoding) data start entry finish ∧
    ∃ hi : index.val < env.func_type_indices.val.length,
      Typed env env.func_type_indices.val[index.val] entry ∧
      entry.declared.length ≤ limits.MAX_LOCALS.val

/-- Wasm 2.0 tokens consumed from `data` form a `Rep` of `TokenEncoding` over the same span. -/
theorem consumed_rep {data start tokens next}
    (h : Body.Consumed data start tokens next) :
    Binary.At (Binary.Rep Body.TokenEncoding) data start tokens next := by
  induction h with
  | nil hb => exact ⟨[], .nil, Body.Scalar.BytesAt.nil _ _ hb⟩
  | snoc _ ht ih =>
    obtain ⟨bs, he, hs⟩ := ih
    obtain ⟨cs, hc, hp⟩ := ht
    exact ⟨bs ++ cs, he.snoc hc, hs.append hp⟩

/-- A `Rep` of `TokenEncoding` over a span of `data` is consumed as Wasm 2.0 tokens. -/
theorem rep_consumed {data start next tokens bytes}
    (he : Binary.Rep Body.TokenEncoding tokens bytes)
    (hs : Body.Scalar.BytesAt data start bytes next) : Body.Consumed data start tokens next := by
  induction he generalizing start with
  | nil =>
    have hn := hs.empty
    subst next
    exact .nil _ hs.bound
  | cons ht _ ih =>
    obtain ⟨middle, hfirst, hrest⟩ := hs.split
    exact Body.Consumed.cons_iff.mpr ⟨middle, ⟨_, ht, hfirst⟩, ih hrest⟩

/-- `Body.BodyEncoding` over a slice gives `BodyBytes` of its contents. -/
theorem body_encoding_bytes {data ops} (h : Body.BodyEncoding data ops) :
    BodyBytes ops data.val := by
  obtain ⟨tokens, next, hs, hn, ht⟩ := h
  obtain ⟨bytes, he, hb⟩ := consumed_rep hs
  have heq : data.val = bytes := by simpa [hn] using hb.suffix
  exact ⟨tokens, heq.symm ▸ he, ht⟩

/-- `BodyBytes` of a slice's contents gives `Body.BodyEncoding` over the slice. -/
theorem BodyBytes.body {data : Slice U8} {ops}
    (h : BodyBytes ops data.val) : Body.BodyEncoding data ops := by
  obtain ⟨tokens, ht, hb⟩ := h
  exact ⟨tokens, Slice.len data, rep_consumed ht
    ⟨by simp, by simp, by simp⟩, rfl, hb⟩

/-- A code entry parses as `CodeEncoding` when its size, locals and body parse in turn. The framing
proof preserves the exact source span. -/
theorem code_encoding_of_parts {data start content localEnd last size groups body ops}
    (hsize : Binary.Leb128.Decoded data start size content)
    (hlength : last.val = content.val + size.val)
    (hlocals : Binary.At
      (Binary.VecEncoding Binary.LocalEncoding) data content groups localEnd)
    (hbodybytes : Body.Scalar.BytesAt data localEnd body.val last)
    (hbody : Body.BodyEncoding body ops) :
    Binary.At (CodeEncoding) data start ⟨groups, ops⟩ last := by
  obtain ⟨header, hh, hn, hb, he⟩ := hsize
  obtain ⟨localBytes, hl, hls⟩ := hlocals
  have hlen : size.val = localBytes.length + body.val.length := by
    have := hls.length
    have := hbodybytes.length
    omega
  refine ⟨header ++ localBytes ++ body.val,
    ⟨header, localBytes, body.val, ?_, hl, body_encoding_bytes hbody, rfl⟩, ?_⟩
  · simpa [hlen] using he
  · exact ((⟨hh, hn, hb⟩ : Body.Scalar.BytesAt data start header content).append hls).append hbodybytes

/-- `Body.functionContext` is the code entry body context when locals are parameters then declared
locals. -/
theorem function_context_entry {env : metadata.Env} {locals : alloc.vec.Vec wasm_types.ValueType}
    {ft : wasm_types.FuncType} {declared : List wasm_types.ValueType}
    (hl : locals.val = ft.params.val ++ declared) :
    Body.functionContext env locals ft = CodeEntry.bodyContext env ft.params.val declared ft.results.val := by
  simp [Body.functionContext, Body.bodyContext, Translation.Environment.context,
    Body.Control.labelContext, CodeEntry.bodyContext, hl]
  rfl

/-- A typed body with declared references gives `Typed`. -/
theorem Typed.of_body {env locals index ft groups ops}
    (hi : env.types.val[index.val]? = some ft)
    (hl : locals.val = ft.params.val ++ CodeEntry.Locals.declared groups)
    (ht : Body.FunctionTyped env locals ft ops)
    (hdeclared : Spec.DeclaredReferences.Instructions
      (env.declared_funcs.val.map (fun idx => uN.mk_uN idx.val)) ops) :
    Typed env index ⟨groups, ops⟩ := by
  have hlt := List.getElem?_eq_some_iff.mp hi
  refine ⟨hlt.1, ?_, hdeclared⟩
  change Instrs_ok (Body.functionContext env locals ft) ops _ at ht
  rw [function_context_entry hl] at ht
  simpa only [hlt.2, Binary.Code.declared, CodeEntry.Locals.declared,
    CodeEntry.instructionType] using ht

/-- `Typed` and a body encoding give `Body.Validated`. -/
theorem Typed.body {env index entry}
    (h : Typed env index entry) (data : Slice U8)
    (locals : alloc.vec.Vec wasm_types.ValueType)
    (hl : locals.val = (env.types.val[index.val]'h.type_lt).params.val ++ entry.declared)
    (he : Body.BodyEncoding data entry.body) : Body.Validated data env locals index := by
  refine ⟨env.types.val[index.val]'h.type_lt, entry.body,
    List.getElem?_eq_getElem h.type_lt, he, ?_, h.declared⟩
  change Instrs_ok (Body.functionContext env locals _) entry.body _
  rw [function_context_entry hl]
  exact h.typed

end Itasca.CodeEntry

end
