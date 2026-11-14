import Itasca.Profile.Types
import Itasca.Wasm2.LoopDispatch
import Itasca.Binary.Wasm2.SyntaxUnique
import Itasca.Module.Code.Encoding

/-!
Sections, each formerly its own module: BodySpec, CodeEntry.
-/

/-! ## BodySpec -/

section

/-!
# Function-body grammar

`BodyEncoding` describes exact Wasm 2.0 body bytes. The shared semantic
certificate is `Wasm2.Validated`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Profile

/-- The grammar relates the exact body bytes, including the final `end`, to the
instruction tree `ops`. It does not execute the validator or impose implementation limits. -/
def BodyEncoding (data : Slice U8) (ops : List instr) : Prop :=
  Wasm2.BodyEncoding data ops

end Itasca.Profile

end

/-! ## CodeEntry -/

section

/-!
# Code entries

Specification of a code entry: `CodeEncoding` (size prefix, local declarations
and `BodyBytes`), `EntryTyped` (declarative typing and declared references)
and `Entry`, which combines them for the entry an accepted validation run describes. Also relates
the Wasm 2.0 token consumption to `ModuleBinary.Rep`, and `EntryTyped` to `CodeEntry.Typed`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Profile

/-- The bytes of a body for the Wasm 2.0 instruction grammar. -/
def BodyBytes (ops : List instr) (bytes : List U8) : Prop :=
  ∃ tokens, ModuleBinary.Rep Wasm2.TokenEncoding tokens bytes ∧
    Wasm2.BodyTokens tokens ops

/-- The bytes of a code entry: size prefix, local declarations and body. The body grammar
is the Wasm 2.0 grammar. -/
def CodeEncoding (entry : ModuleBinary.Code)
    (bytes : List U8) : Prop :=
  ∃ size locals body, Leb128.Encoding size (locals.length + body.length) ∧
    ModuleBinary.VecEncoding ModuleBinary.LocalEncoding entry.locals locals ∧
    BodyBytes entry.body body ∧ bytes = size ++ locals ++ body

/-- `CodeEncoding` with bounds on the declared locals and the body bytes. Function parameters and
the size prefix are not counted. -/
def CodeEncodingWithinLimits (entry : ModuleBinary.Code)
    (bytes : List U8) : Prop :=
  entry.declared.length ≤ limits.MAX_LOCALS.val ∧
  ∃ size locals body, Leb128.Encoding size (locals.length + body.length) ∧
    ModuleBinary.VecEncoding ModuleBinary.LocalEncoding entry.locals locals ∧
    BodyBytes entry.body body ∧ body.length ≤ limits.MAX_FUNCTION_BYTES.val ∧
    bytes = size ++ locals ++ body

/-- A bounded code entry encoding is a code entry encoding. -/
theorem CodeEncodingWithinLimits.encoding {entry bytes}
    (h : CodeEncodingWithinLimits entry bytes) : CodeEncoding entry bytes := by
  obtain ⟨_, size, locals, body, hs, hl, hb, _, he⟩ := h
  exact ⟨size, locals, body, hs, hl, hb, he⟩

/-- The typing facts about a code entry under the type at `typeIdx`: the
body is typed and references are declared. -/
structure EntryTyped (env : metadata.Env)
    (typeIdx : U32) (entry : ModuleBinary.Code) : Prop where
  type_lt : typeIdx.val < env.types.val.length
  typed : Instrs_ok (CodeEntry.bodyContext env env.types.val[typeIdx.val].params.val
    entry.declared env.types.val[typeIdx.val].results.val) entry.body
    (CodeEntry.instructionType env.types.val[typeIdx.val])
  declared : DeclaredReferences.Instructions
    (env.declared_funcs.val.map (fun idx => uN.mk_uN idx.val)) entry.body

/-- The specification of the code entry for function `index` between byte offsets `start` and
`finish`: it parses as a `CodeEncoding`, satisfies `EntryTyped` against the function's type, and
stays within the local limit. -/
def Entry (data : Slice U8) (env : metadata.Env)
    (index start finish : Usize) : Prop :=
  ∃ entry, ModuleBinary.At (CodeEncoding) data start entry finish ∧
    ∃ hi : index.val < env.func_type_indices.val.length,
      EntryTyped env env.func_type_indices.val[index.val] entry ∧
      entry.declared.length ≤ limits.MAX_LOCALS.val

/-- Wasm 2.0 tokens consumed from `data` form a `Rep` of `TokenEncoding` over the same span. -/
theorem wasm2_consumed_rep {data start tokens next}
    (h : Wasm2.Consumed data start tokens next) :
    ModuleBinary.At (ModuleBinary.Rep Wasm2.TokenEncoding) data start tokens next := by
  induction h with
  | nil hb => exact ⟨[], .nil, Wasm1.BytesAt.nil _ _ hb⟩
  | snoc _ ht ih =>
    obtain ⟨bs, he, hs⟩ := ih
    obtain ⟨cs, hc, hp⟩ := ht
    exact ⟨bs ++ cs, he.snoc hc, hs.append hp⟩

/-- A `Rep` of `TokenEncoding` over a span of `data` is consumed as Wasm 2.0 tokens. -/
theorem wasm2_rep_consumed {data start next tokens bytes}
    (he : ModuleBinary.Rep Wasm2.TokenEncoding tokens bytes)
    (hs : Wasm1.BytesAt data start bytes next) : Wasm2.Consumed data start tokens next := by
  induction he generalizing start with
  | nil =>
    have hn := hs.empty
    subst next
    exact .nil _ hs.bound
  | cons ht _ ih =>
    obtain ⟨middle, hfirst, hrest⟩ := hs.split
    exact Wasm2.Consumed.cons_iff.mpr ⟨middle, ⟨_, ht, hfirst⟩, ih hrest⟩

/-- `BodyEncoding` over a slice gives `BodyBytes` of its contents. -/
theorem BodyEncoding.bytes {data ops} (h : BodyEncoding data ops) :
    BodyBytes ops data.val := by
  obtain ⟨tokens, next, hs, hn, ht⟩ := h
  obtain ⟨bytes, he, hb⟩ := wasm2_consumed_rep hs
  have heq : data.val = bytes := by simpa [hn] using hb.suffix
  exact ⟨tokens, heq.symm ▸ he, ht⟩

/-- `BodyBytes` of a slice's contents gives `BodyEncoding` over the slice. -/
theorem BodyBytes.body {data : Slice U8} {ops}
    (h : BodyBytes ops data.val) : BodyEncoding data ops := by
  obtain ⟨tokens, ht, hb⟩ := h
  exact ⟨tokens, Slice.len data, wasm2_rep_consumed ht
    ⟨by simp, by simp, by simp⟩, rfl, hb⟩

/-- A code entry parses as `CodeEncoding` when its size, locals and body parse in turn. The framing
proof preserves the exact source span. -/
theorem codeEncoding_of_parts {data start content localEnd last size groups body ops}
    (hsize : Leb128.Decoded data start size content)
    (hlength : last.val = content.val + size.val)
    (hlocals : ModuleBinary.At
      (ModuleBinary.VecEncoding ModuleBinary.LocalEncoding) data content groups localEnd)
    (hbodybytes : Wasm1.BytesAt data localEnd body.val last)
    (hbody : BodyEncoding body ops) :
    ModuleBinary.At (CodeEncoding) data start ⟨groups, ops⟩ last := by
  obtain ⟨header, hh, hn, hb, he⟩ := hsize
  obtain ⟨localBytes, hl, hls⟩ := hlocals
  have hlen : size.val = localBytes.length + body.val.length := by
    have := hls.length
    have := hbodybytes.length
    omega
  refine ⟨header ++ localBytes ++ body.val,
    ⟨header, localBytes, body.val, ?_, hl, hbody.bytes, rfl⟩, ?_⟩
  · simpa [hlen] using he
  · exact ((⟨hh, hn, hb⟩ : Wasm1.BytesAt data start header content).append hls).append hbodybytes

/-- `Wasm2.functionContext` is the code entry body context when locals are parameters then declared
locals. -/
theorem functionContext_entry {env : metadata.Env} {locals : alloc.vec.Vec wasm_types.ValueType}
    {ft : wasm_types.FuncType} {declared : List wasm_types.ValueType}
    (hl : locals.val = ft.params.val ++ declared) :
    Wasm2.functionContext env locals ft = CodeEntry.bodyContext env ft.params.val declared ft.results.val := by
  simp [Wasm2.functionContext, Wasm2.bodyContext, EnvTranslation.context,
    Control.labelContext, CodeEntry.bodyContext, hl]
  rfl

/-- A typed body with declared references gives `EntryTyped`. -/
theorem EntryTyped.of_body {env locals index ft groups ops}
    (hi : env.types.val[index.val]? = some ft)
    (hl : locals.val = ft.params.val ++ ModuleLocals.declared groups)
    (ht : Wasm2.FunctionTyped env locals ft ops)
    (hdeclared : DeclaredReferences.Instructions
      (env.declared_funcs.val.map (fun idx => uN.mk_uN idx.val)) ops) :
    EntryTyped env index ⟨groups, ops⟩ := by
  have hlt := List.getElem?_eq_some_iff.mp hi
  refine ⟨hlt.1, ?_, hdeclared⟩
  change Instrs_ok (Wasm2.functionContext env locals ft) ops _ at ht
  rw [functionContext_entry hl] at ht
  simpa only [hlt.2, ModuleBinary.Code.declared, ModuleLocals.declared,
    CodeEntry.instructionType] using ht

/-- `EntryTyped` and a body encoding give `Wasm2.Validated`. -/
theorem EntryTyped.body {env index entry}
    (h : EntryTyped env index entry) (data : Slice U8)
    (locals : alloc.vec.Vec wasm_types.ValueType)
    (hl : locals.val = (env.types.val[index.val]'h.type_lt).params.val ++ entry.declared)
    (he : BodyEncoding data entry.body) : Wasm2.Validated data env locals index := by
  refine ⟨env.types.val[index.val]'h.type_lt, entry.body,
    List.getElem?_eq_getElem h.type_lt, he, ?_, h.declared⟩
  change Instrs_ok (Wasm2.functionContext env locals _) entry.body _
  rw [functionContext_entry hl]
  exact h.typed

/-- `EntryTyped` gives `CodeEntry.Typed`. -/
theorem EntryTyped.core {env typeIdx entry} (h : EntryTyped env typeIdx entry) :
    CodeEntry.Typed env typeIdx entry := ⟨h.type_lt, h.typed, h.declared⟩

/-- `CodeEntry.Typed` gives `EntryTyped`. -/
theorem EntryTyped.of_core {env typeIdx entry} (h : CodeEntry.Typed env typeIdx entry) : EntryTyped env typeIdx entry :=
  ⟨h.type_lt, h.typed, h.declared⟩

end Itasca.Profile

end
