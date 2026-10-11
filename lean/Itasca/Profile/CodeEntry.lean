import Itasca.Profile.BodySpec
import Itasca.MultiValue.BinaryComplete
import Itasca.Module.ModuleCodeContext
import Itasca.Module.ModuleCodeBinary

open Aeneas Aeneas.Std

namespace Itasca.Profile

/-- Independent bytes for the selected instruction grammar. -/
def BodyBytes (profile : ValidationProfile) (ops : List instr) (bytes : List U8) : Prop :=
  match profile with
  | .Wasm1 => ModuleBinary.BodyEncoding ops bytes
  | .Wasm2 => ∃ tokens, ModuleBinary.Rep MultiValue.TokenEncoding tokens bytes ∧
      MultiValue.BodyTokens tokens ops

/-- Entry framing and locals are shared across the supported profiles. -/
def CodeEncoding (profile : ValidationProfile) (entry : ModuleBinary.Code)
    (bytes : List U8) : Prop :=
  ∃ size locals body, Leb128.Encoding size (locals.length + body.length) ∧
    ModuleBinary.VecEncoding ModuleBinary.LocalEncoding entry.locals locals ∧
    BodyBytes profile entry.body body ∧ bytes = size ++ locals ++ body

/-- Completeness bounds constrain declared locals and the exact body bytes;
function parameters and the entry size prefix are counted separately. -/
def CodeEncodingWithinLimits (profile : ValidationProfile) (entry : ModuleBinary.Code)
    (bytes : List U8) : Prop :=
  entry.declared.length ≤ limits.MAX_LOCALS.val ∧
  ∃ size locals body, Leb128.Encoding size (locals.length + body.length) ∧
    ModuleBinary.VecEncoding ModuleBinary.LocalEncoding entry.locals locals ∧
    BodyBytes profile entry.body body ∧ body.length ≤ limits.MAX_FUNCTION_BYTES.val ∧
    bytes = size ++ locals ++ body

theorem CodeEncodingWithinLimits.encoding {profile entry bytes}
    (h : CodeEncodingWithinLimits profile entry bytes) : CodeEncoding profile entry bytes := by
  obtain ⟨_, size, locals, body, hs, hl, hb, _, he⟩ := h
  exact ⟨size, locals, body, hs, hl, hb, he⟩

structure EntryTyped (profile : ValidationProfile) (env : module.Env)
    (typeIdx : U32) (entry : ModuleBinary.Code) : Prop where
  type_lt : typeIdx.val < env.types.val.length
  signature : FuncType profile env.types.val[typeIdx.val]
  typed : Instrs_ok (CodeEntry.bodyContext env env.types.val[typeIdx.val].params.val
    entry.declared env.types.val[typeIdx.val].results.val) entry.body
    (CodeEntry.instructionType env.types.val[typeIdx.val])
  instructions : Instructions profile (CodeEntry.bodyContext env
    env.types.val[typeIdx.val].params.val entry.declared
    env.types.val[typeIdx.val].results.val) entry.body
  locals_allowed : ∀ group ∈ entry.locals, ModuleBinary.ValueTypeAllowed profile group.2
  declared : DeclaredReferences.Instructions
    (env.declared_funcs.val.map (fun idx => uN.mk_uN idx.val)) entry.body

/-- An accepted entry is described entirely by independent binary syntax and
declarative typing, using the original function-index and type-index spaces. -/
def Entry (profile : ValidationProfile) (data : Slice U8) (env : module.Env)
    (index start finish : Usize) : Prop :=
  ∃ entry, ModuleBinary.At (CodeEncoding profile) data start entry finish ∧
    ∃ hi : index.val < env.func_type_indices.val.length,
      EntryTyped profile env env.func_type_indices.val[index.val] entry ∧
      entry.declared.length ≤ limits.MAX_LOCALS.val

theorem multiValue_consumed_rep {data start tokens next}
    (h : MultiValue.Consumed data start tokens next) :
    ModuleBinary.At (ModuleBinary.Rep MultiValue.TokenEncoding) data start tokens next := by
  induction h with
  | nil hb => exact ⟨[], .nil, Wasm.BytesAt.nil _ _ hb⟩
  | snoc _ ht ih =>
    obtain ⟨bs, he, hs⟩ := ih
    obtain ⟨cs, hc, hp⟩ := ht
    exact ⟨bs ++ cs, he.snoc hc, hs.append hp⟩

theorem multiValue_rep_consumed {data start next tokens bytes}
    (he : ModuleBinary.Rep MultiValue.TokenEncoding tokens bytes)
    (hs : Wasm.BytesAt data start bytes next) : MultiValue.Consumed data start tokens next := by
  induction he generalizing start with
  | nil =>
    have hn := hs.empty
    subst next
    exact .nil _ hs.bound
  | cons ht _ ih =>
    obtain ⟨middle, hfirst, hrest⟩ := hs.split
    exact MultiValue.Consumed.cons_iff.mpr ⟨middle, ⟨_, ht, hfirst⟩, ih hrest⟩

theorem BodyEncoding.bytes {profile data ops} (h : BodyEncoding profile data ops) :
    BodyBytes profile ops data.val := by
  cases profile with
  | Wasm1 => exact ModuleBinary.bodyEncoding_of_body h
  | Wasm2 =>
    obtain ⟨tokens, next, hs, hn, ht⟩ := h
    obtain ⟨bytes, he, hb⟩ := multiValue_consumed_rep hs
    have heq : data.val = bytes := by simpa [hn] using hb.suffix
    exact ⟨tokens, heq.symm ▸ he, ht⟩

theorem BodyBytes.body {profile} {data : Slice U8} {ops}
    (h : BodyBytes profile ops data.val) : BodyEncoding profile data ops := by
  cases profile with
  | Wasm1 => exact ModuleBinary.body_of_bodyEncoding h
  | Wasm2 =>
    obtain ⟨tokens, ht, hb⟩ := h
    exact ⟨tokens, Slice.len data, multiValue_rep_consumed ht
      ⟨by simp, by simp, by simp⟩, rfl, hb⟩

/-- Framing is proved once; only the independent body grammar is selected by
the profile. -/
theorem codeEncoding_of_parts {profile data start content localEnd last size groups body ops}
    (hsize : Leb128.Decoded data start size content)
    (hlength : last.val = content.val + size.val)
    (hlocals : ModuleBinary.At
      (ModuleBinary.VecEncoding ModuleBinary.LocalEncoding) data content groups localEnd)
    (hbodybytes : Wasm.BytesAt data localEnd body.val last)
    (hbody : BodyEncoding profile body ops) :
    ModuleBinary.At (CodeEncoding profile) data start ⟨groups, ops⟩ last := by
  obtain ⟨header, hh, hn, hb, he⟩ := hsize
  obtain ⟨localBytes, hl, hls⟩ := hlocals
  have hlen : size.val = localBytes.length + body.val.length := by
    have := hls.length
    have := hbodybytes.length
    omega
  refine ⟨header ++ localBytes ++ body.val,
    ⟨header, localBytes, body.val, ?_, hl, hbody.bytes, rfl⟩, ?_⟩
  · simpa [hlen] using he
  · exact ((⟨hh, hn, hb⟩ : Wasm.BytesAt data start header content).append hls).append hbodybytes

theorem functionContext_entry {env : module.Env} {locals : alloc.vec.Vec types.ValueType}
    {ft : types.FuncType} {declared : List types.ValueType}
    (hl : locals.val = ft.params.val ++ declared) :
    functionContext env locals ft = CodeEntry.bodyContext env ft.params.val declared ft.results.val := by
  simp [functionContext, MultiValue.bodyContext, EnvTranslation.context,
    Control.labelContext, CodeEntry.bodyContext, hl]
  rfl

theorem EntryTyped.of_body {profile env locals index ft groups ops}
    (hi : env.types.val[index.val]? = some ft) (hs : FuncType profile ft)
    (hl : locals.val = ft.params.val ++ ModuleLocals.declared groups)
    (ht : MultiValue.FunctionTyped env locals ft ops)
    (hp : Instructions profile (functionContext env locals ft) ops)
    (hallowed : ∀ group ∈ groups, ModuleBinary.ValueTypeAllowed profile group.2)
    (hdeclared : DeclaredReferences.Instructions
      (env.declared_funcs.val.map (fun idx => uN.mk_uN idx.val)) ops) :
    EntryTyped profile env index ⟨groups, ops⟩ := by
  have hlt := List.getElem?_eq_some_iff.mp hi
  refine ⟨hlt.1, ?_, ?_, ?_, hallowed, hdeclared⟩
  · simpa [hlt.2] using hs
  · change Instrs_ok (functionContext env locals ft) ops _ at ht
    rw [functionContext_entry hl] at ht
    simpa only [hlt.2, ModuleBinary.Code.declared, ModuleLocals.declared,
      CodeEntry.instructionType] using ht
  · rw [functionContext_entry hl] at hp
    simpa only [hlt.2, ModuleBinary.Code.declared, ModuleLocals.declared] using hp

theorem EntryTyped.body {profile env index entry}
    (h : EntryTyped profile env index entry) (data : Slice U8)
    (locals : alloc.vec.Vec types.ValueType)
    (hl : locals.val = (env.types.val[index.val]'h.type_lt).params.val ++ entry.declared)
    (he : BodyEncoding profile data entry.body) : Body profile data env locals index := by
  refine ⟨env.types.val[index.val]'h.type_lt, entry.body,
    List.getElem?_eq_getElem h.type_lt, h.signature, he, ?_, ?_, h.declared⟩
  · change Instrs_ok (functionContext env locals _) entry.body _
    rw [functionContext_entry hl]
    exact h.typed
  · rw [functionContext_entry hl]
    exact h.instructions

/-- Generated function typing uses a single proof for every profile. -/
theorem EntryTyped.func_ok {profile env typeIdx entry}
    (h : EntryTyped profile env typeIdx entry) (C : context)
    (hc : CodeEntry.ModuleContext env C) (hsegments : CodeEntry.SegmentContext env C) :
    Func_ok C (CodeEntry.function typeIdx entry)
      (EnvTranslation.funcType (env.types.val[typeIdx.val]'h.type_lt)) :=
  CodeEntry.typed_func_ok h.type_lt h.typed C hc hsegments

/-- Shared module composition needs the typing and instruction-profile facts;
the signature restriction is retained separately by the entry certificate. -/
theorem EntryTyped.core {profile env typeIdx entry} (h : EntryTyped profile env typeIdx entry) :
    CodeEntry.Typed env typeIdx entry profile := ⟨h.type_lt, h.typed, h.instructions, h.locals_allowed, h.declared⟩

theorem EntryTyped.of_core {profile env typeIdx entry} (h : CodeEntry.Typed env typeIdx entry profile)
    (hs : FuncType profile (env.types.val[typeIdx.val]'h.type_lt)) : EntryTyped profile env typeIdx entry :=
  ⟨h.type_lt, hs, h.typed, h.profile, h.locals_allowed, h.declared⟩

theorem EntryTyped.wasm1 {env typeIdx entry} (h : EntryTyped .Wasm1 env typeIdx entry) :
    CodeEntry.Typed env typeIdx entry := ⟨h.type_lt, h.typed, h.instructions, h.locals_allowed, h.declared⟩

theorem EntryTyped.of_wasm1 {env typeIdx entry} (h : CodeEntry.Typed env typeIdx entry)
    (hs : FuncType .Wasm1 (env.types.val[typeIdx.val]'h.type_lt)) : EntryTyped .Wasm1 env typeIdx entry :=
  ⟨h.type_lt, hs, h.typed, h.profile, h.locals_allowed, h.declared⟩

end Itasca.Profile
