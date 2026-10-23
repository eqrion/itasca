import Itasca.Module.Code.Encoding
import Itasca.Profile.CodeEntry

/-!
# Resource bounds on module encodings

Strengthens the independent module grammar with the implementation caps that completeness needs:
`CodeEncodingWithinLimits` bounds one code entry, `ModuleEncodingWithinLimits` bounds the whole
encoding and every entry, and `ModuleSignaturesWithinLimits` bounds signature sizes. The caps
are `limits.MAX_*` constants and are separate from language validity. The file also lifts
relation weakening (`.imp`) through the grammar combinators.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

/-- A code entry encoding whose flattened declared locals and instruction bytes stay within
`limits.MAX_LOCALS` and `limits.MAX_FUNCTION_BYTES`. The instruction bytes follow the locals
vector and include the final `end`. The size prefix and locals bytes do not count toward the
body cap. -/
def CodeEncodingWithinLimits (entry : Code) (bytes : List U8) : Prop :=
  entry.declared.length ≤ limits.MAX_LOCALS.val ∧
  ∃ size locals body, Leb128.Encoding size (locals.length + body.length) ∧
    VecEncoding LocalEncoding entry.locals locals ∧ BodyEncoding entry.body body ∧
    body.length ≤ limits.MAX_FUNCTION_BYTES.val ∧ bytes = size ++ locals ++ body

end Itasca.ModuleBinary

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

theorem Rep.imp {α : Type} {R S : α → List U8 → Prop} {values bytes}
    (h : Rep R values bytes) (hs : ∀ value bs, R value bs → S value bs) : Rep S values bytes := by
  induction h with
  | nil => exact .nil
  | cons hp _ ih => exact .cons (hs _ _ hp) ih

theorem VecEncoding.imp {α : Type} {R S : α → List U8 → Prop} {values bytes}
    (h : VecEncoding R values bytes) (hs : ∀ value bs, R value bs → S value bs) :
    VecEncoding S values bytes := by
  obtain ⟨count, entries, hn, he, hb⟩ := h
  exact ⟨count, entries, hn, he.imp hs, hb⟩

theorem PaddedEncoding.imp {α : Type} {R S : α → List U8 → Prop} {id absent value bytes}
    (h : PaddedEncoding id R absent value bytes) (hs : ∀ value bs, R value bs → S value bs) :
    PaddedEncoding id S absent value bytes := by
  obtain ⟨customs, sec, hc, hr, he⟩ := h
  refine ⟨customs, sec, hc, ?_, he⟩
  cases hr with
  | absent => exact .absent
  | present hp =>
    obtain ⟨size, payload, hn, hval, hb⟩ := hp
    exact .present ⟨size, payload, hn, hs _ _ hval, hb⟩

theorem ModuleEncodingWith.imp {profile} {R S : Code → List U8 → Prop} {raw bytes}
    (h : ModuleEncodingWith R raw bytes profile) (hs : ∀ code bs, R code bs → S code bs) :
    ModuleEncodingWith S raw bytes profile := by
  obtain ⟨types, imports, functions, tables, memories, globals, exports, start, elements, dataCount,
    codes, datas, customs, ht, hi, hf, htt, hm, hg, he, hst, hel, hcount, hc, hd, hcs, hb, ha, hv⟩ := h
  exact ⟨types, imports, functions, tables, memories, globals, exports, start, elements, dataCount,
    codes, datas, customs, ht, hi, hf, htt, hm, hg, he, hst, hel, hcount,
    hc.imp (fun _ _ hv => hv.imp hs), hd, hcs, hb, ha, hv⟩

theorem ModuleEncodingWith.guards {profile R raw bytes}
    (h : ModuleEncodingWith R raw bytes profile) :
    ModuleTypesAllowed profile raw ∧ DataCountValid raw := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ha, hc⟩ := h
  exact ⟨ha, hc⟩

/-- A module encoding of at most `limits.MAX_MODULE_BYTES` bytes whose code entries satisfy
`CodeEncodingWithinLimits`. Only the code entries' encoding witnesses are strengthened. Padded
LEB encodings stay admitted, and the caps constrain the actual encoded body bytes. -/
def ModuleEncodingWithinLimits (raw : Module) (bytes : List U8)
    (profile : ValidationProfile := .Wasm1) : Prop :=
  bytes.length ≤ limits.MAX_MODULE_BYTES.val ∧
    ModuleEncodingWith (Profile.CodeEncodingWithinLimits profile) raw bytes profile

/-- Forgetting the caps leaves a `ModuleEncodingWith` the profile's plain code encoding. -/
theorem ModuleEncodingWithinLimits.encoding {profile raw bytes}
    (h : ModuleEncodingWithinLimits raw bytes profile) :
    ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes profile :=
  h.2.imp (fun _ _ hc => hc.encoding)

/-- Every signature in the type section satisfies `Profile.FuncTypeWithinLimits`. This is an
implementation cap on parameters and results, shared by both profiles and required for
completeness only. -/
def ModuleSignaturesWithinLimits (raw : Module) : Prop :=
  ∀ ft ∈ raw.types, Profile.FuncTypeWithinLimits ft

end Itasca.ModuleBinary
