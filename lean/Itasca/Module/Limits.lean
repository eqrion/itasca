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

theorem ModuleEncodingWith.imp {R S : Code → List U8 → Prop} {raw bytes}
    (h : ModuleEncodingWith R raw bytes) (hs : ∀ code bs, R code bs → S code bs) :
    ModuleEncodingWith S raw bytes := by
  obtain ⟨types, imports, functions, tables, memories, globals, exports, start, elements, dataCount,
    codes, datas, customs, ht, hi, hf, htt, hm, hg, he, hst, hel, hcount, hc, hd, hcs, hb, hv⟩ := h
  exact ⟨types, imports, functions, tables, memories, globals, exports, start, elements, dataCount,
    codes, datas, customs, ht, hi, hf, htt, hm, hg, he, hst, hel, hcount,
    hc.imp (fun _ _ hv => hv.imp hs), hd, hcs, hb, hv⟩

theorem ModuleEncodingWith.guards {R raw bytes}
    (h : ModuleEncodingWith R raw bytes) :
    DataCountValid raw := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hc⟩ := h
  exact hc

/-- A module encoding of at most `limits.MAX_MODULE_BYTES` bytes whose code entries satisfy
`CodeEncodingWithinLimits`. Only the code entries' encoding witnesses are strengthened. Padded
LEB encodings stay admitted, and the caps constrain the actual encoded body bytes. -/
def ModuleEncodingWithinLimits (raw : Module) (bytes : List U8) : Prop :=
  bytes.length ≤ limits.MAX_MODULE_BYTES.val ∧
    ModuleEncodingWith (Profile.CodeEncodingWithinLimits) raw bytes

/-- Forgetting the caps leaves a `ModuleEncodingWith` the plain code encoding. -/
theorem ModuleEncodingWithinLimits.encoding {raw bytes}
    (h : ModuleEncodingWithinLimits raw bytes) :
    ModuleEncodingWith (Profile.CodeEncoding) raw bytes :=
  h.2.imp (fun _ _ hc => hc.encoding)

/-- Every signature in the type section satisfies `Profile.FuncTypeWithinLimits`. This is an
implementation cap on parameters and results, required for
completeness only. -/
def ModuleSignaturesWithinLimits (raw : Module) : Prop :=
  ∀ ft ∈ raw.types, Profile.FuncTypeWithinLimits ft

end Itasca.ModuleBinary
