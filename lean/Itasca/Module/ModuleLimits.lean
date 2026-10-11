import Itasca.Module.ModuleCodeLimits
import Itasca.Profile.CodeEntry

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

/-- This strengthens only the code entries' exact encoding witnesses. It
retains padded LEB encodings and constrains the actual encoded body bytes. -/
def ModuleEncodingWithinLimits (raw : Module) (bytes : List U8)
    (profile : ValidationProfile := .Wasm1) : Prop :=
  bytes.length ≤ limits.MAX_MODULE_BYTES.val ∧
    ModuleEncodingWith (Profile.CodeEncodingWithinLimits profile) raw bytes profile

theorem ModuleEncodingWithinLimits.encoding {profile raw bytes}
    (h : ModuleEncodingWithinLimits raw bytes profile) :
    ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes profile :=
  h.2.imp (fun _ _ hc => hc.encoding)

/-- Signature allocation caps are explicit completeness conditions rather than
language restrictions; Wasm 1.0 keeps its existing unbounded parameter behavior. -/
def ModuleSignaturesWithinLimits (raw : Module) (profile : ValidationProfile) : Prop :=
  ∀ ft ∈ raw.types, Profile.FuncTypeWithinLimits profile ft

end Itasca.ModuleBinary
