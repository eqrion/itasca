import Itasca.Module.ModuleCodeLimits

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
  obtain ⟨types, imports, functions, tables, memories, globals, exports, start, elements,
    codes, datas, customs, ht, hi, hf, htt, hm, hg, he, hst, hel, hc, hd, hcs, hb⟩ := h
  exact ⟨types, imports, functions, tables, memories, globals, exports, start, elements,
    codes, datas, customs, ht, hi, hf, htt, hm, hg, he, hst, hel,
    hc.imp (fun _ _ hv => hv.imp hs), hd, hcs, hb⟩

/-- This strengthens only the code entries' exact encoding witnesses. It
retains padded LEB encodings and constrains the actual encoded body bytes. -/
def ModuleEncodingWithinLimits (raw : Module) (bytes : List U8) : Prop :=
  bytes.length ≤ limits.MAX_MODULE_BYTES.val ∧
    ModuleEncodingWith CodeEncodingWithinLimits raw bytes

theorem ModuleEncodingWithinLimits.encoding {raw bytes} (h : ModuleEncodingWithinLimits raw bytes) :
    ModuleEncoding raw bytes := h.2.imp (fun _ _ hc => hc.encoding)

end Itasca.ModuleBinary
