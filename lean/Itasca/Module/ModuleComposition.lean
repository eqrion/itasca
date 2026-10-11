import Itasca.Module.ModuleDeclarations
import Itasca.Module.ModuleTail

open Aeneas Aeneas.Std

namespace Itasca.ModuleComposition

open ModuleBinary

theorem padded_prepend_custom {α : Type} {id : U8} {R : α → List U8 → Prop}
    {absent value before bytes} (hc : CustomsEncoding before)
    (hp : PaddedEncoding id R absent value bytes) :
    PaddedEncoding id R absent value (before ++ bytes) := by
  obtain ⟨customs, payload, hcustoms, hsection, he⟩ := hp
  exact ⟨before ++ customs, payload, ModuleTail.customs_append hc hcustoms,
    hsection, by simp [he, List.append_assoc]⟩

/-- The three independent byte grammars compose into exactly one module. -/
theorem encoding {profile : ValidationProfile} {codeRel : Code → List U8 → Prop} {decls : ModuleEnv.Declarations} {codes segments before codeBytes tailBytes}
    (henv : ModuleEnv.PrefixEncoding decls before profile)
    (hcode : PaddedEncoding 10#u8 (VecEncoding codeRel) [] codes codeBytes)
    (htail : ModuleTail.Encoding segments tailBytes profile)
    (hallowed : ModuleTypesAllowed profile (decls.module codes segments))
    (hcount : DataCountValid (decls.module codes segments)) :
    ModuleEncodingWith codeRel (decls.module codes segments) (before ++ codeBytes ++ tailBytes) profile := by
  obtain ⟨types, imports, functions, tables, memories, globals, exports, start,
    elements, dataCount, customs, htypes, himports, hfunctions, htables, hmemories, hglobals,
    hexports, hstart, helements, hdataCount, hcustoms, he, _⟩ := henv
  obtain ⟨datas, trailing, hdatas, htrailing, ht⟩ := htail
  refine ⟨types, imports, functions, tables, memories, globals, exports, start,
    elements, dataCount, customs ++ codeBytes, datas, trailing, htypes, himports, hfunctions,
    htables, hmemories, hglobals, hexports, hstart, helements, hdataCount,
    padded_prepend_custom hcustoms hcode, hdatas, htrailing, ?_, hallowed, hcount⟩
  simp only [he, ht, List.append_assoc]

/-- Exact adjacent spans plus the tail's EOF guarantee reconstruct the input. -/
theorem whole_bytes {profile : ValidationProfile} {codeRel : Code → List U8 → Prop} {data : Slice U8} {codePos tailPos decls codes segments}
    (henv : At (fun decls bytes => ModuleEnv.PrefixEncoding decls bytes profile) data 0#usize decls codePos)
    (hcode : At (PaddedEncoding 10#u8 (VecEncoding codeRel) []) data codePos codes tailPos)
    (htail : At (fun segments bytes => ModuleTail.Encoding segments bytes profile) data tailPos segments (Slice.len data))
    (hallowed : ModuleTypesAllowed profile (decls.module codes segments))
    (hcount : DataCountValid (decls.module codes segments)) :
    ModuleEncodingWith codeRel (decls.module codes segments) data.val profile := by
  obtain ⟨before, he, hs⟩ := henv
  obtain ⟨codeBytes, hc, hcs⟩ := hcode
  obtain ⟨tailBytes, ht, hts⟩ := htail
  have hspan := (hs.append hcs).append hts
  have hbytes : data.val = before ++ codeBytes ++ tailBytes := by
    simpa using hspan.suffix
  rw [hbytes]
  exact encoding he hc ht hallowed hcount

end Itasca.ModuleComposition
