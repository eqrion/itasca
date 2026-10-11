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
theorem encoding {decls : ModuleEnv.Declarations} {codes segments before codeBytes tailBytes}
    (henv : ModuleEnv.PrefixEncoding decls before)
    (hcode : PaddedEncoding 10#u8 (VecEncoding CodeEncoding) [] codes codeBytes)
    (htail : ModuleTail.Encoding segments tailBytes) :
    ModuleEncoding (decls.module codes segments) (before ++ codeBytes ++ tailBytes) := by
  obtain ⟨types, imports, functions, tables, memories, globals, exports, start,
    elements, customs, htypes, himports, hfunctions, htables, hmemories, hglobals,
    hexports, hstart, helements, hcustoms, he⟩ := henv
  obtain ⟨datas, trailing, hdatas, htrailing, ht⟩ := htail
  refine ⟨types, imports, functions, tables, memories, globals, exports, start,
    elements, customs ++ codeBytes, datas, trailing, htypes, himports, hfunctions,
    htables, hmemories, hglobals, hexports, hstart, helements,
    padded_prepend_custom hcustoms hcode, hdatas, htrailing, ?_⟩
  simp only [he, ht, List.append_assoc]

/-- Exact adjacent spans plus the tail's EOF guarantee reconstruct the input. -/
theorem whole_bytes {data : Slice U8} {codePos tailPos decls codes segments}
    (henv : At ModuleEnv.PrefixEncoding data 0#usize decls codePos)
    (hcode : At (PaddedEncoding 10#u8 (VecEncoding CodeEncoding) []) data codePos codes tailPos)
    (htail : At ModuleTail.Encoding data tailPos segments (Slice.len data)) :
    ModuleEncoding (decls.module codes segments) data.val := by
  obtain ⟨before, he, hs⟩ := henv
  obtain ⟨codeBytes, hc, hcs⟩ := hcode
  obtain ⟨tailBytes, ht, hts⟩ := htail
  have hspan := (hs.append hcs).append hts
  have hbytes : data.val = before ++ codeBytes ++ tailBytes := by
    simpa using hspan.suffix
  rw [hbytes]
  exact encoding he hc ht

end Itasca.ModuleComposition
