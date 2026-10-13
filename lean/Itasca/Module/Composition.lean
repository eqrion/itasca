import Itasca.Module.Env.Declarations
import Itasca.Module.Sections.Tail

/-!
# Composing the module regions

Joins the three independent byte regions (environment prefix, code section, tail) into one
`ModuleEncodingWith`. `encoding` works on byte lists and `whole_bytes` on adjacent spans of the
input slice, using the tail's end-of-input guarantee. Custom sections before the code section
are absorbed into the code section's padding.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleComposition

open ModuleBinary

/-- Custom sections can be prepended to a padded section. -/
theorem padded_prepend_custom {α : Type} {id : U8} {R : α → List U8 → Prop}
    {absent value before bytes} (hc : CustomsEncoding before)
    (hp : PaddedEncoding id R absent value bytes) :
    PaddedEncoding id R absent value (before ++ bytes) := by
  obtain ⟨customs, payload, hcustoms, hsection, he⟩ := hp
  exact ⟨before ++ customs, payload, ModuleTail.customs_append hc hcustoms,
    hsection, by simp [he, List.append_assoc]⟩

/-- The environment prefix, code section and tail encodings compose into one module encoding of
`before ++ codeBytes ++ tailBytes`. -/
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

/-- Adjacent spans for the environment, code section and tail, with the tail ending at EOF,
make the input exactly one module encoding. -/
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
