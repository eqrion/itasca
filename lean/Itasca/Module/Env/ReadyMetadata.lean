import Itasca.Module.Env.ReadyContexts

open Aeneas Aeneas.Std

namespace Itasca.ModuleEnv

/-- A fully decoded declaration prefix and exact data realization preserve every
returned field of the independent module, including the merged index spaces. -/
theorem Ready.matches {raw : ModuleBinary.Module} {decls : Declarations} {env : module.Env}
    (h : Ready raw 10 decls env) (tail : module.Tail)
    (htail : tail.data.val.map ModuleData.raw = raw.data) :
    ModuleElaboration.Matches env tail raw := by
  have hr := h.represents
  have ht := h.types (by decide)
  have hi := h.imports (by decide)
  have hf := h.functions (by decide)
  have hta := h.tables (by decide)
  have hm := h.memories (by decide)
  have hg := h.globals (by decide)
  have he := h.exports (by decide)
  have hs := h.start (by decide)
  have hel := h.elements (by decide)
  have hdc := h.dataCount (by decide)
  refine ⟨?_, by simpa [hta, hm] using hr.cache⟩
  cases raw
  simp_all [ModuleElaboration.fromEnv, hr.types, hr.imports, hr.functions, hr.globals,
      hr.exports, hr.start, hr.elements, hr.dataCount]

end Itasca.ModuleEnv
