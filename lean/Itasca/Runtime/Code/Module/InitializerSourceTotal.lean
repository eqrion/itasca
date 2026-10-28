import Itasca.Runtime.Code.Module.InitializerSourceBounds
import Itasca.Runtime.Code.Module.CompileAssembly

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.ModuleBinary

/-- The actual fresh compiler-driver input has enough space for initializer
lowering, directly from the independently encoded module and collected function
count. This covers successful lowering and every normal error result. -/
theorem initializer_lower_source_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (env : Itasca.module.Env) (tail : Itasca.module.Tail)
    (profile : Itasca.ValidationProfile) (functions : alloc.vec.Vec runtime.bytecode.CompiledFunction)
    (budget : runtime.compiler.Budget A) {R raw bytes}
    (encoding : ModuleEncodingWith R raw bytes profile)
    (matched : Itasca.ModuleElaboration.Matches env tail raw)
    (bounded : bytes.length ≤ Itasca.limits.MAX_MODULE_BYTES.val)
    (functionCount : functions.val.length = env.func_type_indices.val.length) :
    runtime.compiler.initialize.lower ops (uninitializedModule env tail profile functions) budget
      ⦃ _ => True ⦄ := by
  obtain ⟨mapSpace, segmentSpace⟩ := initializer_source_headroom encoding matched bounded
  apply initializer_lower_fresh_total ops law _ budget rfl rfl rfl rfl
  · simpa only [uninitializedModule, functionCount] using mapSpace
  · exact segmentSpace

end Itasca.Runtime.Code
