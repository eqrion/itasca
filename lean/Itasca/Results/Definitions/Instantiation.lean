import Itasca.Generated.FunsInstantiate
import Itasca.Results.Definitions.Store.State
import Itasca.Results.Definitions.Compiler.Source

/-!
# Instantiation and publication

Instantiation links an accepted compiled module, initializes its segments, and
returns its start handle without executing it. Read the source outcomes before
the operation law: rejection before publication rolls back; later traps retain
committed effects.
-/

section InstantiationConfiguration

open Itasca.Representation

/-!
## Source start configuration

The module start frame identifies the returned start call before its execution.
-/

namespace Itasca.Integration

open Aeneas Aeneas.Std SpecExt

/-- Module-start execution uses the newly installed module and no ambient locals. -/
def moduleStartFrame {M : Type} (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) : frame :=
  ⟨[], Representation.decodeInstance store inst⟩

end Itasca.Integration

end InstantiationConfiguration

section InstantiationOutcomes

open Itasca.Representation

/-!
## Source instantiation outcomes

Resolved start handles, initialized source states and permitted failures distinguish
rollback before publication from retained initialization effects afterward.
-/

namespace Itasca.Integration

open Aeneas Aeneas.Std Itasca Store SpecExt

/-- The returned start function is the one the module declares, resolved through the new
instance and issued by the store. -/
def StartResolved {M : Type} (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) :
    Option runtime.FuncAddr → Prop
  | none => inst.module.module.env.start = none
  | some address => ∃ index,inst.module.module.env.start=some index ∧ inst.funcs.val[index.val]?=some address ∧
      address.store=store.id ∧ address.index.val<store.funcs.length

/-- Initialization follows the source instantiation configuration: success reaches the call of
the start function, if any, and a trap or resource error is a reachable source configuration. -/
def InitializedSource (initial : config) (store : _root_.store) (ambient : frame) :
    core.result.Result runtime.Instantiated runtime.ExecError → Prop
  | .Ok out => StepsH initial [] ⟨⟨store,ambient⟩,out.start.toList.map (fun address => .CALL_ADDR address.index.val)⟩
  | .Err (.Trap _) => StepsH initial [] ⟨⟨store,ambient⟩,[.TRAP]⟩
  | .Err (.Exhausted _) | .Err .Terminated => ∃ body,StepsH initial [] ⟨⟨store,ambient⟩,body⟩
  | .Err _ => False

/-- A rejection before publication leaves the store unchanged and never reports a trap.
Otherwise the new instance follows the generated source instantiation. -/
def InstantiationSourceOutcome {M P : Type} (view : M → Slice U8)
    (oldCode code : CodeInterpretation) (before : runtime.store.Store M)
    (module : runtime.compiler.ExecutableModule) (imports : Slice runtime.Extern)
    (raw : Binary.Module) (platform : P)
    (result : core.result.Result runtime.Instantiated runtime.ExecError)
    (after : runtime.store.Store M) (host : P) : Prop :=
  (∃ error,result=.Err error ∧ PrecommitError error ∧ after=before ∧ host=platform) ∨
  ∃ inst initial,
    after.instances.val[before.instances.len.val]?=some inst ∧ inst.module=module ∧ host=platform ∧
    fun_instantiate (decodeStore view oldCode before) (Module.Elaboration.moduleOf raw)
      (imports.val.map decodeExternal) initial ∧
    InitializedSource initial (decodeStore view code after) (moduleStartFrame after inst) result ∧
    ∀ instantiated,result=.Ok instantiated →
      instantiated.instance=⟨before.id,before.instances.len⟩ ∧ StartResolved after inst instantiated.start

end Itasca.Integration

end InstantiationOutcomes

namespace Itasca.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Representation Itasca.Store

/-- Actual accepted compilation and public instantiation terminate. The final code
  interpretation installs the module's source functions at the next instance index. The full
  invariant, raw prefix and cross-world source extension use that interpretation.
  `InstantiationSourceOutcome` separates failure before publication, which rolls back, from
  initialization after publication, which reaches the call of the returned start function or a trap.
  The module is also source-typed. -/
def InstantiationLaw {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop) : Prop :=
  ∀ {P F A : Type}
  (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
  (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
  (_memory_laws : Platform.MemoryLaws memory view)
  (_allocator_correct : Platform.AllocCorrect allocator)
  (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
  (imports : Slice runtime.Extern) (platform : P)
  (oldCode : CodeInterpretation) (_store_invariant : Inv oldCode before)
  (_imports_issued : ∀ external ∈ imports.val, ExternalIssued before external)
  (bytes : Slice U8) (limits : runtime.compiler.CompileLimits)
  (_compilation_accepted : runtime.compiler.compile_with allocator bytes limits = .ok (.Ok module))
  (raw : Binary.Module)
  (_source_encoding : Binary.ModuleEncodingWith (CodeEntry.CodeEncoding) raw bytes.val) ,
  Module_ok (Module.Elaboration.moduleOf raw) ∧
    runtime.store.instantiate.Store.instantiate_with memory hooks floats allocator before module imports platform
      ⦃ (result, after, nextPlatform) => Inv (installCode oldCode before.instances.length (Compiler.sourceFunctions raw)) after ∧
        Store.MetadataExtended before after ∧
        Extend_store (decodeStore view oldCode before)
          (decodeStore view (installCode oldCode before.instances.length (Compiler.sourceFunctions raw)) after) ∧
        InstantiationSourceOutcome view oldCode (installCode oldCode before.instances.length (Compiler.sourceFunctions raw))
          before module imports raw platform result after nextPlatform ⦄


end Itasca.Integration
