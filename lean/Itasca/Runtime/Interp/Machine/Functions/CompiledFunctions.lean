import Itasca.Runtime.Interp.Relations.CompiledFunctions
import Itasca.Runtime.Compiler.Local.Relations.Function.CoreFunctionContext
import Itasca.Runtime.SourceMachine.Typing
import Itasca.Runtime.Interp.Machine.SuspendedPoint
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredFunction

/-!
Sections, each formerly its own module: Typing, FunctionCode, CompiledFunctions.
-/

/-! ## Typing -/

section

/-!
The completed module context has no ambient function-local declarations.

Main declarations: `moduleSourceContext` and `CoreFunctionTyped`. A direct consumer is `Interp.Machine.Calls.CallLookup`.
-/

namespace Itasca.Runtime.Compiler
/-- The completed module context has no ambient function-local declarations. -/
def moduleSourceContext (module : runtime.compiler.ExecutableModule) : context :=
  {moduleFunctionContext module [] [] with RETURN := none}
end Itasca.Runtime.Compiler
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Source typing uses the exact canonical context retained by the compiler,
not an existential alternative with unrelated global or memory declarations. -/
def CoreFunctionTyped {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (function : runtime.store.FuncInst) : Prop :=
  match function.code with
  | .Host _ => Functype_ok (Store.decodeFunction code store function).TYPE
  | .Wasm instanceIndex functionIndex =>
      ∃ inst index locals body,
        store.instances.val[instanceIndex.val]? = some inst ∧
        code instanceIndex.val inst.module functionIndex.val = .FUNC index locals body ∧
        SourceMachine.ModuleBindings (Store.decodeStore view code store) (Store.decodeInstance store inst)
          (Compiler.moduleSourceContext inst.module) ∧
        Func_ok (Compiler.moduleSourceContext inst.module) (.FUNC index locals body)
          (Store.decodeFunction code store function).TYPE

def CoreFunctionsTyped {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) : Prop :=
  ∀ function ∈ store.funcs.val, CoreFunctionTyped view code store function

theorem CoreFunctionsTyped.functions_typed {M : Type} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {store : runtime.store.Store M}
    (typed : CoreFunctionsTyped view code store) :
    SourceMachine.FunctionsTyped (Store.decodeStore view code store) := by
  intro fn member
  obtain ⟨function, present, rfl⟩ := List.mem_map.mp member
  have body := typed function present
  cases kind : function.code with
  | Host id => simpa only [CoreFunctionTyped, kind, Store.decodeFunction] using body
  | Wasm ii fi =>
    simp only [CoreFunctionTyped, kind] at body
    obtain ⟨inst, index, locals, instructions, found, source, bindings, body⟩ := body
    simp only [Store.decodeFunction, kind, found, source] at body ⊢
    exact ⟨Compiler.moduleSourceContext inst.module, bindings, rfl, rfl, rfl, body⟩
end Itasca.Runtime.Interp

end

/-! ## FunctionCode -/

section

/-!
Function-local emission metadata and complete syntactic compiler evidence.

Main declarations: `FunctionCode`. A direct consumer is `Interp.Machine.Calls.CallStackEntry`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas.Std

/-- Function-local emission metadata and complete syntactic compiler evidence. -/
def FunctionCode (C : context)
    (params declared results : List valtype) (body : List instr)
    (compiled : runtime.bytecode.CompiledFunction) (epilogue : U32) : Prop :=
  C.LOCALS = params ++ declared ∧
  Compiler.StructuredFunctionCode (emission compiled C) C.TYPES C.FUNCS params declared results body compiled epilogue

theorem FunctionCode.entry {C params declared results body compiled epilogue}
    (certificate : FunctionCode C params declared results body compiled epilogue) :
    Compiler.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS results C.LOCALS compiled.code.val compiled.jump_tables.val
      [Compiler.functionRootLabel results compiled epilogue] [] body 0 epilogue.val results := by
  simpa only [certificate.1] using certificate.2.entry
end Itasca.Runtime.Interp.Machine

end

/-! ## CompiledFunctions -/

section

/-!
Concrete function lookup retains the canonical source context for mutable instructions. This is source syntax and layout evidence, independent of any claim about execution or mutable store contents.

Main declarations: `FunctionCompiled` and `CompiledFunctions`. A direct consumer is `Interp.Machine.Calls.CallLookup`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std

/-- Concrete function lookup retains the canonical source context for mutable
instructions. This is source syntax and layout evidence, independent of any
claim about execution or mutable store contents. -/
def FunctionCompiled {M : Type} (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (function : runtime.store.FuncInst) : Prop :=
  ∀ instanceIndex functionIndex, function.code = .Wasm instanceIndex functionIndex →
    ∃ inst compiled signature declared body epilogue,
      store.instances.val[instanceIndex.val]? = some inst ∧
      inst.module.functions.val[functionIndex.val]? = some compiled ∧
      store.types.val[function.signature.val]? = some signature ∧
      code instanceIndex.val inst.module functionIndex.val =
        .FUNC (.mk_uN compiled.type_index.val) (declared.map local.LOCAL) body ∧
      FunctionTable store inst (inst.module.module.env.func_types.val.map Store.decodeFuncType) ∧
      (Store.decodeInstance store inst).TYPES = inst.module.module.env.types.val.map Store.decodeFuncType ∧
      FunctionCode (Compiler.moduleFunctionContext inst.module
        (signature.params.val.map sourceType ++ declared) (signature.results.val.map sourceType))
        (signature.params.val.map sourceType) declared (signature.results.val.map sourceType)
        body compiled epilogue

def CompiledFunctions {M : Type} (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) : Prop :=
  ∀ function ∈ store.funcs.val, FunctionCompiled code store function

theorem declared_types_not_bottom {C params declared results body compiled epilogue}
    (certificate : FunctionCode C params declared results body compiled epilogue) :
    Forall (fun ty => ty ≠ valtype.BOT) declared := by
  intro ty member
  have present : ty ∈ params ++ declared := List.mem_append_right _ member
  rw [← certificate.2.locals] at present
  obtain ⟨rawType, _, rfl⟩ := List.mem_map.mp present
  cases rawType <;> decide
end Itasca.Runtime.Interp.Machine

end
