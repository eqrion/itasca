import Itasca.Runtime.SourceMachine.Definitions
import Itasca.Results.Definitions.Host
import Itasca.Runtime.Compiler.Body.Definitions

open WebAssembly


section InterpCallSites

/-!
### Source call sites

Suspended source slot requirements and `SourceCallSite` retain the selected
caller/callee boundary used by resource causes.
-/

namespace Itasca.Interp

open Aeneas Aeneas.Std

/-- Storage retained by suspended source callers. Arguments passed to the
callee have already been removed from these operand lists. -/
def suspendedSourceWords : List SourceMachine.AFrame → Nat
  | [] => 0
  | f :: rest => Representation.slots ((f.locals ++ f.vals).map Representation.valueType) + suspendedSourceWords rest

/-- A reachable source call identifies its callee and shared argument position.
This predicate uses only source configurations, values, and addresses. -/
def SourceCallSite (initial : SourceMachine.AState) (address : funcaddr) (base : Nat) : Prop :=
  ∃ (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
      (target : Nat) (after : List instr) (front args : List val) (callee : funcinst)
      (params results : List valtype) (count : Nat),
    Spec.StepsHN count (SourceMachine.decode initial) [] (SourceMachine.decode ⟨initial.store, initial.ambient,
      {f with code := .CALL (.mk_uN target) :: after, vals := front ++ args} :: rest, []⟩) ∧
    f.module.FUNCS[target]? = some address ∧
    initial.store.FUNCS[address]? = some callee ∧
    callee.TYPE = .mk_functype (.mk_list params) (.mk_list results) ∧
    args.map Representation.valueType = params ∧
    base = suspendedSourceWords rest + Representation.slots ((f.locals ++ front).map Representation.valueType)

end Itasca.Interp

end InterpCallSites

section InterpResources

open Itasca.Representation

/-!
### Source invocation capacities

Source capacity environments, canonical function capacities and direct/indirect
invocation sites describe source-only frame and allocation demand.
-/

namespace Itasca.Interp

open Aeneas Aeneas.Std

/-- The type and function tables used by the integer/control trace match the
source module and its issued function signatures. The selected signature also
matches the source function itself; no compiled slot counter appears here. -/
structure SourceCapacityEnvironment (store : WebAssembly.store) (function : funcinst)
    (env : Itasca.metadata.Env) (typeIndex : U32) : Prop where
  types : function.MODULE.TYPES = env.types.val.map Itasca.Translation.Environment.funcType
  functions : Representation.FunctionsMatch store function.MODULE (env.func_types.val.map Itasca.Translation.Environment.funcType)
  signature : ∃ signature, env.types.val[typeIndex.val]? = some signature ∧
    function.TYPE = Itasca.Translation.Environment.funcType signature

/-- The complete source module namespace. The data namespace is completed
from the parsed module tail, as in the canonical function-typing certificate. -/
def sourceCapacityContext (env : Itasca.metadata.Env) (dataCount : Nat) : context :=
  { Compiler.sourceFunctionContext env [] [] with
    DATAS := List.replicate dataCount datatype.OK, RETURN := none }

/-- A source frame requirement whose complete validation environment is tied
by semantic bindings to the actual source instance. The function is typed in
that same context. No compiled slot counter appears in this definition. -/
def SourceCanonicalFunctionCapacity (store : WebAssembly.store) (address : funcaddr) (words : Nat) : Prop :=
  ∃ (function : funcinst) (env : Itasca.metadata.Env)
      (typeIndex : U32) (dataCount : Nat),
    store.FUNCS[address]? = some function ∧
    SourceCapacityEnvironment store function env typeIndex ∧
    SourceMachine.ModuleBindings store function.MODULE (sourceCapacityContext env dataCount) ∧
    (∃ index locals body, function.CODE = .FUNC index locals body ∧
      Func_ok (sourceCapacityContext env dataCount) (.FUNC index locals body) function.TYPE) ∧
    Representation.SourceFrameCapacity env typeIndex function.CODE words

/-- An indirect source call retains the selected callee and the shared
argument position, including storage suspended in all source callers. -/
def SourceIndirectCallSite (initial : SourceMachine.AState) (address : funcaddr) (base : Nat) : Prop :=
  ∃ (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (table type position : Nat) (after : List instr)
    (front args : List val) (callee : funcinst) (params results : List valtype) (count : Nat),
    Spec.StepsHN count (SourceMachine.decode initial) [] (SourceMachine.decode ⟨initial.store,initial.ambient,
      {f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩) ∧
    f.vals=(front++args)++[SourceMachine.integerVal .I32 position] ∧ position<2^32 ∧
    SourceMachine.Indirect.resolve initial.store f table type position=some address ∧
    initial.store.FUNCS[address]?=some callee ∧
    callee.TYPE=⟨.mk_list params,.mk_list results⟩ ∧ args.map Representation.valueType=params ∧
    base=suspendedSourceWords rest+Representation.slots ((f.locals++front).map Representation.valueType)

/-- A selected call may be direct or table-resolved; either witness is purely
source-level and fixes the shared argument base. -/
def SourceInvocationSite (source : SourceMachine.AState) (address : funcaddr) (base : Nat) : Prop :=
  SourceCallSite source address base ∨ SourceIndirectCallSite source address base

def SourceInvocationAllocation {A : Type} (allocator : runtime.platform.Alloc A)
    (source : SourceMachine.AState) : Prop :=
  ∃ address base words, SourceInvocationSite source address base ∧
    SourceCanonicalFunctionCapacity source.store address words ∧
    ((∃ (slots : alloc.vec.Vec U64) (n : Usize), n.val ≤ base+words ∧
      allocator.reserve slots n=.ok (false,slots)) ∨
      ∃ frames : alloc.vec.Vec runtime.interp.Frame, allocator.reserve frames 1#usize=.ok (false,frames))

end Itasca.Interp

end InterpResources

/-! Internal instruction-position and compiled-function relations for the simulation proof. -/

/-! ## Interp / InitializerResources -/

section InterpInitializerResources

/-!
### Synthetic initializer resource causes

`SyntheticPreparationCause` identifies a concrete resource cause reached by synthetic
initializer preparation.
-/

namespace Itasca.Interp

open Aeneas Aeneas.Std
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

/-- Synthetic initialization allocates exactly its fixed slot count and one
frame. Refusals retain those concrete requests; the value quota is explicit. -/
def SyntheticPreparationCause {M A : Type} (allocator : runtime.platform.Alloc A)
    (store : runtime.store.Store M) (code : runtime.bytecode.CompiledFunction) : runtime.ExecError → Prop
  | .Exhausted .Values => store.limits.max_values.val < (UScalar.cast .Usize code.slot_count).val
  | .Exhausted .Allocation =>
      allocator.reserve (alloc.vec.Vec.new U64) (UScalar.cast .Usize code.slot_count) =
        .ok (false,alloc.vec.Vec.new U64) ∨
      allocator.reserve (alloc.vec.Vec.new runtime.interp.Frame) 1#usize =
        .ok (false,alloc.vec.Vec.new runtime.interp.Frame)
  | _ => False

end Itasca.Interp

end InterpInitializerResources

/-! ## Interp / Machine / Point -/

section InterpMachinePoint

/-!
### Active and suspended machine points

Context emissions, frame points and control points relate concrete program counters to
source continuations and structured code positions.
-/

namespace Itasca.Interp.Machine

open Aeneas.Std

abbrev ContextEmission := context → List valtype → instr → List Compiler.Bytecode → List valtype → Prop

end Itasca.Interp.Machine

namespace Itasca.Interp

/-- The emission relation of a compiled function: the complete compiler relation over the
function's retained indirect, SIMD, constant and jump-table metadata. -/
abbrev emission (compiled : runtime.bytecode.CompiledFunction) : Machine.ContextEmission :=
  Compiler.ExecutableEmission (Compiler.CompilerTables.ofFunction compiled)

end Itasca.Interp



end InterpMachinePoint




/-! ## Interp / Machine / Functions -/

section InterpMachineFunctions

open Itasca.Representation

/-!
### Compiled source functions

Source contexts, typing and function/code relations connect retained concrete function
objects to the source bodies supplied by the code interpretation.
-/

namespace Itasca.Compiler

/-- The completed module context has no ambient function-local declarations. -/
def moduleSourceContext (module : runtime.compiler.ExecutableModule) : context :=
  {moduleFunctionContext module [] [] with RETURN := none}

end Itasca.Compiler

namespace Itasca.Interp

open Aeneas Aeneas.Std

/-- Source typing uses the exact canonical context retained by the compiler,
not an existential alternative with unrelated global or memory declarations. -/
def CoreFunctionTyped {M : Type} (view : M → Slice U8) (code : Representation.CodeInterpretation)
    (store : runtime.store.Store M) (function : runtime.store.FuncInst) : Prop :=
  match function.code with
  | .Host _ => Functype_ok (Representation.decodeFunction code store function).TYPE
  | .Wasm instanceIndex functionIndex =>
      ∃ inst index locals body,
        store.instances.val[instanceIndex.val]? = some inst ∧
        code instanceIndex.val inst.module functionIndex.val = .FUNC index locals body ∧
        SourceMachine.ModuleBindings (Representation.decodeStore view code store) (Representation.decodeInstance store inst)
          (Compiler.moduleSourceContext inst.module) ∧
        Func_ok (Compiler.moduleSourceContext inst.module) (.FUNC index locals body)
          (Representation.decodeFunction code store function).TYPE

def CoreFunctionsTyped {M : Type} (view : M → Slice U8) (code : Representation.CodeInterpretation)
    (store : runtime.store.Store M) : Prop :=
  ∀ function ∈ store.funcs.val, CoreFunctionTyped view code store function

end Itasca.Interp

namespace Itasca.Interp.Machine

open Aeneas.Std

/-- Function-local emission metadata and complete syntactic compiler evidence. -/
def FunctionCode (C : context)
    (params declared results : List valtype) (body : List instr)
    (compiled : runtime.bytecode.CompiledFunction) (epilogue : U32) : Prop :=
  C.LOCALS = params ++ declared ∧
  Compiler.StructuredFunctionCode (emission compiled C) C.TYPES C.FUNCS params declared results body compiled epilogue

end Itasca.Interp.Machine

namespace Itasca.Interp.Machine

open Aeneas Aeneas.Std

/-- Concrete function lookup retains the canonical source context for mutable
instructions. This is source syntax and layout evidence, independent of any
claim about execution or mutable store contents. -/
def FunctionCompiled {M : Type} (code : Representation.CodeInterpretation)
    (store : runtime.store.Store M) (function : runtime.store.FuncInst) : Prop :=
  ∀ instanceIndex functionIndex, function.code = .Wasm instanceIndex functionIndex →
    ∃ inst compiled signature declared body epilogue,
      store.instances.val[instanceIndex.val]? = some inst ∧
      inst.module.functions.val[functionIndex.val]? = some compiled ∧
      store.types.val[function.signature.val]? = some signature ∧
      code instanceIndex.val inst.module functionIndex.val =
        .FUNC (.mk_uN compiled.type_index.val) (declared.map local.LOCAL) body ∧
      FunctionTable store inst (inst.module.module.env.func_types.val.map Itasca.Translation.Environment.funcType) ∧
      (Representation.decodeInstance store inst).TYPES = inst.module.module.env.types.val.map Itasca.Translation.Environment.funcType ∧
      FunctionCode (Compiler.moduleFunctionContext inst.module
        (signature.params.val.map Itasca.Translation.valueType ++ declared) (signature.results.val.map Itasca.Translation.valueType))
        (signature.params.val.map Itasca.Translation.valueType) declared (signature.results.val.map Itasca.Translation.valueType)
        body compiled epilogue

def CompiledFunctions {M : Type} (code : Representation.CodeInterpretation)
    (store : runtime.store.Store M) : Prop :=
  ∀ function ∈ store.funcs.val, FunctionCompiled code store function

end Itasca.Interp.Machine

end InterpMachineFunctions


/-! ## Interp / Mutation -/

section InterpMutation

/-!
### Concrete store mutation witnesses

Global, opaque-memory and table update witnesses describe exactly which object
changes and what its representation retains. Execution joins use these relations
to transport source effects and concrete store invariants.
-/

/-!
## Global mutation witness

`GlobalMutation` supplies the concrete global-update witness used by the source/machine
execution join.
-/

namespace Itasca.Interp
open Itasca.Representation

open Aeneas Aeneas.Std

/-- An instruction writes the represented source value into one existing global;
scalar writes retain the unused high word. -/
def GlobalMutation {M : Type} (before after : runtime.store.Store M) (value : val) : Prop :=
  ∃ index : Usize, ∃ old : runtime.store.GlobalInst, ∃ lo hi : U64,
    before.globals.val[index.val]? = some old ∧ old.ty.mutability = .Var ∧
    Itasca.Translation.valueType old.ty.valtype = Representation.valueType value ∧
    pairWords old.ty.valtype (lo,hi) = Representation.encodeValue value ∧
    (old.ty.valtype ≠ .V128 → hi = old.hi) ∧
    after = {before with globals := before.globals.set index {old with lo,hi}}

end Itasca.Interp

/-!
## Memory mutation witness

`MemoryMutation` describes the concrete memory effect carried through source/machine
execution and store preservation.
-/

namespace Itasca.Interp

open Aeneas Aeneas.Std WebAssembly

/-- A scalar memory instruction changes only the selected opaque buffer and
retains its byte length. This includes bounds failures whose writeback callback
chooses a different representation of the same bytes. -/
def MemoryMutation {M : Type} (view : M → Slice U8) (before after : runtime.store.Store M)
    (address : runtime.MemoryAddr) (object : runtime.store.MemInst M) : Prop :=
  ∃ buffer, after = {before with memories := before.memories.set address.index {object with buf := buffer}} ∧
    (view buffer).length = (view object.buf).length

end Itasca.Interp

/-!
## Table mutation witness

`TableMutation` supplies the concrete table-update witness used by stateful
source/machine execution.
-/

namespace Itasca.Interp

open Aeneas Aeneas.Std

/-- A table content update retains the object's reference type, maximum and
length; every word is either retained or the explicit replacement reference. -/
def TableMutation {M : Type} (before after : runtime.store.Store M)
    (address : runtime.TableAddr) (object : runtime.store.TableInst) (replacement : U64) : Prop :=
  ∃ words, after = {before with tables := before.tables.set address.index {object with elements := words}} ∧
    words.length = object.elements.length ∧
    ∀ word ∈ words.val, word ∈ object.elements.val ∨ word = replacement

end Itasca.Interp

end InterpMutation
