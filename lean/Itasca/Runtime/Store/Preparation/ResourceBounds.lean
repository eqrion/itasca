import Itasca.Runtime.Store.Definitions
import Itasca.Runtime.Store.Invariant.Rollback
import Itasca.Runtime.Store.Invariant.PrecommitError
import Itasca.Runtime.Store.Api.ObjectStaging
import Itasca.Runtime.Store.Api.GlobalStagingAndCopy

/-!
Proofs for Runtime / Store / Preparation.

This module collects PreparationCalls, ResourceBounds.
Each section documents its contracts and consumers.
-/

/-! ## PreparationCalls -/

section

/-! ## AllocationCauses -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

/-- The allocator's actual Boolean response is retained alongside the runtime
error wrapper. Capacity changes cannot alter the vector's logical contents. -/
theorem reserve_with_cause {A T : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (values : alloc.vec.Vec T) (extra : Usize) :
    ∃ answer : Bool, runtime.reserve allocator values extra = .ok
      ((if answer then .Ok () else .Err (.Exhausted .Allocation)),values) ∧
      allocator.reserve values extra = .ok (answer,values) := by
  obtain ⟨answer,called⟩ := law.reserve_eq values extra
  refine ⟨answer,?_,called⟩
  cases answer <;> simp [runtime.reserve,called]

theorem copy_type_resource_causes {A : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (ty : Itasca.wasm_types.FuncType) :
    runtime.copy_type allocator ty ⦃ answer => answer = .Ok ty ∨
      (answer = .Err (.Exhausted .Allocation) ∧ TypeCopyRefusal allocator ty) ⦄ := by
  unfold runtime.copy_type
  dsimp only
  obtain ⟨answer,wrapped,called⟩ := reserve_with_cause allocator law
    (alloc.vec.Vec.new Itasca.wasm_types.ValueType) ty.params.len
  rw [wrapped]
  cases answer
  · simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,TypeCopyRefusal,called]
  · simp [core.result.Result.Insts.CoreOpsTry.branch]
    obtain ⟨answer,wrapped,called⟩ := reserve_with_cause allocator law
      (alloc.vec.Vec.new Itasca.wasm_types.ValueType) ty.results.len
    rw [wrapped]
    cases answer
    · simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,TypeCopyRefusal,called]
    · simp
      step with copy_type_loop ty.params (alloc.vec.Vec.new Itasca.wasm_types.ValueType) 0#usize
        (by scalar_tac) (by simp) as ⟨params,hp⟩
      step with copy_type_loop_results ty.results (alloc.vec.Vec.new Itasca.wasm_types.ValueType) 0#usize
        (by scalar_tac) (by simp) as ⟨results,hr⟩
      simp [hp,hr]
end Itasca.Store

end

end

/-! ## ResourceBounds -/

section

/-! Source-sized bounds on preparation effects.

These lemmas forget concrete object payloads and retain only the quantities
charged against resource limits. They establish public refusal bounds from the
starting store and source declarations, without exporting helper-call traces. Reusing an interned signature can only reduce the source allowance.
-/
namespace Itasca.Store
open Aeneas Aeneas.Std Itasca.Representation

namespace PreparationDemand

/-- One canonical object per signature, plus its parameter and result values. -/
def types (source : List wasm_types.FuncType) : PreparationDemand :=
  {objects := source.length,
   signatures := (source.map fun ty => ty.params.length + ty.results.length).sum}

/-- One object per table and storage for its declared minimum. -/
def tables (source : List wasm_types.TableType) : PreparationDemand :=
  {objects := source.length,
   tableElements := (source.map fun ty => ty.limits.min.val).sum}

/-- One object per memory and its declared minimum in bytes (64 KiB pages). -/
def memories (source : List wasm_types.MemType) : PreparationDemand :=
  {objects := source.length,
   memoryBytes := (source.map fun ty => ty.limits.min.val * 65536).sum}

def add (a b : PreparationDemand) : PreparationDemand :=
  ⟨a.objects + b.objects, a.signatures + b.signatures,
    a.memoryBytes + b.memoryBytes, a.tableElements + b.tableElements⟩

/-- Signature allowance for a source prefix. This is used only while composing
loop proofs; the public requirement uses the complete source list. -/
theorem types_step (source : List wasm_types.FuncType) (i : Nat) (within : i < source.length) :
    (types (source.take i)).add
      {objects := 1, signatures := source[i].params.length + source[i].results.length} =
      types (source.take (i + 1)) := by
  rw [List.take_succ_eq_append_getElem within]
  simp only [types, add, List.length_append, List.length_singleton, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]

/-- Storage allowance for a source prefix. This is used only while composing
loop proofs; the public requirement uses the complete source list. -/
theorem tables_step (source : List wasm_types.TableType) (i : Nat) (within : i < source.length) :
    (tables (source.take i)).add
      {objects := 1, tableElements := source[i].limits.min.val} =
      tables (source.take (i + 1)) := by
  rw [List.take_succ_eq_append_getElem within]
  simp only [tables, add, List.length_append, List.length_singleton, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]

/-- Storage allowance for a source prefix. This is used only while composing
loop proofs; the public requirement uses the complete source list. -/
theorem memories_step (source : List wasm_types.MemType) (i : Nat) (within : i < source.length) :
    (memories (source.take i)).add
      {objects := 1, memoryBytes := source[i].limits.min.val * 65536} =
      memories (source.take (i + 1)) := by
  rw [List.take_succ_eq_append_getElem within]
  simp only [memories, add, List.length_append, List.length_singleton, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]

end PreparationDemand

theorem PreparationGrowth.refl {M : Type} (store : runtime.store.Store M) :
    PreparationGrowth store store {} := ⟨rfl, by omega, by omega, by omega, by omega⟩

theorem PreparationGrowth.trans {M : Type} {before middle after : runtime.store.Store M}
    {a b : PreparationDemand} (first : PreparationGrowth before middle a)
    (second : PreparationGrowth middle after b) : PreparationGrowth before after (a.add b) := by
  rcases first with ⟨limits₁, objects₁, signatures₁, memory₁, tables₁⟩
  rcases second with ⟨limits₂, objects₂, signatures₂, memory₂, tables₂⟩
  exact ⟨limits₂.trans limits₁, by dsimp [PreparationDemand.add]; omega,
    by dsimp [PreparationDemand.add]; omega, by dsimp [PreparationDemand.add]; omega,
    by dsimp [PreparationDemand.add]; omega⟩

/-- Unused source allowance may be retained when a phase stops early. -/
theorem PreparationGrowth.mono {M : Type} {before after : runtime.store.Store M}
    {a b : PreparationDemand} (growth : PreparationGrowth before after a)
    (objects : a.objects ≤ b.objects) (signatures : a.signatures ≤ b.signatures)
    (memoryBytes : a.memoryBytes ≤ b.memoryBytes) (tableElements : a.tableElements ≤ b.tableElements) :
    PreparationGrowth before after b := by
  rcases growth with ⟨limits, oldObjects, oldSignatures, oldMemory, oldTables⟩
  exact ⟨limits, by omega, by omega, by omega, by omega⟩

/-- A partial signature traversal never exceeds the full source allowance. -/
theorem PreparationGrowth.types_complete {M : Type} {before after : runtime.store.Store M}
    {source : List wasm_types.FuncType} {i : Nat}
    (growth : PreparationGrowth before after (PreparationDemand.types (source.take i))) :
    PreparationGrowth before after (PreparationDemand.types source) := by
  apply growth.mono
  · simp only [PreparationDemand.types, List.length_take]; omega
  · have partition := congrArg
      (fun xs : List wasm_types.FuncType =>
        (xs.map fun ty => ty.params.length + ty.results.length).sum)
      (List.take_append_drop i source)
    simp only [List.map_append, List.sum_append] at partition
    dsimp only [PreparationDemand.types]
    omega
  · exact Nat.le_refl _
  · exact Nat.le_refl _

/-- A partial storage traversal never exceeds the full source allowance. -/
theorem PreparationGrowth.tables_complete {M : Type} {before after : runtime.store.Store M}
    {source : List wasm_types.TableType} {i : Nat}
    (growth : PreparationGrowth before after (PreparationDemand.tables (source.take i))) :
    PreparationGrowth before after (PreparationDemand.tables source) := by
  apply growth.mono
  · simp only [PreparationDemand.tables, List.length_take]; omega
  · exact Nat.le_refl _
  · exact Nat.le_refl _
  · have partition := congrArg
      (fun xs : List wasm_types.TableType =>
        (xs.map fun ty => ty.limits.min.val).sum)
      (List.take_append_drop i source)
    simp only [List.map_append, List.sum_append] at partition
    dsimp only [PreparationDemand.tables]
    omega

/-- A partial storage traversal never exceeds the full source allowance. -/
theorem PreparationGrowth.memories_complete {M : Type} {before after : runtime.store.Store M}
    {source : List wasm_types.MemType} {i : Nat}
    (growth : PreparationGrowth before after (PreparationDemand.memories (source.take i))) :
    PreparationGrowth before after (PreparationDemand.memories source) := by
  apply growth.mono
  · simp only [PreparationDemand.memories, List.length_take]; omega
  · exact Nat.le_refl _
  · have partition := congrArg
      (fun xs : List wasm_types.MemType =>
        (xs.map fun ty => ty.limits.min.val * 65536).sum)
      (List.take_append_drop i source)
    simp only [List.map_append, List.sum_append] at partition
    dsimp only [PreparationDemand.memories]
    omega
  · exact Nat.le_refl _

/-- Canonical interning charges at most one object and the source signature's
parameter/result count. A reused signature has zero additional charge. -/
theorem InternEffect.resource_growth {M : Type} {store : runtime.store.Store M}
    {ty : wasm_types.FuncType} {out}
    (effect : InternEffect store ty out) :
    PreparationGrowth store out.2
      {objects := 1, signatures := ty.params.length + ty.results.length} := by
  rcases effect with ⟨error, rfl⟩ | ⟨index, found, rfl⟩ |
    ⟨types, count, appended, fresh, room, charged, bounded, rfl⟩
  · constructor <;> dsimp <;> omega
  · constructor <;> dsimp <;> omega
  · have length : types.length = store.types.length + 1 := by
      simpa only [List.length_append, List.length_singleton] using congrArg List.length appended
    constructor
    · rfl
    · simp only [objectCount]
      omega
    · dsimp only
      omega
    · exact Nat.le_refl _
    · exact Nat.le_refl _

/-- Installing a source type uses only its canonical interning allowance. -/
theorem TypeStageEffect.resource_growth {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {ty : wasm_types.FuncType} {out}
    (effect : TypeStageEffect store inst ty out) :
    PreparationGrowth store out.2.1
      {objects := 1, signatures := ty.params.length + ty.results.length} := by
  rcases effect with ⟨error, rfl⟩ | ⟨index, addresses, interned, rest⟩
  · constructor <;> dsimp <;> omega
  · exact interned.resource_growth

/-- A defined function consumes one store object, irrespective of its bytecode. -/
theorem FunctionStageEffect.resource_growth {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {instanceIndex index signature out}
    (effect : FunctionStageEffect store inst instanceIndex index signature out) :
    PreparationGrowth store out.2.1 {objects := 1} := by
  rcases effect with ⟨error, rfl⟩ | ⟨functions, addresses, appended, mapped, room, rfl⟩
  · constructor <;> dsimp <;> omega
  · have length : functions.length = store.funcs.length + 1 := by
      simpa only [List.length_append, List.length_singleton] using congrArg List.length appended
    constructor
    · rfl
    · simp only [objectCount]; omega
    · exact Nat.le_refl _
    · exact Nat.le_refl _
    · exact Nat.le_refl _

/-- Table storage is bounded by its source minimum, in table elements. -/
theorem TableStageEffect.resource_growth {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {ty : wasm_types.TableType} {out}
    (effect : TableStageEffect store inst ty out) :
    PreparationGrowth store out.2.1 {objects := 1, tableElements := ty.limits.min.val} := by
  rcases effect with ⟨error, rfl⟩ |
    ⟨tables, elements, addresses, count, zeros, appended, mapped, fit, room, charged, bounded, rfl⟩
  · constructor <;> dsimp <;> omega
  · have length : tables.length = store.tables.length + 1 := by
      simpa only [List.length_append, List.length_singleton] using congrArg List.length appended
    constructor
    · rfl
    · simp only [objectCount]; omega
    · exact Nat.le_refl _
    · exact Nat.le_refl _
    · exact Nat.le_of_eq charged

/-- Memory storage is bounded by its source minimum, converted from pages to bytes. -/
theorem MemoryStageEffect.resource_growth {M : Type} {view : M → Slice U8}
    {store : runtime.store.Store M} {inst : runtime.store.ModuleInst}
    {ty : wasm_types.MemType} {out} (effect : MemoryStageEffect view store inst ty out) :
    PreparationGrowth store out.2.1 {objects := 1, memoryBytes := ty.limits.min.val * 65536} := by
  rcases effect with ⟨error, rfl⟩ |
    ⟨memories, buffer, addresses, count, zeros, appended, mapped, fit, room, charged, bounded, rfl⟩
  · constructor <;> dsimp <;> omega
  · have length : memories.length = store.memories.length + 1 := by
      simpa only [List.length_append, List.length_singleton] using congrArg List.length appended
    have bytes : (view buffer).length = ty.limits.min.val * 65536 := by
      simpa only [List.length_replicate] using congrArg List.length zeros
    constructor
    · rfl
    · simp only [objectCount]; omega
    · exact Nat.le_refl _
    · dsimp only
      omega
    · exact Nat.le_refl _

/-- Initializer evaluation does not add objects beyond its declared global. -/
theorem GlobalStageEffect.resource_growth {M : Type} {store after : runtime.store.Store M}
    {instIndex : Usize} {inst : runtime.store.ModuleInst}
    (effect : GlobalStageEffect store instIndex inst after) :
    PreparationGrowth store after {objects := 1} := by
  cases effect with
  | unchanged => constructor <;> dsimp <;> omega
  | appended globals addresses global appended mapped canonical room =>
    have length : globals.length = store.globals.length + 1 := by
      simpa only [List.length_append, List.length_singleton] using congrArg List.length appended
    constructor
    · rfl
    · simp only [objectCount]; omega
    · exact Nat.le_refl _
    · exact Nat.le_refl _
    · exact Nat.le_refl _

theorem synthetic_resource {M A : Type} {allocator : runtime.platform.Alloc A}
    {store : runtime.store.Store M} {code : runtime.bytecode.CompiledFunction} {error : runtime.ExecError}
    (bounded : code.slot_count.val ≤ 3)
    (cause : Interp.SyntheticPreparationCause allocator store code error) :
    InitializationResourceDemand allocator store error := by
  have castBound : (UScalar.cast .Usize code.slot_count).val ≤ 3 := by scalar_tac
  cases error with
  | Exhausted limit =>
    cases limit with
    | Values => exact Nat.lt_of_lt_of_le cause castBound
    | Allocation => exact cause.imp (fun refused => ⟨_, castBound, refused⟩) id
    | CallStack | Objects => exact cause.elim
  | Trap _ | Link _ | BadArguments | WrongStore | Terminated | Internal => exact cause.elim

theorem initializer_resource {M A : Type} {allocator : runtime.platform.Alloc A}
    {store : runtime.store.Store M} {code : runtime.bytecode.CompiledFunction}
    {expr : Itasca.wasm_types.ConstExpr} {ty : Itasca.wasm_types.ValueType} {error : runtime.ExecError}
    (compiled : Compiler.InitializerCode code expr ty)
    (cause : Interp.SyntheticPreparationCause allocator store code error) :
    InitializationResourceDemand allocator store error := by
  apply synthetic_resource (code := code) ?_ cause
  have capacity := compiled.capacity
  cases ty <;> simp only [initializerWidth] at capacity <;> scalar_tac

theorem ElementInitializerCause.public {M A : Type}
    {allocator : runtime.platform.Alloc A} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {index : Usize} {segment : Itasca.metadata.Element} {error : runtime.ExecError}
    (cause : ElementInitializerCause allocator store inst index segment error) :
    ElementInitializationResource allocator store segment error := by
  obtain ⟨k, functions, function, code, expr, bounded, _, _, found, _, compiled, refusal⟩ := cause
  exact ⟨k, expr, bounded, found, initializer_resource compiled refusal⟩

theorem ElementAllocationCause.public {M A : Type}
    {allocator : runtime.platform.Alloc A} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {index : Usize} {segment : Itasca.metadata.Element} {error : runtime.ExecError}
    (cause : ElementAllocationCause allocator store inst index segment error) :
    ElementPreparationResource allocator store segment error :=
  cause.imp id ElementInitializerCause.public

end Itasca.Store

end
