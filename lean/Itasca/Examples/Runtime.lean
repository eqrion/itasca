import Itasca.Main

/-!
# Closed runtime examples

The concrete vector memory, mathematical float dictionary, trapping callbacks,
and granting allocator discharge the runtime's platform obligations. These
examples establish a fresh store and compile the eight-byte empty module from
independent source validity and numerical eligibility. The generic trapping-host
corollary is retained alongside the closed examples.
-/

namespace Itasca.Runtime.Examples
open Aeneas Aeneas.Std SpecExt Integration

theorem trapHost_no_spurious_errors {M F : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (correct : Platform.FloatOpsCorrect floats)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (valid : ExecutableInv view code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (owner : address.store=store.id) (issued : Store.ExternalIssued store (.Func address))
    (owned : ∀value∈args.val,Store.ValueInStore store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map Interp.sourceValue) initial)
    (typedArguments : InvocationArgumentsTyped (Store.decodeStore view code store) address.index.val
      (args.val.map Interp.sourceValue))
    (fits : SourceResourcesFit (Store.decodeStore view code store) address.index.val initial
      store.limits.max_values.val store.limits.max_frames.val) :
    runtime.interp.invoke_with memory (trapHost memory) floats grantAll exec store () address args results
      ⦃ out => ∀error,out.1=.Err error → ∃trap,error=.Trap trap ⦄div :=
  runtime.interp.invoke_with.no_spurious_errors memory (trapHost memory) floats grantAll view
    ⟨correct,grantAll_correct,fun _ => by rw [trapHost,WP.spec_ok]; trivial,laws⟩ code (trapHost_laws memory view)
    (fun _ _ _ _ _ _ _ result nextPlatform after returned called =>
      congrArg (fun (_, _, store, _) => store.limits) (trapHost_answer called))
    exec store () valid address args results owner issued owned initial invoked typedArguments fits
    (grantAll_available _) (fun _ _ refused => by simp [trapHost] at refused)
    (fun _ _ _ _ _ _ _ _ _ _ refused => by have same := trapHost_answer refused; simp at same)


def exampleMemory := Platform.vecMemory grantAll
def exampleView := Platform.vecMemoryView
def exampleCode : Store.CodeInterpretation := fun _ _ _ => .HOST 0
def exampleLimits : runtime.store.StoreLimits :=
  ⟨1024#usize, 1024#usize, 1024#usize, 1024#usize, 1024#usize, 1024#usize, 1024#usize, 1024#usize⟩
def freshStore : runtime.store.Store runtime.platform.VecMemory := {
  id := 1#usize, limits := exampleLimits,
  funcs := alloc.vec.Vec.new _, types := alloc.vec.Vec.new _, tables := alloc.vec.Vec.new _,
  memories := alloc.vec.Vec.new _, globals := alloc.vec.Vec.new _, instances := alloc.vec.Vec.new _,
  elems := alloc.vec.Vec.new _, datas := alloc.vec.Vec.new _, externs := alloc.vec.Vec.new _,
  instance_items := 0#usize, signature_values := 0#usize, memory_bytes := 0#usize, table_elements := 0#usize }

theorem fresh_store_valid : ExecutableInv exampleView exampleCode freshStore := by
  have created := runtime.store.Store.with_identity.spec exampleMemory exampleView exampleCode
    1#usize exampleLimits (by scalar_tac)
  change Result.ok freshStore ⦃ store => ExecutableInv exampleView exampleCode store ∧
    store.id = 1#usize ∧ store.limits = exampleLimits ∧ Store.decodeStore exampleView exampleCode store = ⟨[], [], [], [], [], []⟩ ⦄ at created
  simp only [WP.spec_ok] at created
  exact created.1

private theorem host_invocation {s : store} {address host : Nat}
    (wellFormed : wf_store s) (function : HostFunction s address host [] []) :
    fun_invoke s address [] ⟨⟨s, Spec.invocationFrame⟩, [.CALL_ADDR address]⟩ := by
  obtain ⟨module, found⟩ := function
  have frameWf : wf_frame Spec.invocationFrame := by
    constructor
    · intro value member; cases member
    · constructor; intro exported member; cases member
  have typed : ResultsTyped s [] [] := by
    exact List.Forall₂.nil
  have configWf := Spec.host_call_wf (fa := address) wellFormed frameWf typed
  apply fun_invoke.fun_invoke_case_0 s address 0 [] Spec.invocationFrame [] [] rfl
  · exact (List.getElem?_eq_some_iff.mp found).1
  · simpa only [fun_funcinst, List.getElem!_eq_getElem?_getD, found, Option.getD_some]
  · exact configWf
  · exact frameWf
  · exact .state_case_0 _ _ wellFormed frameWf
  · rfl



def exampleHostType : Itasca.wasm_types.FuncType := ⟨alloc.vec.Vec.new _, alloc.vec.Vec.new _⟩
def exampleExecution : runtime.interp.Execution :=
  ⟨0#usize, alloc.vec.Vec.new _, alloc.vec.Vec.new _, alloc.vec.Vec.new _, alloc.vec.Vec.new _⟩

/-- This closed call creates a fresh store, successfully defines a [] → []
host, and applies invocation soundness with every platform obligation proved. -/
theorem host_only_invoke : ∃ address after,
    runtime.store.Store.define_host_with exampleMemory grantAll freshStore exampleHostType 0#u64 =
      .ok (.Ok address, after) ∧
    InvocationBehaves exampleMemory (trapHost exampleMemory) Platform.floatWitness grantAll
      exampleView exampleCode exampleExecution after () address (Slice.new runtime.Value)
      (alloc.vec.Vec.new runtime.Value)
      ⟨⟨Store.decodeStore exampleView exampleCode after, Spec.invocationFrame⟩, [.CALL_ADDR address.index.val]⟩
      (runtime.interp.invoke_with exampleMemory (trapHost exampleMemory) Platform.floatWitness grantAll
        exampleExecution after () address (Slice.new runtime.Value) (alloc.vec.Vec.new runtime.Value)) := by
  have available := define_host_available exampleMemory grantAll grantAll_correct (grantAll_available _)
    freshStore exampleHostType 0#u64
    (by simp only [freshStore, Store.objectCount, alloc.vec.Vec.new, alloc.vec.Vec.from_val,
          alloc.vec.Vec.length, List.length_nil, Nat.zero_add, exampleLimits]; scalar_tac)
    (by simp only [exampleHostType, alloc.vec.Vec.new, alloc.vec.Vec.from_val,
          alloc.vec.Vec.length, List.length_nil, Nat.zero_add]; omega)
    (by simp only [freshStore, exampleHostType, alloc.vec.Vec.new, alloc.vec.Vec.from_val,
          alloc.vec.Vec.length, List.length_nil, Nat.add_zero, exampleLimits]; scalar_tac)
  obtain ⟨⟨result, after⟩, run, address, same⟩ := WP.spec_imp_exists available
  subst result
  have defined := runtime.store.Store.define_host_with.spec exampleMemory grantAll grantAll_correct
    exampleView exampleCode freshStore fresh_store_valid exampleHostType 0#u64
  rw [run] at defined
  simp only [WP.spec_ok, uncurry_apply_pair] at defined
  obtain ⟨valid, retained, extension, owner, index, issued, owned, host⟩ := defined
  have sourceHost : HostFunction (Store.decodeStore exampleView exampleCode after) address.index.val 0 [] [] := by
    simpa only [exampleHostType, alloc.vec.Vec.new, alloc.vec.Vec.from_val, List.map_nil,
      UScalar.ofNatCore_val_eq] using host
  refine ⟨address, after, run, ?_⟩
  apply runtime.interp.invoke_with.behaves exampleMemory (trapHost exampleMemory) Platform.floatWitness
    grantAll exampleView ?_ exampleCode (trapHost_laws _ _) exampleExecution after () valid
    address (Slice.new runtime.Value) (alloc.vec.Vec.new runtime.Value) issued ?_
    _ (host_invocation valid.well_formed sourceHost)
  · exact ⟨Platform.floatWitness_correct, grantAll_correct,
      fun _ => by rw [trapHost, WP.spec_ok]; trivial, Platform.vecMemory_laws grantAll grantAll_correct⟩
  · intro value member
    cases member

namespace EmptyModule
open Compiler Itasca ModuleBinary ModuleElaboration

def raw : ModuleBinary.Module := ⟨[], [], [], [], [], [], [], none, [], none, [], []⟩
def bytes : Slice U8 := Slice.from magicVersion (by simp only [magicVersion, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd]; scalar_tac)
def env : metadata.Env where
  types := alloc.vec.Vec.new _
  imports := alloc.vec.Vec.new _
  globals := alloc.vec.Vec.new _
  exports := alloc.vec.Vec.new _
  elements := alloc.vec.Vec.new _
  start := none
  data_count := none
  declared_funcs := alloc.vec.Vec.new _
  func_type_indices := alloc.vec.Vec.new _
  func_types := alloc.vec.Vec.new _
  table_types := alloc.vec.Vec.new _
  mem_types := alloc.vec.Vec.new _
  global_types := alloc.vec.Vec.new _
  num_imported_funcs := 0#usize
  num_imported_globals := 0#usize

private theorem cache : ModuleEnv.Cache env [] [] := by
  constructor <;> simp only [env, alloc.vec.Vec.from_val, ModuleEnv.importedFuncs, ModuleEnv.importedGlobals,
    ModuleEnv.importedTables, ModuleEnv.importedMems, List.filterMap_nil, List.append_nil,
    List.forall₂_nil_right_iff, UScalar.ofNatCore_val_eq, List.length_nil, List.map_nil]

private theorem environment_valid : ModuleEnv.Valid env := by
  constructor <;> simp only [env, Itasca.Profile.FuncTypeAdmissible, ModuleReferences.Coherent,
    ModuleReferences.collected, alloc.vec.Vec.from_val, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, Nat.reducePow, Nat.add_one_sub_one, List.length_nil, zero_le, List.map_nil,
    List.nodup_nil, reduceCtorEq, not_lt_zero, IsEmpty.exists_iff, imp_self, List.flatMap_nil,
    List.append_nil]

private theorem omitted {α : Type} (id : U8) (R : α → List U8 → Prop) (absent : α) :
    PaddedEncoding id R absent absent [] := ⟨[], [], .nil, .absent, rfl⟩

private theorem encoded : ModuleEncodingWithinLimits raw bytes.val := by
  constructor
  · exact Compiler.module_header_fits
  · refine ⟨[], [], [], [], [], [], [], [], [], [], [], [], [],
      omitted _ _ _, omitted _ _ _, omitted _ _ _, omitted _ _ _, omitted _ _ _,
      omitted _ _ _, omitted _ _ _, omitted _ _ _, omitted _ _ _, omitted _ _ _,
      omitted _ _ _, omitted _ _ _, .nil, ?_, ?_⟩
    · simp only [bytes, Slice.from_val, List.append_nil]
    · simp only [DataCountValid, raw, List.not_mem_nil, IsEmpty.forall_iff, implies_true]

theorem valid : Runtime.Compiler.ValidCompilationSource bytes raw := by
  have codes : List.Forall₂ (fun idx code => CodeEntry.Typed env idx code) env.func_type_indices.val [] := .nil
  refine ⟨encoded, ?_, ?_, ?_, ?_⟩
  · simp only [ModuleSignaturesWithinLimits, raw, List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  · exact ModuleElaboration.elaborates (segments := []) cache codes
  · exact ModuleElaboration.typed (segments := []) cache environment_valid (by simp only [env, alloc.vec.Vec.from_val, List.not_mem_nil, IsEmpty.forall_iff, implies_true]) (by simp only [env, alloc.vec.Vec.from_val, List.not_mem_nil, IsEmpty.forall_iff, implies_true])
      codes (by simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true]) (by simp only [env, reduceCtorEq, List.length_nil, IsEmpty.forall_iff, implies_true]) (List.Forall₂.nil : List.Forall₂ (ModuleExternals.ExportResolves env) [] [])
  · exact ModuleElaboration.restrictions (segments := []) cache environment_valid codes

theorem empty_demand {data regions env tail} (certificate : StreamCompleteRegions.Certificate data raw regions env tail)
    (limits : runtime.compiler.CompileLimits) (room : 1 ≤ limits.max_instructions.val) :
    SourceCompilationDemand Unit env tail limits 0 0 0 4 := by
  have oneFits : 1 ≤ Usize.max := by scalar_tac
  have rawEq := certificate.realization.1
  have types : env.types.val = [] := (congrArg ModuleBinary.Module.types rawEq).symm
  have funcs : env.func_type_indices.val = [] := (congrArg ModuleBinary.Module.functions rawEq).symm
  have globals : env.globals.val = [] := (congrArg ModuleBinary.Module.globals rawEq).symm
  have imports : env.imports.val = [] := List.map_eq_nil_iff.mp (congrArg ModuleBinary.Module.imports rawEq).symm
  have elements : env.elements.val = [] := List.map_eq_nil_iff.mp (congrArg ModuleBinary.Module.elements rawEq).symm
  have segments : tail.data.val = [] := List.map_eq_nil_iff.mp (congrArg ModuleBinary.Module.data rawEq).symm
  have ftypes : env.func_types.val = [] := by
    have related := certificate.realization.2.funcs
    simpa [imports,funcs,ModuleEnv.importedFuncs] using related
  constructor
  · constructor <;> simp only [initialScheduler, alloc.vec.Vec.new, alloc.vec.Vec.length, alloc.vec.Vec.from_val, types, funcs, ftypes, List.length_nil, List.not_mem_nil, IsEmpty.forall_iff, implies_true, Nat.add_zero, Nat.zero_le]
  · constructor
    · simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_le]
    · intro counter; cases counter <;> simp only [initialScheduler, ChargeCounter.used, ChargeCounter.limit, funcs, UScalar.ofNatCore_val_eq, List.length_nil, Nat.zero_mul, Nat.add_zero, Nat.zero_le]
    · decide
    · decide
    · decide
    · simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_le]
  · intro bytes ordinal position next entry encoded prepared
    have impossible := prepared.index_lt
    simp only [funcs, List.length_nil, Nat.not_lt_zero] at impossible
  all_goals simp only [alloc.vec.Vec.length,funcs,globals,elements,segments,sourceInitializerInstructions,
    initializerMappingCost, initializerElementCost, room, oneFits, List.length_nil, Nat.mul_zero, Nat.zero_mul, List.map_nil, List.sum_nil, Nat.add_zero, Nat.zero_add, Nat.one_le_ofNat, Nat.reduceLeDiff, Nat.zero_le, List.not_mem_nil, IsEmpty.forall_iff, implies_true, Std.le_refl]

/-- Eight input bytes and one initializer instruction suffice for the empty module. -/
def compileLimits : runtime.compiler.CompileLimits :=
  ⟨8#usize, 0#usize, 0#usize, 1#usize, 0#usize, 0#usize, 0#usize⟩

theorem eligible : Compiler.CompileEligible Unit bytes raw compileLimits 4 := by
  refine ⟨?_, ?_⟩
  · simp only [Slice.length, bytes, magicVersion, Slice.from_val, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, compileLimits, UScalar.ofNatCore_val_eq, Std.le_refl]
  · intro regions env tail certificate
    exact ⟨0, 0, 0, empty_demand certificate compileLimits (by decide)⟩

/-- Compiler completeness has satisfiable premises on the header-only module. -/
theorem compiled : ∃ executable,
    runtime.compiler.compile_with grantAll bytes compileLimits = .ok (.Ok executable) ∧
      CompilationCertificate bytes executable :=
  runtime.compiler.compile_with.complete grantAll grantAll_correct 4 (grantAll_available 4)
    bytes raw compileLimits valid eligible

/-- The compiled empty module can be passed to instantiation with every API
premise discharged, preserving the executable invariant and source outcome. -/
theorem compiled_instantiates : ∃ executable,
    runtime.compiler.compile_with grantAll bytes compileLimits = .ok (.Ok executable) ∧
    runtime.store.instantiate.Store.instantiate_with exampleMemory (trapHost exampleMemory)
      Platform.floatWitness grantAll freshStore executable (Slice.new runtime.Extern) ()
      ⦃ (result, after, platform) =>
        ExecutableInv exampleView
          (Store.installCode exampleCode freshStore.instances.length (Compiler.sourceFunctions raw)) after ∧
        InstantiationSourceOutcome exampleView exampleCode
          (Store.installCode exampleCode freshStore.instances.length (Compiler.sourceFunctions raw))
          freshStore executable (Slice.new runtime.Extern) raw () result after platform ⦄ := by
  obtain ⟨executable, accepted, certificate⟩ := compiled
  have contract := runtime.store.instantiate.Store.instantiate_with.spec exampleMemory
    (trapHost exampleMemory) Platform.floatWitness grantAll exampleView
    (Platform.vecMemory_laws grantAll grantAll_correct) grantAll_correct freshStore executable
    (Slice.new runtime.Extern) () exampleCode fresh_store_valid
    (by intro external member; cases member) bytes compileLimits accepted raw encoded.encoding
  refine ⟨executable, accepted, WP.spec_mono contract.2 ?_⟩
  rintro ⟨result, after, platform⟩ ⟨invariant, retained, extension, outcome, causes⟩
  exact ⟨invariant, outcome⟩

end EmptyModule

end Itasca.Runtime.Examples
