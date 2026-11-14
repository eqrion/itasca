import Itasca.Generated.FunsInstantiate
import Itasca.Runtime.Store.Invariant.OwnedInitializerErrors
import Itasca.Module.Env.Basic
import Itasca.Runtime.Store.Invariant.FunctionStaging
import Mathlib.Data.List.Forall2
import Itasca.Runtime.Spec.ModuleMembership
import Itasca.Runtime.Store.Invariant.CodeAgreement
import Itasca.Runtime.Compiler.Local.Source.SourceSegmentPrograms
import Itasca.Runtime.Store.Invariant.AllocatedMemoryLoop
import Itasca.Runtime.Store.Invariant.PrecommitError
import Itasca.Runtime.Compiler.Body.Relations.Executable.RecordingEmission
import Itasca.Runtime.Interp.Machine.Stateful.Prepare
import Itasca.Runtime.Interp.Machine.Coverage.OrdinaryHeads
import Itasca.Runtime.Interp.Machine.Simd.FrameStep
import Itasca.Runtime.Interp.Machine.Calls.CallStackEntry
import Itasca.Runtime.Store.Initialization.InitializerResourceCauses
import Itasca.Runtime.Store.Preparation.PreparationCalls
import Itasca.Runtime.Store.Invariant.Rollback
import Itasca.Runtime.Compiler.Local.Initializer

/-!
Sections, each formerly its own module: SourceExports, FunctionPayload, FunctionSourceAllocation, SourceFunctionAllocation, FunctionOrderLoop, ExecutableInstantiationCode, OwnedInitializerCauses, InternTypeCauses, FunctionTypeCauses, FunctionStagingCauses.
-/

/-! ## SourceExports -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std Itasca

/-- Runtime export decoding resolves the same namespace entry as the generated
module allocator, using the validated index and the completed instance map. -/
theorem export_source {M : Type} (store : runtime.store.Store M) (inst : runtime.store.ModuleInst)
    (entry : Itasca.metadata.Export) (ty : wasm_types.ExternType)
    (shape : InstanceShape store inst)
    (resolved : ModuleExternals.ExportResolves inst.module.module.env entry ty)
    (nameWf : wf_name (decodeName entry.name.val)) :
    fun_instexport (decodeInstance store inst).FUNCS (decodeInstance store inst).GLOBALS
      (decodeInstance store inst).TABLES (decodeInstance store inst).MEMS
      (ModuleElaboration.exportDecl (ModuleEnv.rawExport entry)) (decodeExport inst entry) := by
  obtain ⟨_, functionCount, tableCount, memoryCount, globalCount, _⟩ := shape
  cases desc : entry.desc with
  | Func index =>
    simp only [ModuleExternals.ExportResolves, desc] at resolved
    obtain ⟨bound, _⟩ := resolved
    have mapped : index.val < (inst.funcs.val.map (fun address => address.index.val)).length := by
      simp only [List.length_map]
      change index.val < inst.funcs.length
      rw [functionCount]
      exact bound
    have source := fun_instexport.fun_instexport_case_0
      (inst.funcs.val.map (fun address => address.index.val))
      (inst.globals.val.map (fun address => address.index.val))
      (inst.tables.val.map (fun address => address.index.val))
      (inst.memories.val.map (fun address => address.index.val))
      (decodeName entry.name.val) (.mk_uN index.val) (by simpa [proj_uN_0] using mapped) (by simpa [proj_uN_0] using mapped) (.exportinst_case_ _ _ nameWf)
    simpa only [decodeInstance, ModuleElaboration.exportDecl, ModuleEnv.rawExport,
      ModuleElaboration.exportIndex, decodeExport, desc, ← decode_name_source,
      List.getElem!_eq_getElem?_getD, List.getD, proj_uN_0,
      List.getElem?_eq_getElem mapped, Option.getD_some] using source
  | Global index =>
    simp only [ModuleExternals.ExportResolves, desc] at resolved
    obtain ⟨bound, _⟩ := resolved
    have mapped : index.val < (inst.globals.val.map (fun address => address.index.val)).length := by
      simp only [List.length_map]
      change index.val < inst.globals.length
      rw [globalCount]
      exact bound
    have source := fun_instexport.fun_instexport_case_1
      (inst.funcs.val.map (fun address => address.index.val))
      (inst.globals.val.map (fun address => address.index.val))
      (inst.tables.val.map (fun address => address.index.val))
      (inst.memories.val.map (fun address => address.index.val))
      (decodeName entry.name.val) (.mk_uN index.val) (by simpa [proj_uN_0] using mapped) (by simpa [proj_uN_0] using mapped) (.exportinst_case_ _ _ nameWf)
    simpa only [decodeInstance, ModuleElaboration.exportDecl, ModuleEnv.rawExport,
      ModuleElaboration.exportIndex, decodeExport, desc, ← decode_name_source,
      List.getElem!_eq_getElem?_getD, List.getD, proj_uN_0,
      List.getElem?_eq_getElem mapped, Option.getD_some] using source
  | Table index =>
    simp only [ModuleExternals.ExportResolves, desc] at resolved
    obtain ⟨bound, _⟩ := resolved
    have mapped : index.val < (inst.tables.val.map (fun address => address.index.val)).length := by
      simp only [List.length_map]
      change index.val < inst.tables.length
      rw [tableCount]
      exact bound
    have source := fun_instexport.fun_instexport_case_2
      (inst.funcs.val.map (fun address => address.index.val))
      (inst.globals.val.map (fun address => address.index.val))
      (inst.tables.val.map (fun address => address.index.val))
      (inst.memories.val.map (fun address => address.index.val))
      (decodeName entry.name.val) (.mk_uN index.val) (by simpa [proj_uN_0] using mapped) (by simpa [proj_uN_0] using mapped) (.exportinst_case_ _ _ nameWf)
    simpa only [decodeInstance, ModuleElaboration.exportDecl, ModuleEnv.rawExport,
      ModuleElaboration.exportIndex, decodeExport, desc, ← decode_name_source,
      List.getElem!_eq_getElem?_getD, List.getD, proj_uN_0,
      List.getElem?_eq_getElem mapped, Option.getD_some] using source
  | Memory index =>
    simp only [ModuleExternals.ExportResolves, desc] at resolved
    obtain ⟨bound, _⟩ := resolved
    have mapped : index.val < (inst.memories.val.map (fun address => address.index.val)).length := by
      simp only [List.length_map]
      change index.val < inst.memories.length
      rw [memoryCount]
      exact bound
    have source := fun_instexport.fun_instexport_case_3
      (inst.funcs.val.map (fun address => address.index.val))
      (inst.globals.val.map (fun address => address.index.val))
      (inst.tables.val.map (fun address => address.index.val))
      (inst.memories.val.map (fun address => address.index.val))
      (decodeName entry.name.val) (.mk_uN index.val) (by simpa [proj_uN_0] using mapped) (by simpa [proj_uN_0] using mapped) (.exportinst_case_ _ _ nameWf)
    simpa only [decodeInstance, ModuleElaboration.exportDecl, ModuleEnv.rawExport,
      ModuleElaboration.exportIndex, decodeExport, desc, ← decode_name_source,
      List.getElem!_eq_getElem?_getD, List.getD, proj_uN_0,
      List.getElem?_eq_getElem mapped, Option.getD_some] using source

/-- All source-ordered exports satisfy the generated allocator's resolutions. -/
theorem exports_source {M : Type} (store : runtime.store.Store M) (inst : runtime.store.ModuleInst)
    (shape : InstanceShape store inst)
    (valid : Itasca.ModuleEnv.Valid inst.module.module.env)
    (code : CodeInterpretation) (instanceIndex : Nat) (sourceSyntax : InstanceSyntax code instanceIndex inst) :
    List.Forall₂ (fun source allocated => fun_instexport
      (decodeInstance store inst).FUNCS (decodeInstance store inst).GLOBALS
      (decodeInstance store inst).TABLES (decodeInstance store inst).MEMS source allocated)
      (inst.module.module.env.exports.val.map (fun entry => ModuleElaboration.exportDecl (ModuleEnv.rawExport entry)))
      (inst.module.module.env.exports.val.map (decodeExport inst)) := by
  apply List.forall₂_map_left_iff.mpr
  apply List.forall₂_map_right_iff.mpr
  apply List.forall₂_same.mpr
  intro entry member
  obtain ⟨ty, resolved⟩ := valid.exports entry member
  exact export_source store inst entry ty shape resolved (sourceSyntax.exportNames entry member)

/-- The exact canonical source export list resolves to the decoded instance's
export records. -/
theorem exports_source_raw {M : Type} (store : runtime.store.Store M) (inst : runtime.store.ModuleInst)
    (shape : InstanceShape store inst)
    (valid : Itasca.ModuleEnv.Valid inst.module.module.env)
    (code : CodeInterpretation) (instanceIndex : Nat) (sourceSyntax : InstanceSyntax code instanceIndex inst)
    (raw : ModuleBinary.Module)
    (matched : ModuleElaboration.Matches inst.module.module.env inst.module.module.tail raw) :
    List.Forall₂ (fun source allocated => fun_instexport
      (decodeInstance store inst).FUNCS (decodeInstance store inst).GLOBALS
      (decodeInstance store inst).TABLES (decodeInstance store inst).MEMS source allocated)
      (raw.exports.map ModuleElaboration.exportDecl) (decodeInstance store inst).EXPORTS := by
  have exports := congrArg ModuleBinary.Module.exports matched.1
  simp only [ModuleElaboration.fromEnv] at exports
  have resolved := exports_source store inst shape valid code instanceIndex sourceSyntax
  rw [exports]
  simpa only [List.map_map, Function.comp_def, decodeInstance] using resolved
end Itasca.Runtime.Store

end

/-! ## FunctionPayload -/

section

/-!
Function allocation payload and its loop preservation. Shared certificates remain independent of the instantiation construction.
-/

/-! ## Function Payload -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Exact source ordinal and interned type index stored in a freshly allocated
Wasm function. The function body is supplied later by the compiled module's
source interpretation. -/
def FunctionAllocatedAt (seed : runtime.store.ModuleInst) (instanceIndex : Usize)
    (ordinal : Nat) (function : runtime.store.FuncInst) : Prop :=
  ∃ index : Usize, index.val = ordinal ∧ function.code = .Wasm instanceIndex index ∧
    ∃ typeIndex, seed.module.module.env.func_type_indices.val[ordinal]? = some typeIndex ∧
      seed.types.val[typeIndex.val]? = some function.signature

def FunctionPayload {M : Type} (before after : runtime.store.Store M)
    (seed : runtime.store.ModuleInst) (instanceIndex : Usize) (count : Nat) : Prop :=
  ∃ fresh, after.funcs.val = before.funcs.val ++ fresh ∧
    List.Forall₂ (FunctionAllocatedAt seed instanceIndex) (List.range count) fresh

theorem FunctionPayload.initial {M : Type} (store : runtime.store.Store M)
    (seed : runtime.store.ModuleInst) (instanceIndex : Usize) :
    FunctionPayload store store seed instanceIndex 0 := ⟨[], by simp, .nil⟩

theorem FunctionStageEffect.payload {M : Type} {before store : runtime.store.Store M}
    {inst seed : runtime.store.ModuleInst} {instanceIndex index signature out}
    (effect : FunctionStageEffect store inst instanceIndex index signature out)
    (success : out.1 = .Ok ())
    (payload : FunctionPayload before store seed instanceIndex index.val)
    (source : inst.module = seed.module) (types : inst.types = seed.types)
    (bound : index.val < inst.module.module.env.func_type_indices.val.length)
    (typeBound : inst.module.module.env.func_type_indices.val[index.val].val < inst.types.val.length)
    (signatureEq : signature = inst.types.val[inst.module.module.env.func_type_indices.val[index.val].val]) :
    FunctionPayload before out.2.1 seed instanceIndex (index.val + 1) := by
  rcases effect with ⟨error, rfl⟩ | ⟨functions, addresses, appended, mapped, room, rfl⟩
  · simp at success
  · obtain ⟨fresh, stored, paired⟩ := payload
    refine ⟨fresh ++ [{signature, code := .Wasm instanceIndex index}], ?_, ?_⟩
    · simpa only [stored, List.append_assoc] using appended
    · rw [List.range_succ]
      apply List.rel_append paired
      refine .cons ⟨index, rfl, rfl, inst.module.module.env.func_type_indices.val[index.val], ?_, ?_⟩ .nil
      · simpa only [source] using List.getElem?_eq_getElem bound
      · simpa only [types, signatureEq] using List.getElem?_eq_getElem typeBound
end Itasca.Runtime.Store

end

/-! ## Function Payload Loop -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- The actual defined-function allocation loop establishes complete issued
function maps, while retaining all old store objects. The exact helper effect
also records each function's canonical signature and source function index. -/
theorem function_payload_loop {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (seed inst : runtime.store.ModuleInst)
    (instanceIndex start : Usize)
    (startBound : start.val ≤ seed.module.module.env.func_type_indices.val.length)
    (changed : store = {before with funcs := store.funcs})
    (instChanged : inst = {seed with funcs := inst.funcs})
    (retained : StagedPrefix before store) (objectBound : objectCount store ≤ Usize.max)
    (typeBounds : ∀ idx ∈ seed.module.module.env.func_type_indices.val, idx.val < seed.types.length)
    (issued : ∀ address ∈ inst.funcs.val, address.index.val < store.funcs.length)
    (count : inst.funcs.length = seed.funcs.length + start.val)
    (capacity : seed.funcs.length + seed.module.module.env.func_type_indices.val.length ≤ Usize.max)
    (payload : FunctionPayload before store seed instanceIndex start.val) :
    runtime.store.instantiate.Store.prepare_instance_loop4 memory allocator store (.Ok ()) start inst instanceIndex
      ⦃ out => ∃ after next status, out = typeParts after status next ∧
        after = {before with funcs := after.funcs} ∧ next = {seed with funcs := next.funcs} ∧
        StagedPrefix before after ∧ objectCount after ≤ Usize.max ∧
        (∀ address ∈ next.funcs.val, address.index.val < after.funcs.length) ∧
        (status = .Ok () → next.funcs.length = seed.funcs.length + seed.module.module.env.func_type_indices.val.length ∧
          FunctionPayload before after seed instanceIndex seed.module.module.env.func_type_indices.val.length) ⦄ := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop4
  apply loop.spec_decr_nat (fun state => seed.module.module.env.func_type_indices.val.length - state.2.2.1.val)
    (fun state => state.1 = {before with funcs := state.1.funcs} ∧
      state.2.2.2 = {seed with funcs := state.2.2.2.funcs} ∧ StagedPrefix before state.1 ∧
      objectCount state.1 ≤ Usize.max ∧
      (∀ address ∈ state.2.2.2.funcs.val, address.index.val < state.1.funcs.length) ∧
      state.2.2.1.val ≤ seed.module.module.env.func_type_indices.val.length ∧
      (state.2.1 = .Ok () → state.2.2.2.funcs.length = seed.funcs.length + state.2.2.1.val ∧
        FunctionPayload before state.1 seed instanceIndex state.2.2.1.val))
  · rintro ⟨current, status, index, currentInst⟩ ⟨currentChanged, mapChanged, prefixStore, bound, currentIssued, indexBound, counting⟩
    dsimp only at currentChanged mapChanged prefixStore bound currentIssued indexBound counting ⊢
    have source : currentInst.module = seed.module := by
      have eq := congrArg runtime.store.ModuleInst.module mapChanged
      exact eq
    have types : currentInst.types = seed.types := by
      have eq := congrArg runtime.store.ModuleInst.types mapChanged
      exact eq
    unfold runtime.store.instantiate.Store.prepare_instance_loop4.body
    simp only [runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.func_type_indices, source, bind_ok]
    split
    · rename_i more
      have within : index.val < seed.module.module.env.func_type_indices.val.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, currentInst, .Err error, by simp [typeParts, source], currentChanged,
          mapChanged, prefixStore, bound, currentIssued, by simp⟩
      | Ok value =>
        cases value
        obtain ⟨size, currentPayload⟩ := counting rfl
        have actualBound : index.val < currentInst.module.module.env.func_type_indices.val.length := by simpa only [source] using within
        have typeBound : currentInst.module.module.env.func_type_indices.val[index.val].val < currentInst.types.val.length := by
          simpa only [source, types] using typeBounds _ (List.getElem_mem within)
        have room : currentInst.funcs.length < Usize.max := by omega
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        step with add_instance_function_effect memory allocator law current currentInst instanceIndex index
          bound actualBound typeBound room as ⟨status, after, nextInst, effect⟩
        obtain ⟨afterChanged, nextChanged, prefixNext, nextBound, _⟩ := effect.context bound
        have afterExact : after = {before with funcs := after.funcs} := by
          calc
            after = {current with funcs := after.funcs} := afterChanged
            _ = _ := by rw [currentChanged]
        have nextExact : nextInst = {seed with funcs := nextInst.funcs} := by
          calc
            nextInst = {currentInst with funcs := nextInst.funcs} := nextChanged
            _ = _ := by rw [mapChanged]
        step as ⟨next, increment⟩
        refine ⟨afterExact, nextExact, prefixStore.trans prefixNext, nextBound,
          effect.issued currentIssued, ?_, ?_, ?_⟩
        · omega
        · intro success
          have appended := effect.count success
          dsimp only at appended
          constructor
          · omega
          · rw [increment]
            exact effect.payload success currentPayload source types actualBound typeBound rfl
        · omega
    · rename_i stopped
      have atEnd : index.val = seed.module.module.env.func_type_indices.val.length := by
        simp [alloc.vec.Vec.deref] at stopped
        omega
      simp only [WP.spec_ok]
      refine ⟨current, currentInst, status, by simp [typeParts, source], currentChanged,
        mapChanged, prefixStore, bound, currentIssued, ?_⟩
      intro success
      simpa only [atEnd] using counting success
  · exact ⟨changed, instChanged, retained, objectBound, issued, startBound, fun _ => ⟨count, payload⟩⟩

end Itasca.Runtime.Store

end

end

/-! ## FunctionSourceAllocation -/

section

/-!
Decoded function allocation and source payload lists. The per-function allocation witness establishes the ordered source function-instance list.
-/

/-! ## Function Allocation Decode -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem FunctionAllocatedAt.decode {M : Type}
    {seed : runtime.store.ModuleInst} {instanceIndex : Usize} {ordinal : Nat}
    {function : runtime.store.FuncInst}
    (allocated : FunctionAllocatedAt seed instanceIndex ordinal function)
    (code : CodeInterpretation) (store : runtime.store.Store M) (inst : runtime.store.ModuleInst)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (types : inst.types = seed.types)
    (source : func) (typeIndex : U32)
    (indexFound : seed.module.module.env.func_type_indices.val[ordinal]? = some typeIndex)
    (sourceIndex : Spec.allocationFunctionIndex source = typeIndex.val)
    (sourceCode : code instanceIndex.val inst.module ordinal = funccode_func source) :
    decodeFunction code store function = Spec.allocationFunction (decodeInstance store inst) source := by
  obtain ⟨index, ordinalEq, encoded, rawIndex, rawFound, signatureFound⟩ := allocated
  have same : rawIndex = typeIndex := Option.some.inj (rawFound.symm.trans indexFound)
  subst rawIndex
  simp only [decodeFunction, encoded, found, ordinalEq, sourceCode, Spec.allocationFunction,
    decodeInstance, sourceIndex, types, List.getElem!_eq_getElem?_getD,
    List.getElem?_map, signatureFound, Option.map_some, Option.getD_some]

end Itasca.Runtime.Store

end

/-! ## Function Source Allocation -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Exact source-ordinal allocation and the installed body interpretation give
all newly allocated source function instances, in declaration order. -/
theorem FunctionPayload.source_list {M : Type} {before after : runtime.store.Store M}
    {seed : runtime.store.ModuleInst} {instanceIndex : Usize}
    (sources : List func)
    (payload : FunctionPayload before after seed instanceIndex sources.length)
    (code : CodeInterpretation) (store : runtime.store.Store M) (inst : runtime.store.ModuleInst)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (types : inst.types = seed.types)
    (typeIndices : List.Forall₂ (fun index source => index.val = Spec.allocationFunctionIndex source)
      seed.module.module.env.func_type_indices.val sources)
    (sourceCode : ∀ index source, sources[index]? = some source →
      code instanceIndex.val inst.module index = funccode_func source) :
    after.funcs.val.map (decodeFunction code store) = before.funcs.val.map (decodeFunction code store) ++
      sources.map (Spec.allocationFunction (decodeInstance store inst)) := by
  obtain ⟨fresh, stored, paired⟩ := payload
  rw [stored, List.map_append]
  congr 1
  have length : fresh.length = sources.length := by simpa only [List.length_range] using paired.length_eq.symm
  apply List.ext_getElem
  · simpa only [List.length_map] using length
  · intro index leftBound rightBound
    have sourceBound : index < sources.length := by simpa only [List.length_map] using rightBound
    have freshBound : index < fresh.length := by simpa only [List.length_map] using leftBound
    have rawBound : index < seed.module.module.env.func_type_indices.val.length := by
      rw [typeIndices.length_eq]
      exact sourceBound
    have allocated : FunctionAllocatedAt seed instanceIndex index fresh[index] := by
      simpa only [List.get_eq_getElem, List.getElem_range] using paired.get (by simpa using sourceBound) freshBound
    have sourceIndex : Spec.allocationFunctionIndex sources[index] = seed.module.module.env.func_type_indices.val[index].val := by
      have matching := typeIndices.get rawBound sourceBound
      simpa only [List.get_eq_getElem] using matching.symm
    simp only [List.getElem_map]
    exact allocated.decode code store inst found types sources[index]
      seed.module.module.env.func_type_indices.val[index] (List.getElem?_eq_getElem rawBound)
      sourceIndex (sourceCode index sources[index] (List.getElem?_eq_getElem sourceBound))
end Itasca.Runtime.Store

end

end

/-! ## SourceFunctionAllocation -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std Itasca

/-- Independent source declaration order agrees with the actual raw type-index
vector; equal section counts exclude zip truncation. -/
theorem source_function_type_indices (indices : List U32) (entries : List ModuleBinary.Code)
    (lengths : indices.length = entries.length) :
    List.Forall₂ (fun index source => index.val = Spec.allocationFunctionIndex source)
      indices (List.zipWith CodeEntry.function indices entries) := by
  induction indices generalizing entries with
  | nil => cases entries <;> simp_all
  | cons index indices ih =>
    cases entries with
    | nil => simp at lengths
    | cons entry entries =>
      have tail : indices.length = entries.length := by simpa only [List.length_cons, Nat.add_right_cancel_iff] using lengths
      exact .cons rfl (ih entries tail)

@[simp] theorem source_function_code (source : func) : Compiler.functionCode source = funccode_func source := by
  cases source <;> rfl

theorem installed_source_function (code : CodeInterpretation) (instanceIndex : Nat)
    (module : runtime.compiler.ExecutableModule) (raw : ModuleBinary.Module)
    (index : Nat) (source : func)
    (found : (List.zipWith CodeEntry.function raw.functions raw.codes)[index]? = some source) :
    installCode code instanceIndex (Compiler.sourceFunctions raw) instanceIndex module index = funccode_func source := by
  apply install_code_lookup
  simp only [Compiler.source_functions_eq, List.getElem?_map, found, Option.map_some, source_function_code]

theorem canonical_function_payload_decode {M : Type} {before after : runtime.store.Store M}
    {seed : runtime.store.ModuleInst} {instanceIndex : Usize}
    (raw : ModuleBinary.Module)
    (lengths : raw.functions.length = raw.codes.length)
    (indices : seed.module.module.env.func_type_indices.val = raw.functions)
    (payload : FunctionPayload before after seed instanceIndex raw.functions.length)
    (code : CodeInterpretation) (store : runtime.store.Store M) (inst : runtime.store.ModuleInst)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (types : inst.types = seed.types) :
    after.funcs.val.map (decodeFunction (installCode code instanceIndex.val (Compiler.sourceFunctions raw)) store) =
      before.funcs.val.map (decodeFunction (installCode code instanceIndex.val (Compiler.sourceFunctions raw)) store) ++
      (List.zipWith CodeEntry.function raw.functions raw.codes).map
        (Spec.allocationFunction (decodeInstance store inst)) := by
  apply FunctionPayload.source_list _ ?_ _ store inst found types ?_ ?_
  · simpa only [List.length_zipWith, lengths, Nat.min_self] using payload
  · rw [indices]
    exact source_function_type_indices raw.functions raw.codes lengths
  · exact installed_source_function code instanceIndex.val inst.module raw
end Itasca.Runtime.Store

end

/-! ## FunctionOrderLoop -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- The actual defined-function allocation loop establishes complete issued
function maps, while retaining all old store objects. The exact helper effect
also records each function's canonical signature and source function index. -/
theorem function_order_loop {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (seed inst : runtime.store.ModuleInst)
    (instanceIndex start : Usize)
    (startBound : start.val ≤ seed.module.module.env.func_type_indices.val.length)
    (changed : store = {before with funcs := store.funcs})
    (instChanged : inst = {seed with funcs := inst.funcs})
    (retained : StagedPrefix before store) (objectBound : objectCount store ≤ Usize.max)
    (typeBounds : ∀ idx ∈ seed.module.module.env.func_type_indices.val, idx.val < seed.types.length)
    (issued : ∀ address ∈ inst.funcs.val, address.index.val < store.funcs.length)
    (count : inst.funcs.length = seed.funcs.length + start.val)
    (capacity : seed.funcs.length + seed.module.module.env.func_type_indices.val.length ≤ Usize.max)
    (base : Nat) (initial : List Nat)
    (ordered : AddressOrder base initial store.funcs.length (inst.funcs.val.map fun address => address.index.val)) :
    runtime.store.instantiate.Store.prepare_instance_loop4 memory allocator store (.Ok ()) start inst instanceIndex
      ⦃ out => ∃ after next status, out = typeParts after status next ∧
        after = {before with funcs := after.funcs} ∧ next = {seed with funcs := next.funcs} ∧
        StagedPrefix before after ∧ objectCount after ≤ Usize.max ∧
        AddressOrder base initial after.funcs.length (next.funcs.val.map fun address => address.index.val) ∧
        (∀ address ∈ next.funcs.val, address.index.val < after.funcs.length) ∧
        (status = .Ok () → next.funcs.length = seed.funcs.length + seed.module.module.env.func_type_indices.val.length) ⦄ := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop4
  apply loop.spec_decr_nat (fun state => seed.module.module.env.func_type_indices.val.length - state.2.2.1.val)
    (fun state => state.1 = {before with funcs := state.1.funcs} ∧
      state.2.2.2 = {seed with funcs := state.2.2.2.funcs} ∧ StagedPrefix before state.1 ∧
      objectCount state.1 ≤ Usize.max ∧
      AddressOrder base initial state.1.funcs.length (state.2.2.2.funcs.val.map fun address => address.index.val) ∧
      (∀ address ∈ state.2.2.2.funcs.val, address.index.val < state.1.funcs.length) ∧
      state.2.2.1.val ≤ seed.module.module.env.func_type_indices.val.length ∧
      (state.2.1 = .Ok () → state.2.2.2.funcs.length = seed.funcs.length + state.2.2.1.val))
  · rintro ⟨current, status, index, currentInst⟩ ⟨currentChanged, mapChanged, prefixStore, bound, currentOrder, currentIssued, indexBound, counting⟩
    dsimp only at currentChanged mapChanged prefixStore bound currentOrder currentIssued indexBound counting ⊢
    have source : currentInst.module = seed.module := by
      have eq := congrArg runtime.store.ModuleInst.module mapChanged
      exact eq
    have types : currentInst.types = seed.types := by
      have eq := congrArg runtime.store.ModuleInst.types mapChanged
      exact eq
    unfold runtime.store.instantiate.Store.prepare_instance_loop4.body
    simp only [runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.func_type_indices, source, bind_ok]
    split
    · rename_i more
      have within : index.val < seed.module.module.env.func_type_indices.val.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, currentInst, .Err error, by simp [typeParts, source], currentChanged,
          mapChanged, prefixStore, bound, currentOrder, currentIssued, by simp⟩
      | Ok value =>
        cases value
        have size := counting rfl
        have actualBound : index.val < currentInst.module.module.env.func_type_indices.val.length := by simpa only [source] using within
        have typeBound : currentInst.module.module.env.func_type_indices.val[index.val].val < currentInst.types.val.length := by
          simpa only [source, types] using typeBounds _ (List.getElem_mem within)
        have room : currentInst.funcs.length < Usize.max := by omega
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        step with add_instance_function_effect memory allocator law current currentInst instanceIndex index
          bound actualBound typeBound room as ⟨status, after, nextInst, effect⟩
        obtain ⟨afterChanged, nextChanged, prefixNext, nextBound, _⟩ := effect.context bound
        have afterExact : after = {before with funcs := after.funcs} := by
          calc
            after = {current with funcs := after.funcs} := afterChanged
            _ = _ := by rw [currentChanged]
        have nextExact : nextInst = {seed with funcs := nextInst.funcs} := by
          calc
            nextInst = {currentInst with funcs := nextInst.funcs} := nextChanged
            _ = _ := by rw [mapChanged]
        step as ⟨next, increment⟩
        refine ⟨afterExact, nextExact, prefixStore.trans prefixNext, nextBound, effect.address_order currentOrder,
          effect.issued currentIssued, ?_, ?_, ?_⟩
        · omega
        · intro success
          have appended := effect.count success
          dsimp only at appended
          omega
        · omega
    · rename_i stopped
      have atEnd : index.val = seed.module.module.env.func_type_indices.val.length := by
        simp [alloc.vec.Vec.deref] at stopped
        omega
      simp only [WP.spec_ok]
      refine ⟨current, currentInst, status, by simp [typeParts, source], currentChanged,
        mapChanged, prefixStore, bound, currentOrder, currentIssued, ?_⟩
      intro success
      simpa only [atEnd] using counting success
  · exact ⟨changed, instChanged, retained, objectBound, ordered, issued, startBound, fun _ => count⟩

end Itasca.Runtime.Store

end

/-! ## ExecutableInstantiationCode -/

section

/-!
Executable function certificates after publication. Compiled function definitions establish the executable-code component retained by instantiation.
-/

/-! ## Executable Compiled Definitions -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
open Itasca.ModuleEnv

/-- Publication of a fresh instance turns staged source-index metadata into
complete compiled-function coverage. Existing functions retain their old
certificates; fresh functions use the compiler's module certificate and the
actual canonical type/function maps. -/
theorem executable_compiled_functions_publish {M : Type} {view : M → Slice U8}
    (before after : runtime.store.Store M) (oldCode : CodeInterpretation)
    (shape : Shape view before) (retained : StagedPrefix before after)
    (oldCompiled : Interp.Machine.CompiledFunctions oldCode before)
    (inst : runtime.store.ModuleInst) (sources : List funccode)
    (found : after.instances.val[before.instances.len.val]? = some inst)
    (certificate : Compiler.ExecutableModuleFunctions inst.module sources)
    (dataCount : ∀ count, inst.module.module.env.data_count = some count →
      count.val = inst.module.module.tail.data.val.length)
    {tables memories} (cache : Cache inst.module.module.env tables memories)
    (entries : TypeEntries after inst.module.module.env.types.val inst.types.val)
    (table : Interp.FunctionTable after inst (inst.module.module.env.func_types.val.map decodeFuncType))
    (staged : StagedFunctionSignatures before after before.instances.len
      (inst.module.module.env.func_types.val.drop (importedFuncs inst.module.module.env.imports.val).length)) :
    Interp.Machine.CompiledFunctions (installCode oldCode before.instances.len.val sources) after := by
  intro function present
  rcases staged function present with old | ⟨index, bound, encoded, signatureFound⟩
  · exact supported_function_compiled_prefix shape retained (install_code_agrees before oldCode sources) (oldCompiled function old)
  · intro instanceIndex functionIndex defined
    obtain ⟨sameInstance, sameFunction⟩ := runtime.store.FuncCode.Wasm.inj (defined.symm.trans encoded)
    subst instanceIndex
    subst functionIndex
    let imported := (importedFuncs inst.module.module.env.imports.val).length
    let definedTypes := inst.module.module.env.func_types.val.drop imported
    have resolves : List.Forall₂ (Resolves inst.module.module.env.types.val)
        inst.module.module.env.func_type_indices.val definedTypes := by
      simpa only [definedTypes, imported, List.drop_left] using List.forall₂_drop imported cache.funcs
    have sourceBound : index.val < inst.module.module.env.func_type_indices.val.length := by
      rw [resolves.length_eq]
      exact bound
    let typeIndex := inst.module.module.env.func_type_indices.val[index.val]
    have sourceIndex : inst.module.module.env.func_type_indices.val[index.val]? = some typeIndex :=
      List.getElem?_eq_getElem sourceBound
    obtain ⟨compiled, source, compiledFound, sourceFound, typeIndexEq, signature,
      declared, body, epilogue, typeFound, sourceEq, functionCode⟩ := certificate.entry index.val typeIndex sourceIndex
    have resolved := resolves.get sourceBound bound
    simp only [List.get_eq_getElem] at resolved
    obtain ⟨typeBound, resolvedType⟩ := resolved
    have actualType : inst.module.module.env.types.val[typeIndex.val]? = some definedTypes[index.val] := by
      rw [List.getElem?_eq_getElem typeBound, resolvedType]
    have signatureEq : signature = definedTypes[index.val] := Option.some.inj (typeFound.symm.trans actualType)
    subst signature
    refine ⟨inst, compiled, definedTypes[index.val], declared, body, epilogue,
      found, compiledFound, signatureFound, ?_, table, type_entries_decoded entries, Compiler.ExecutableFunctionCode.complete_module functionCode dataCount⟩
    · rw [install_code_lookup oldCode before.instances.len.val sources inst.module index.val source sourceFound]
      simpa only [typeIndexEq] using sourceEq

end Itasca.Runtime.Store

end

/-! ## Executable Instantiation Code -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std Itasca.ModuleEnv
/-- The compiler's syntactic module certificate supplies fresh function bodies;
existing bodies keep their old certificate. Charging instance items changes no
field involved in code interpretation or function lookup. -/
theorem InstantiationCode.executable_compiled {M : Type} {view : M → Slice U8}
    {before ready : runtime.store.Store M} {inst : runtime.store.ModuleInst}
    (code : InstantiationCode before ready inst) (oldCode : CodeInterpretation)
    (shape : Shape view before) (oldCompiled : Interp.Machine.CompiledFunctions oldCode before)
    (found : ready.instances.val[before.instances.len.val]? = some inst)
    (sources : List funccode) (certificate : Compiler.ExecutableModuleFunctions inst.module sources)
    (dataCount : ∀ count, inst.module.module.env.data_count = some count →
      count.val = inst.module.module.tail.data.val.length)
    {tables memories} (cache : Cache inst.module.module.env tables memories) :
    Interp.Machine.CompiledFunctions (installCode oldCode before.instances.len.val sources) ready := by
  obtain ⟨staged, count, rfl, retained, entries, table, signatures⟩ := code
  have compiled := executable_compiled_functions_publish before staged oldCode shape retained oldCompiled inst sources
    found certificate dataCount cache entries table signatures
  exact compiled

end Itasca.Runtime.Store

end

end

/-! ## OwnedInitializerCauses -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)
theorem eval_const_owned_resource_causes (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex function : Usize)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType) (words : List U64)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hc : inst.module.functions.val[function.val]? = some code)
    (compiled : Compiler.InitializerCode code expr ty)
    (resolved : Interp.InitializerResolution store inst expr ty words)
    (bindings : InitializerBindings store inst) :
    runtime.interp.eval_const memory hooks floats allocator store platform instIndex function ty
      ⦃ out => out.2.1 = store ∧ out.2.2 = platform ∧
        (∀ value, out.1 = .Ok value → ValueInStore store value ∧ Interp.rawType value = ty) ∧
        (∀ error, out.1 = .Err error → Interp.SyntheticPreparationCause allocator store code error) ⦄ := by
  obtain ⟨out, called, sameStore, sameHost, values⟩ := WP.spec_imp_exists
    (eval_const_owned memory hooks floats allocator law store platform instIndex function
      inst code expr ty words hi hc compiled resolved bindings)
  have errors := eval_const_resource_causes memory hooks floats allocator law store platform instIndex function
    inst code expr ty words hi hc compiled resolved (initializer_reference_bound resolved bindings)
  rw [called] at errors
  simp only [WP.spec_ok] at errors
  exact WP.exists_imp_spec ⟨out,called,sameStore,sameHost,values,errors.2.2.2⟩
end Itasca.Runtime.Store

end

/-! ## InternTypeCauses -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Concrete thresholds and reached allocator requests for creating one new
canonical signature. Existing signatures return before these checks. -/
def TypeInternResourceCause {M A : Type} (allocator : runtime.platform.Alloc A)
    (store : runtime.store.Store M) (ty : Itasca.wasm_types.FuncType) : runtime.ExecError → Prop
  | .Exhausted .Objects =>
      Usize.max < ty.params.length + ty.results.length ∨
      store.limits.max_signature_values.val < store.signature_values.val + ty.params.length + ty.results.length ∨
      store.limits.max_objects.val ≤ objectCount store
  | .Exhausted .Allocation =>
      allocator.reserve store.types 1#usize = .ok (false,store.types) ∨ TypeCopyRefusal allocator ty
  | _ => False

theorem intern_type_resource_causes {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (ty : Itasca.wasm_types.FuncType)
    (bound : objectCount store ≤ Usize.max) :
    runtime.store.Store.intern_type memory allocator store ty ⦃ out => ∀ error, out.1 = .Err error →
      out.2 = store ∧ ty ∉ store.types.val ∧ TypeInternResourceCause allocator store ty error ⦄ := by
  obtain ⟨index,run,indexBound,priorTypes,found⟩ :=
    WP.spec_imp_exists (runtime.store.Store.find_type.spec memory store ty)
  unfold runtime.store.Store.intern_type
  rw [run]
  simp only [bind_ok]
  split
  · simp
  · rename_i notLess
    have indexEq : index.val = store.types.length := by scalar_tac
    have absent : ty ∉ store.types.val := by simpa [indexEq] using priorTypes
    step as ⟨count,countEq⟩
    cases count with
    | none =>
      simp [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        TypeInternResourceCause,absent]
      exact Or.inl (by scalar_tac)
    | some count =>
      simp [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch]
      step with within_spec store.signature_values count store.limits.max_signature_values as ⟨fits,fitsEq⟩
      rw [fitsEq]
      split
      · rename_i budget
        step with room_spec memory store bound as ⟨room,roomEq⟩
        rw [roomEq]
        by_cases space : objectCount store < store.limits.max_objects.val
        · simp only [if_pos space]
          simp [core.result.Result.Insts.CoreOpsTry.branch]
          obtain ⟨answer,wrapped,called⟩ := reserve_with_cause allocator law store.types 1#usize
          rw [wrapped]
          cases answer
          · simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              TypeInternResourceCause,absent,called]
          · simp
            step with copy_type_resource_causes allocator law ty as ⟨copied,effect⟩
            rcases effect with copiedEq | ⟨failed,refusal⟩
            · rw [copiedEq]
              simp [core.result.Result.Insts.CoreOpsTry.branch]
              have room : store.types.length < Usize.max := by unfold objectCount at space; scalar_tac
              step
              step
              simp
            · simp [failed,core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                TypeInternResourceCause,absent,refusal]
        · simp [space,core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            TypeInternResourceCause,absent]
          exact Or.inr (Or.inr (by omega))
      · simp [TypeInternResourceCause,absent]
        exact Or.inr (Or.inl (by scalar_tac))
end Itasca.Runtime.Store

end

/-! ## FunctionTypeCauses -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- Defined function publication has only the object-count gate and the exact
store function-vector reservation as resource rejection sites. -/
def FunctionAllocationCause {M A : Type} (allocator : runtime.platform.Alloc A)
    (store : runtime.store.Store M) : runtime.ExecError → Prop
  | .Exhausted .Objects => store.limits.max_objects.val ≤ objectCount store
  | .Exhausted .Allocation => allocator.reserve store.funcs 1#usize = .ok (false,store.funcs)
  | _ => False

theorem add_function_resource_cause {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (instanceIndex index : Usize)
    (bound : objectCount store ≤ Usize.max) (error : runtime.ExecError)
    (after : runtime.store.Store M) (next : runtime.store.ModuleInst)
    (run : runtime.store.instantiate.Store.add_instance_function memory allocator store inst instanceIndex index =
      .ok (.Err error,after,next)) :
    after = store ∧ next = inst ∧ FunctionAllocationCause allocator store error := by
  obtain ⟨status,called,room⟩ := WP.spec_imp_exists (room_spec memory store bound)
  rw [room] at called
  unfold runtime.store.instantiate.Store.add_instance_function at run
  rw [called] at run
  by_cases space : objectCount store < store.limits.max_objects.val
  · simp only [if_pos space,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at run
    obtain ⟨answer,reserved,refusal⟩ := reserve_with_cause allocator law store.funcs 1#usize
    rw [reserved] at run
    cases answer
    · simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at run
      obtain ⟨rfl,rfl,rfl⟩ := run
      exact ⟨rfl,rfl,refusal⟩
    · simp [core.result.Result.Insts.CoreOpsTry.branch,
        runtime.compiler.ExecutableModule.env.eq,Itasca.metadata.Module.impl.env,Itasca.metadata.Env.impl.func_type_indices] at run
      obtain ⟨sourceType,read,run⟩ := normal_bind_exists _ _ _ run
      simp only [lift,bind_ok] at run
      obtain ⟨signature,read,run⟩ := normal_bind_exists _ _ _ run
      obtain ⟨functions,pushed,run⟩ := normal_bind_exists _ _ _ run
      obtain ⟨addresses,mapped,run⟩ := normal_bind_exists _ _ _ run
      simp at run
  · simp [space,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at run
    obtain ⟨rfl,rfl,rfl⟩ := run
    exact ⟨rfl,rfl,by simpa [FunctionAllocationCause] using (Nat.le_of_not_gt space)⟩

/-- Type staging exposes the actual selected source signature and the exact
interning refusal, including absence from the pre-existing canonical pool. -/
theorem add_type_resource_cause {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (index : Usize)
    (bound : objectCount store ≤ Usize.max) (error : runtime.ExecError)
    (after : runtime.store.Store M) (next : runtime.store.ModuleInst)
    (run : runtime.store.instantiate.Store.add_instance_type memory allocator store inst index = .ok (.Err error,after,next)) :
    ∃ ty, inst.module.module.env.types.val[index.val]? = some ty ∧
      after = store ∧ next = inst ∧ ty ∉ store.types.val ∧ TypeInternResourceCause allocator store ty error := by
  unfold runtime.store.instantiate.Store.add_instance_type at run
  simp only [runtime.compiler.ExecutableModule.env.eq,Itasca.metadata.Module.impl.env,Itasca.metadata.Env.impl.types,bind_ok] at run
  obtain ⟨ty,read,run⟩ := normal_bind_exists _ _ _ run
  have found : inst.module.module.env.types.val[index.val]? = some ty := by
    unfold Slice.index_usize at read
    split at read
    · simp at read
    · rename_i value found
      simp only [Result.ok.injEq] at read
      subst value
      simpa [alloc.vec.Vec.deref] using found
  obtain ⟨⟨status,staged⟩,interned,run⟩ := normal_bind_exists _ _ _ run
  have effect := intern_type_resource_causes memory allocator law store ty bound
  rw [interned,WP.spec_ok] at effect
  cases status with
  | Ok canonical =>
    simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at run
    obtain ⟨addresses,pushed,run⟩ := normal_bind_exists _ _ _ run
    simp at run
  | Err rejected =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at run
    obtain ⟨rfl,rfl,rfl⟩ := run
    obtain ⟨sameStore,absent,cause⟩ := effect rejected rfl
    exact ⟨ty,found,sameStore,rfl,absent,cause⟩
end Itasca.Runtime.Store

end

/-! ## FunctionStagingCauses -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

abbrev functionStageCall {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (instanceIndex : Usize)
    (state : runtime.store.Store M × runtime.store.ModuleInst) (index : Usize) :=
  runtime.store.instantiate.Store.add_instance_function memory allocator state.1 state.2 instanceIndex index

def FunctionStagingCause {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (store : runtime.store.Store M) (inst : runtime.store.ModuleInst)
    (instanceIndex start : Usize) (error : runtime.ExecError) : Prop :=
  ∃ current currentInst index,
    PreparationCalls (functionStageCall memory allocator instanceIndex) (store,inst) start (current,currentInst) index ∧
    runtime.store.instantiate.Store.add_instance_function memory allocator current currentInst instanceIndex index = .ok (.Err error,current,currentInst) ∧
    FunctionAllocationCause allocator current error

/-- The actual defined-function allocation loop establishes complete issued
function maps, while retaining all old store objects. The exact helper effect
also records each function's canonical signature and source function index. -/
theorem function_staging_resource_loop {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (seed inst : runtime.store.ModuleInst)
    (instanceIndex start : Usize)
    (startBound : start.val ≤ seed.module.module.env.func_type_indices.val.length)
    (changed : store = {before with funcs := store.funcs})
    (instChanged : inst = {seed with funcs := inst.funcs})
    (retained : StagedPrefix before store) (objectBound : objectCount store ≤ Usize.max)
    (typeBounds : ∀ idx ∈ seed.module.module.env.func_type_indices.val, idx.val < seed.types.length)
    (issued : ∀ address ∈ inst.funcs.val, address.index.val < store.funcs.length)
    (count : inst.funcs.length = seed.funcs.length + start.val)
    (capacity : seed.funcs.length + seed.module.module.env.func_type_indices.val.length ≤ Usize.max) :
    runtime.store.instantiate.Store.prepare_instance_loop4 memory allocator store (.Ok ()) start inst instanceIndex
      ⦃ out => ∃ after next status, out = typeParts after status next ∧
        after = {before with funcs := after.funcs} ∧ next = {seed with funcs := next.funcs} ∧
        StagedPrefix before after ∧ objectCount after ≤ Usize.max ∧
        (∀ address ∈ next.funcs.val, address.index.val < after.funcs.length) ∧
        (status = .Ok () → next.funcs.length = seed.funcs.length + seed.module.module.env.func_type_indices.val.length) ∧
        (∀ error, status = .Err error → FunctionStagingCause memory allocator store inst instanceIndex start error) ⦄ := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop4
  apply loop.spec_decr_nat (fun state => seed.module.module.env.func_type_indices.val.length - state.2.2.1.val)
    (fun state => state.1 = {before with funcs := state.1.funcs} ∧
      state.2.2.2 = {seed with funcs := state.2.2.2.funcs} ∧ StagedPrefix before state.1 ∧
      objectCount state.1 ≤ Usize.max ∧
      (∀ address ∈ state.2.2.2.funcs.val, address.index.val < state.1.funcs.length) ∧
      state.2.2.1.val ≤ seed.module.module.env.func_type_indices.val.length ∧
      (state.2.1 = .Ok () → state.2.2.2.funcs.length = seed.funcs.length + state.2.2.1.val) ∧
      (state.2.1 = .Ok () → PreparationCalls (functionStageCall memory allocator instanceIndex) (store,inst) start (state.1,state.2.2.2) state.2.2.1) ∧
      (∀ error, state.2.1 = .Err error → FunctionStagingCause memory allocator store inst instanceIndex start error))
  · rintro ⟨current, status, index, currentInst⟩ ⟨currentChanged, mapChanged, prefixStore, bound, currentIssued, indexBound, counting, trace, cause⟩
    dsimp only at currentChanged mapChanged prefixStore bound currentIssued indexBound counting ⊢
    have source : currentInst.module = seed.module := by
      have eq := congrArg runtime.store.ModuleInst.module mapChanged
      exact eq
    have types : currentInst.types = seed.types := by
      have eq := congrArg runtime.store.ModuleInst.types mapChanged
      exact eq
    unfold runtime.store.instantiate.Store.prepare_instance_loop4.body
    simp only [runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.func_type_indices, source, bind_ok]
    split
    · rename_i more
      have within : index.val < seed.module.module.env.func_type_indices.val.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, currentInst, .Err error, by simp [typeParts, source], currentChanged,
          mapChanged, prefixStore, bound, currentIssued, by simp, cause⟩
      | Ok value =>
        cases value
        have size := counting rfl
        have actualBound : index.val < currentInst.module.module.env.func_type_indices.val.length := by simpa only [source] using within
        have typeBound : currentInst.module.module.env.func_type_indices.val[index.val].val < currentInst.types.val.length := by
          simpa only [source, types] using typeBounds _ (List.getElem_mem within)
        have room : currentInst.funcs.length < Usize.max := by omega
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        have reached := trace rfl
        obtain ⟨⟨status,after,nextInst⟩,called,effect⟩ := WP.spec_imp_exists
          (add_instance_function_effect memory allocator law current currentInst instanceIndex index
            bound actualBound typeBound room)
        rw [called]
        simp only [bind_ok,uncurry_apply_pair]
        obtain ⟨afterChanged, nextChanged, prefixNext, nextBound, _⟩ := effect.context bound
        have afterExact : after = {before with funcs := after.funcs} := by
          calc
            after = {current with funcs := after.funcs} := afterChanged
            _ = _ := by rw [currentChanged]
        have nextExact : nextInst = {seed with funcs := nextInst.funcs} := by
          calc
            nextInst = {currentInst with funcs := nextInst.funcs} := nextChanged
            _ = _ := by rw [mapChanged]
        step as ⟨next, increment⟩
        refine ⟨afterExact, nextExact, prefixStore.trans prefixNext, nextBound,
          effect.issued currentIssued, ?_, ?_, ?_, ?_, ?_⟩
        · omega
        · intro success
          have appended := effect.count success
          dsimp only at appended
          omega
        · intro success
          subst status
          exact .next reached called increment
        · intro error rejected
          subst status
          obtain ⟨unchanged,sameInst,refusal⟩ :=
            add_function_resource_cause memory allocator law current currentInst instanceIndex index bound error after nextInst called
          subst after
          subst nextInst
          exact ⟨current,currentInst,index,reached,called,refusal⟩
        · omega
    · rename_i stopped
      have atEnd : index.val = seed.module.module.env.func_type_indices.val.length := by
        simp [alloc.vec.Vec.deref] at stopped
        omega
      simp only [WP.spec_ok]
      refine ⟨current, currentInst, status, by simp [typeParts, source], currentChanged,
        mapChanged, prefixStore, bound, currentIssued, ?_, cause⟩
      intro success
      simpa only [atEnd] using counting success
  · exact ⟨changed, instChanged, retained, objectBound, issued, startBound, (fun _ => count), (fun _ => .refl _ _), by simp⟩

end Itasca.Runtime.Store

end
