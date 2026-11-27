import Itasca.Runtime.Representation.Values
import Itasca.Runtime.Spec.PrimitiveOperations
import Itasca.Runtime.Store.Initialization.SegmentReady
import Itasca.Runtime.Store.Invariant.CoreInstantiationSource
import Itasca.Runtime.Store.Initialization.SegmentSourceStaging
import Itasca.Runtime.Store.Initialization.SegmentSyntheticPreservation
import Itasca.Runtime.Interp.Relations.SourceClosure
import Itasca.Runtime.Compiler.Module.DriverAndCodeRegions

/-!
Proofs for Runtime / Store / Initialization.

This module collects SegmentDrop, SegmentInitializePreservation.
Each section documents its contracts and consumers.
-/

/-! ## SegmentDrop -/

section

open Itasca.Representation

/-!
Segment drop execution and decoded source effect. The construction is used before returning the resolved start handle; it does not invoke the start function.
-/

/-! ## Segment Drop Semantics -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std WebAssembly

theorem data_drop_decodes {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (ambient : frame)
    (index : U32) (address : Usize) (old : runtime.store.DataInst)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (mapped : inst.datas.val[index.val]? = some address)
    (found : store.datas.val[address.val]? = some old) :
    decodeStore view code {store with datas := store.datas.set address ⟨alloc.vec.Vec.new U8⟩} =
      Spec.droppedDataStore (decodeStore view code store) ambient index.val := by
  have read : ambient.MODULE.DATAS[index.val]! = address.val := by
    rw [moduleEq]
    simp only [decodeInstance, List.getElem!_eq_getElem?_getD, List.getElem?_map, mapped, Option.map_some, Option.getD_some]
  have lists := Itasca.Representation.map_set_modify decodeData (fun data => {data with BYTES := []}) store.datas.val address.val old
    ⟨alloc.vec.Vec.new U8⟩ found rfl
  unfold Spec.droppedDataStore
  rw [read]
  unfold decodeStore
  simp only [alloc.vec.Vec.set_val_eq, lists]
  rfl

theorem element_drop_decodes {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (ambient : frame)
    (index : U32) (address : Usize) (old : runtime.store.ElemInst)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (mapped : inst.elems.val[index.val]? = some address)
    (found : store.elems.val[address.val]? = some old) :
    decodeStore view code {store with elems := store.elems.set address {old with refs := alloc.vec.Vec.new U64}} =
      Spec.droppedElementStore (decodeStore view code store) ambient index.val := by
  have read : ambient.MODULE.ELEMS[index.val]! = address.val := by
    rw [moduleEq]
    simp only [decodeInstance, List.getElem!_eq_getElem?_getD, List.getElem?_map, mapped, Option.map_some, Option.getD_some]
  have lists := Itasca.Representation.map_set_modify decodeElement (fun element => {element with REFS := []}) store.elems.val address.val old
    {old with refs := alloc.vec.Vec.new U64} found rfl
  unfold Spec.droppedElementStore
  rw [read]
  unfold decodeStore
  simp only [alloc.vec.Vec.set_val_eq, lists]
  rfl

theorem data_drop_refines {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (ambient : frame)
    (index : U32) (address : Usize) (old : runtime.store.DataInst)
    (shape : Shape view store) (sourceSyntax : StoreSyntax code store) (ambientWf : wf_frame ambient)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (mapped : inst.datas.val[index.val]? = some address)
    (found : store.datas.val[address.val]? = some old) :
    StepH ⟨⟨decodeStore view code store,ambient⟩,[.DATA_DROP (.mk_uN index.val)]⟩ []
      ⟨⟨decodeStore view code {store with datas := store.datas.set address ⟨alloc.vec.Vec.new U8⟩},ambient⟩,[]⟩ := by
  rw [data_drop_decodes view code store inst ambient index address old moduleEq mapped found]
  apply Spec.data_drop_step _ _ _ (decode_store_wf view code store shape sourceSyntax) ambientWf (by scalar_tac)
  · have bound := (List.getElem?_eq_some_iff.mp mapped).1
    simpa [moduleEq, decodeInstance] using bound
  · rw [← data_drop_decodes view code store inst ambient index address old moduleEq mapped found]
    exact decode_store_wf view code _ (shape.data_drop address) (sourceSyntax.instances_eq rfl)

theorem element_drop_refines {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (ambient : frame)
    (index : U32) (address : Usize) (old : runtime.store.ElemInst)
    (shape : Shape view store) (sourceSyntax : StoreSyntax code store) (ambientWf : wf_frame ambient)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (mapped : inst.elems.val[index.val]? = some address)
    (found : store.elems.val[address.val]? = some old) :
    StepH ⟨⟨decodeStore view code store,ambient⟩,[.ELEM_DROP (.mk_uN index.val)]⟩ []
      ⟨⟨decodeStore view code {store with elems := store.elems.set address {old with refs := alloc.vec.Vec.new U64}},ambient⟩,[]⟩ := by
  rw [element_drop_decodes view code store inst ambient index address old moduleEq mapped found]
  apply Spec.element_drop_step _ _ _ (decode_store_wf view code store shape sourceSyntax) ambientWf (by scalar_tac)
  · have bound := (List.getElem?_eq_some_iff.mp mapped).1
    simpa [moduleEq, decodeInstance] using bound
  · rw [← element_drop_decodes view code store inst ambient index address old moduleEq mapped found]
    exact decode_store_wf view code _ (shape.element_drop address old) (sourceSyntax.instances_eq rfl)

end Itasca.Store

end

/-! ## Segment Drop Execution -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std WebAssembly

theorem bulk_data_drop_refines {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (instIndex function base : Usize) (slots : Slice U64)
    (inst : runtime.store.ModuleInst) (index : U32) (address : Usize) (ambient : frame)
    (found : store.instances.val[instIndex.val]? = some inst)
    (mapped : inst.datas.val[index.val]? = some address) (issued : address.val < store.datas.length)
    (shape : Shape view store) (sourceSyntax : StoreSyntax code store) (ambientWf : wf_frame ambient)
    (moduleEq : ambient.MODULE = decodeInstance store inst) :
    runtime.interp.bulk.execute memory store instIndex function base slots (.DataDrop index)
      ⦃ out => out.1 = .Ok () ∧
        StepH ⟨⟨decodeStore view code store,ambient⟩,[.DATA_DROP (.mk_uN index.val)]⟩ []
          ⟨⟨decodeStore view code out.2,ambient⟩,[]⟩ ⦄ := by
  apply WP.spec_mono (bulk_data_drop memory store instIndex function base slots inst index address found mapped issued)
  rintro out rfl
  exact ⟨rfl, data_drop_refines view code store inst ambient index address store.datas.val[address.val]
    shape sourceSyntax ambientWf moduleEq mapped (List.getElem?_eq_getElem issued)⟩

theorem bulk_element_drop_refines {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (instIndex function base : Usize) (slots : Slice U64)
    (inst : runtime.store.ModuleInst) (index : U32) (address : Usize) (ambient : frame)
    (found : store.instances.val[instIndex.val]? = some inst)
    (mapped : inst.elems.val[index.val]? = some address) (issued : address.val < store.elems.length)
    (shape : Shape view store) (sourceSyntax : StoreSyntax code store) (ambientWf : wf_frame ambient)
    (moduleEq : ambient.MODULE = decodeInstance store inst) :
    runtime.interp.bulk.execute memory store instIndex function base slots (.ElemDrop index)
      ⦃ out => out.1 = .Ok () ∧
        StepH ⟨⟨decodeStore view code store,ambient⟩,[.ELEM_DROP (.mk_uN index.val)]⟩ []
          ⟨⟨decodeStore view code out.2,ambient⟩,[]⟩ ⦄ := by
  apply WP.spec_mono (bulk_element_drop memory store instIndex function base slots inst index address found mapped issued)
  rintro out rfl
  exact ⟨rfl, element_drop_refines view code store inst ambient index address store.elems.val[address.val]
    shape sourceSyntax ambientWf moduleEq mapped (List.getElem?_eq_getElem issued)⟩

end Itasca.Store

end

end

/-! ## SegmentInitializePreservation -/

section

open Itasca.Representation

/-!
# Segment initialization preservation

Compatibility, accepted compiled execution and retained object effects combine to preserve the initialization certificates across segment programs.
-/

/-! ## SegmentCompatibility -/

section SegmentCompatibility

/-!
# Segment initializer compatibility

Source-ordered initializer programs and staged type maps discharge reference-type compatibility for table initialization. These facts support the source semantics of committed segment effects.
-/

namespace Itasca.Store
open Aeneas Aeneas.Std

private theorem constant_compatible {M : Type} {store : runtime.store.Store M} {inst code dst expr ty instruction}
    (constant : Compiler.ConstantInstruction code dst expr ty instruction) :
    SegmentBulkCompatible store inst code instruction := by
  cases constant <;> trivial

private theorem element_compatible {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (index : Nat) (segment : Itasca.metadata.Element) (instructions : List runtime.bytecode.Instr)
    (program : Compiler.ElementProgram code index segment instructions)
    (found : inst.module.module.env.elements.val[index]? = some segment)
    (typed : Itasca.Module.Segments.elementValid inst.module.module.env segment)
    (bindings : SegmentTypeBindings store inst) :
    ∀ instruction ∈ instructions, SegmentBulkCompatible store inst code instruction := by
  cases program with
  | passive mode => simp
  | declarative mode word encoded => simp [SegmentBulkCompatible]
  | active table offset mode word length entry encoded count descriptor instruction constant =>
    obtain ⟨tableBound, sameType, valid⟩ :=
      (show ∃ h : table.val < inst.module.module.env.table_types.val.length,
        inst.module.module.env.table_types.val[table.val].elem = segment.elem ∧
        Itasca.Module.Constants.Valid inst.module.module.env offset .I32 from by simpa [mode] using typed.1)
    intro op member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact constant_compatible constant
    · trivial
    · trivial
    · exact segment_table_compatible store inst code entry word table segment
        inst.module.module.env.table_types.val[table.val] descriptor (by simpa [encoded] using found)
        (List.getElem?_eq_getElem tableBound) sameType.symm bindings
    · trivial

private theorem data_compatible {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (index : Nat) (segment : Itasca.metadata.Data) (instructions : List runtime.bytecode.Instr)
    (program : Compiler.DataProgram code index segment instructions) :
    ∀ instruction ∈ instructions, SegmentBulkCompatible store inst code instruction := by
  cases program with
  | passive mode => simp
  | active memory offset mode word length encoded count instruction constant =>
    intro op member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact constant_compatible constant
    all_goals trivial

/-- The compiler's source-ordered program and staged type maps discharge all
reference-type compatibility requirements of its table initialization steps. -/
theorem segment_program_compatible {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (program : Compiler.SegmentProgram inst.module code) (bindings : SegmentTypeBindings store inst)
    (valid : ∀ segment ∈ inst.module.module.env.elements.val,
      Itasca.Module.Segments.elementValid inst.module.module.env segment) :
    ∀ instruction ∈ code.code.val, SegmentBulkCompatible store inst code instruction := by
  obtain ⟨elements, datas, certificate⟩ := program
  intro instruction member
  rw [certificate.instructions] at member
  simp only [List.mem_append, List.mem_singleton] at member
  rcases member with (member | member) | rfl
  · obtain ⟨block, inBlocks, inBlock⟩ := List.mem_flatten.mp member
    obtain ⟨index, indexBound, indexed⟩ := List.mem_iff_getElem.mp inBlocks
    have sourceBound : index < inst.module.module.env.elements.val.length := by
      have := certificate.elementCount
      simp only [alloc.vec.Vec.length] at this
      omega
    let segment := inst.module.module.env.elements.val[index]
    have found : inst.module.module.env.elements.val[index]? = some segment := List.getElem?_eq_getElem sourceBound
    obtain ⟨instructions, read, emitted⟩ := certificate.elements index segment found
    have same : instructions = block := by
      rw [List.getElem?_eq_getElem indexBound, indexed] at read
      exact Option.some.inj read.symm
    subst instructions
    exact element_compatible store inst code index segment block emitted found
      (valid segment (List.mem_of_getElem? found)) bindings instruction inBlock
  · obtain ⟨block, inBlocks, inBlock⟩ := List.mem_flatten.mp member
    obtain ⟨index, indexBound, indexed⟩ := List.mem_iff_getElem.mp inBlocks
    have sourceBound : index < inst.module.module.tail.data.val.length := by
      have := certificate.dataCount
      simp only [alloc.vec.Vec.length] at this
      omega
    let segment := inst.module.module.tail.data.val[index]
    have found : inst.module.module.tail.data.val[index]? = some segment := List.getElem?_eq_getElem sourceBound
    obtain ⟨instructions, read, emitted⟩ := certificate.datas index segment found
    have same : instructions = block := by
      rw [List.getElem?_eq_getElem indexBound, indexed] at read
      exact Option.some.inj read.symm
    subst instructions
    exact data_compatible store inst code index segment block emitted instruction inBlock
  · trivial

end Itasca.Store

end SegmentCompatibility

/-! ## SegmentAccepted -/

section SegmentAccepted

/-!
Total compiled segment initialization. Synthetic-frame loop execution lifts to complete segment programs and the accepted compiler certificate, returning without invoking the start function.
-/

/-! ## Segment Synthetic -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std
open Itasca.Interp

/-- The actual synthetic entry point allocates its private slots/frame, then
runs the checked finite segment program. Allocation refusal and ordinary range
traps return normally; platform and address-space metadata are preserved. -/
theorem segment_synthetic_total {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex function : Usize)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[function.val]? = some code)
    (ready : SegmentCodeReady store inst code code.slot_count.val) :
    runtime.interp.run_synthetic memory hooks floats allocator store platform instIndex function
      ⦃ out => SegmentAddressSpace store out.2.1 ∧ out.2.2 = platform ⦄ := by
  unfold runtime.interp.run_synthetic
  step with vec_index_given store.instances instIndex inst found as ⟨actual, equal⟩
  subst actual
  step with vec_index_given inst.module.functions function code functionFound as ⟨actual, equal⟩
  subst actual
  simp only [lift, bind_ok, runtime.interp.Execution.new]
  step with ensure_effect allocator law _ _ _ as ⟨status, prepared, ensured⟩
  cases status with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    exact SegmentAddressSpace.refl store
  | Ok unitValue =>
    cases unitValue
    simp only [EnsureEffect] at ensured
    obtain ⟨limit, hslots, hother⟩ := ensured
    have slots : prepared.slots.val = List.replicate code.slot_count.val 0#u64 := by
      simpa [alloc.vec.Vec.new] using hslots
    have frames : prepared.frames.val = [] := by
      have h := congrArg runtime.interp.Execution.frames hother
      simpa [alloc.vec.Vec.new] using congrArg alloc.vec.Vec.val h
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    obtain ⟨answer, reserved⟩ := law.reserve_eq prepared.frames 1#usize
    have reserveCall : runtime.reserve allocator prepared.frames 1#usize = .ok
        ((if answer then .Ok () else .Err (.Exhausted .Allocation)), prepared.frames) := by
      cases answer <;> simp [runtime.reserve, reserved]
    rw [reserveCall, bind_ok]
    cases answer with
    | false =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      exact SegmentAddressSpace.refl store
    | true =>
      simp only [↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step as ⟨pushed, hpushed⟩
      have pushedFrames : pushed.val = [initializerFrame instIndex function 0#u32] := by
        simpa [frames, initializerFrame] using hpushed
      have nonempty : 0 < code.code.length := by
        have := ready.returnLast
        by_contra empty
        have nil : code.code.val = [] := List.eq_nil_of_length_eq_zero (by simp only [alloc.vec.Vec.length] at empty; omega)
        simp [nil] at this
      have capacity : prepared.slots.length = code.slot_count.val := by simp [alloc.vec.Vec.length, slots]
      step with segment_loop_total memory hooks floats allocator view laws store platform
        {prepared with frames := pushed} instIndex function inst code 0#u32 found functionFound pushedFrames
        (by simpa using nonempty) (by simpa only [capacity] using ready)
        as ⟨after, host, finalSlots, result, metadata, hostEq, width, status⟩
      subst host
      cases result with
      | Err error =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        exact metadata
      | Ok unitValue =>
        cases unitValue
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step with get_effect finalSlots.deref 0#usize
        step with get_effect finalSlots.deref 1#usize
        exact metadata

end Itasca.Store

end

/-! ## Segment Initialize -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

/-- The actual instantiation segment entry point returns normally for the
compiler's retained program and issued instance maps. -/
theorem initialize_segments_total {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex : Usize)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[inst.module.initialization.val]? = some code)
    (ready : SegmentCodeReady store inst code code.slot_count.val) :
    runtime.interp.initialize_segments memory hooks floats allocator store platform instIndex
      ⦃ out => SegmentAddressSpace store out.2.1 ∧ out.2.2 = platform ⦄ := by
  unfold runtime.interp.initialize_segments
  step with Interp.vec_index_given store.instances instIndex inst found as ⟨actual, equal⟩
  subst actual
  step with segment_synthetic_total memory hooks floats allocator view laws law store platform instIndex
    inst.module.initialization inst code found functionFound ready as ⟨result, after, host, metadata, hostEq⟩
  subst host
  cases result <;> simp_all [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- Source typing and the syntactic emitted-program certificate discharge all
machine-readiness obligations; no execution-safety premise is required. -/
theorem initialize_segments_program_total {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex : Usize)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[inst.module.initialization.val]? = some code)
    (program : Compiler.SegmentProgram inst.module code) (pcBound : code.code.length < U32.max)
    (shape : InstanceShape store inst) (imports : InitializerImports store inst)
    (bindings : InitializerBindings store inst)
    (elementsValid : ∀ segment ∈ inst.module.module.env.elements.val,
      Itasca.Module.Segments.elementValid inst.module.module.env segment)
    (dataValid : ∀ segment ∈ inst.module.module.tail.data.val,
      Itasca.Module.Data.Valid inst.module.module.env segment) :
    runtime.interp.initialize_segments memory hooks floats allocator store platform instIndex
      ⦃ out => SegmentAddressSpace store out.2.1 ∧ out.2.2 = platform ⦄ :=
  initialize_segments_total memory hooks floats allocator view laws law store platform instIndex inst code
    found functionFound (segment_program_ready store inst code program pcBound shape imports bindings elementsValid dataValid)

end Itasca.Store

end

/-! ## Segment Accepted -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

/-- A successfully compiled module supplies both the retained program and all
source typing/PC bounds for actual segment initialization. The remaining
premises are the issued instance maps produced by linking and staging. -/
theorem initialize_segments_compiled {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex : Usize)
    (inst : runtime.store.ModuleInst) (bytes : Slice U8)
    (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes limits = .ok (.Ok inst.module))
    (found : store.instances.val[instIndex.val]? = some inst)
    (shape : InstanceShape store inst) (imports : InitializerImports store inst)
    (bindings : InitializerBindings store inst) :
    runtime.interp.initialize_segments memory hooks floats allocator store platform instIndex
      ⦃ out => SegmentAddressSpace store out.2.1 ∧ out.2.2 = platform ⦄ := by
  obtain ⟨witness⟩ := Compiler.compile_accepted allocator bytes limits inst.module accepted
  obtain ⟨code, functionFound, program⟩ := witness.segment_program law
  obtain ⟨valid, dataValid⟩ := witness.semantic law
  have pcBound := Compiler.segment_compile_pc_bound allocator law bytes limits inst.module accepted code program
  exact initialize_segments_program_total memory hooks floats allocator view laws law store platform instIndex inst code
    found functionFound program pcBound shape imports bindings valid.elements dataValid

end Itasca.Store

end

end SegmentAccepted

/-! ## SegmentInitializePreservation -/

section SegmentInitializePreservation

/-!
Complete segment initialization preserves object metadata and shape, using accepted compiler certificates without invoking the resolved start function.
-/

/-! ## Segment Initialize Metadata -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

theorem initialize_segments_object_metadata {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex : Usize)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[inst.module.initialization.val]? = some code)
    (ready : SegmentCodeReady store inst code code.slot_count.val) :
    runtime.interp.initialize_segments memory hooks floats allocator store platform instIndex
      ⦃ out => SegmentObjectMetadata view store out.2.1 ⦄ := by
  unfold runtime.interp.initialize_segments
  step with Interp.vec_index_given store.instances instIndex inst found as ⟨actual, equal⟩
  subst actual
  step with segment_synthetic_object_metadata memory hooks floats allocator view laws law store platform instIndex
    inst.module.initialization inst code found functionFound ready as ⟨result, after, host, objects⟩
  cases result <;> simp_all [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- Canonically compiled initialization preserves object sizes, types and maxima,
and only retains or drops segment payloads. -/
theorem initialize_segments_compiled_object_metadata {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex : Usize)
    (inst : runtime.store.ModuleInst) (bytes : Slice U8)
    (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes limits = .ok (.Ok inst.module))
    (found : store.instances.val[instIndex.val]? = some inst)
    (shape : Shape view store) (imports : InitializerImports store inst)
    (bindings : InitializerBindings store inst) :
    runtime.interp.initialize_segments memory hooks floats allocator store platform instIndex
      ⦃ out => SegmentObjectMetadata view store out.2.1 ⦄ := by
  obtain ⟨witness⟩ := Compiler.compile_accepted allocator bytes limits inst.module accepted
  obtain ⟨code, functionFound, program⟩ := witness.segment_program law
  obtain ⟨valid, dataValid⟩ := witness.semantic law
  have pcBound := Compiler.segment_compile_pc_bound allocator law bytes limits inst.module accepted code program
  have instanceShape := shape.instances inst (List.mem_of_getElem? found)
  have ready := segment_program_ready store inst code program pcBound instanceShape imports bindings valid.elements dataValid
  exact initialize_segments_object_metadata memory hooks floats allocator view laws law store platform instIndex inst code
    found functionFound ready

end Itasca.Store

end

/-! ## Segment Initialize Shape -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

theorem initialize_segments_shape {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex : Usize)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[inst.module.initialization.val]? = some code)
    (ready : SegmentCodeReady store inst code code.slot_count.val)
    (shape : Shape view store)
    (compatible : ∀ instruction ∈ code.code.val, SegmentBulkCompatible store inst code instruction) :
    runtime.interp.initialize_segments memory hooks floats allocator store platform instIndex
      ⦃ out => Shape view out.2.1 ∧ SegmentTypes store out.2.1 ⦄ := by
  unfold runtime.interp.initialize_segments
  step with Interp.vec_index_given store.instances instIndex inst found as ⟨actual, equal⟩
  subst actual
  step with segment_synthetic_shape memory hooks floats allocator view laws law store platform instIndex
    inst.module.initialization inst code found functionFound ready shape compatible as ⟨result, after, host, afterShape, types⟩
  cases result <;> simp_all [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- Canonically compiled initialization preserves the full structural Store
invariant, assuming the source/raw reference-type maps established by staging. -/
theorem initialize_segments_compiled_shape {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex : Usize)
    (inst : runtime.store.ModuleInst) (bytes : Slice U8)
    (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes limits = .ok (.Ok inst.module))
    (found : store.instances.val[instIndex.val]? = some inst)
    (shape : Shape view store) (imports : InitializerImports store inst)
    (bindings : InitializerBindings store inst) (types : SegmentTypeBindings store inst) :
    runtime.interp.initialize_segments memory hooks floats allocator store platform instIndex
      ⦃ out => Shape view out.2.1 ∧ SegmentTypes store out.2.1 ⦄ := by
  obtain ⟨witness⟩ := Compiler.compile_accepted allocator bytes limits inst.module accepted
  obtain ⟨code, functionFound, program⟩ := witness.segment_program law
  obtain ⟨valid, dataValid⟩ := witness.semantic law
  have pcBound := Compiler.segment_compile_pc_bound allocator law bytes limits inst.module accepted code program
  have instanceShape := shape.instances inst (List.mem_of_getElem? found)
  have ready := segment_program_ready store inst code program pcBound instanceShape imports bindings valid.elements dataValid
  have compatible := segment_program_compatible store inst code program types valid.elements
  exact initialize_segments_shape memory hooks floats allocator view laws law store platform instIndex inst code
    found functionFound ready shape compatible

end Itasca.Store

end

end SegmentInitializePreservation

end
