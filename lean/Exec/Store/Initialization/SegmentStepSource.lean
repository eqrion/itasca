import Exec.Store.Initialization.SegmentInstruction
import Exec.Store.Api.TableInitSemantics
import Exec.Spec.Context
import Exec.Store.Initialization.SegmentPending
import Exec.Store.Invariant.Syntax
import Exec.Store.Api.MemoryInitExecution
import Exec.Store.Api.TableInitExecution
import Exec.Store.Initialization.SegmentDropExecution
import Exec.Store.Initialization.SegmentCompatible
import Exec.Code.Local.Relations.Common.SegmentTranslation
import Exec.Store.Initialization.SegmentStep

namespace Exec.Store
open Aeneas Aeneas.Std SpecExt

def segmentAfter (status : core.result.Result Unit runtime.ExecError) (after : List admininstr) : List admininstr :=
  match status with | .Ok _ => after | .Err _ => [.TRAP]

theorem segment_steps_suffix (first : config) (s : store) (f : frame)
    (status : core.result.Result Unit runtime.ExecError) (after : List admininstr)
    (steps : StepsH first [] ⟨⟨s,f⟩,segmentResult status⟩)
    (afterWf : Forall wf_admininstr after) :
    StepsH (Spec.instrContext [] after first) [] ⟨⟨s,f⟩,segmentAfter status after⟩ := by
  have lifted := Spec.stepsH_instrs steps [] after (by simp [Forall]) afterWf
  cases status with
  | Ok _unitValue => simpa [Spec.instrContext,vals,segmentResult,segmentAfter] using lifted
  | Err error =>
    have wf := (Spec.stepsH_wf steps).2
    by_cases empty : after = []
    · subst after
      simpa [Spec.instrContext,vals,segmentResult,segmentAfter] using lifted
    · have input := (Spec.stepsH_wf lifted).2
      have trap : StepH (Spec.instrContext [] after ⟨⟨s,f⟩,segmentResult (.Err error)⟩) [] ⟨⟨s,f⟩,[.TRAP]⟩ :=
        .step (.pure _ _ _ (.trap_vals [] after (Or.inr empty) (by simp [Forall]) afterWf .admininstr_case_73) input wf)
      exact Spec.stepsH_trans lifted (Spec.stepsH_single trap)

end Exec.Store

namespace Exec.Store
open Aeneas Aeneas.Std SpecExt

theorem segment_global_source {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (ambient : frame)
    (index : U32) (address : runtime.GlobalAddr) (value : runtime.store.GlobalInst)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (mapped : inst.globals.val[index.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some value)
    (typed : value.ty.valtype = .I32)
    (shape : Shape view store) (sourceSyntax : StoreSyntax code store) (ambientWf : wf_frame ambient) :
    StepH ⟨⟨decodeStore view code store,ambient⟩,[.GLOBAL_GET (.mk_uN index.val)]⟩ []
      ⟨⟨decodeStore view code store,ambient⟩,vals [segmentValue value.lo]⟩ := by
  have fetched : fun_global ⟨decodeStore view code store,ambient⟩ (.mk_uN index.val) = decodeGlobal value := by
    simp [fun_global,moduleEq,decodeStore,decodeInstance,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,issued]
  have wf := decodeStore_wf view code store shape sourceSyntax
  have input := Spec.wf_config_make wf ambientWf
    (show Forall wf_admininstr [.GLOBAL_GET (.mk_uN index.val)] from by
      simpa [Forall] using wf_admininstr.admininstr_case_46 _ (Spec.Segment.index_wf _ (by scalar_tac)))
  have output := Spec.wf_config_vals wf ambientWf (show Forall wf_val [segmentValue value.lo] from by
    simpa [Forall] using segmentValue_wf value.lo)
  apply StepH.step
  apply Step.read _ _ _ ?_ input output
  have read := Step_read.global_get ⟨decodeStore view code store,ambient⟩ (.mk_uN index.val) input
  have bits : (bulkWord value.lo).val = value.lo.val % 2^32 := by scalar_tac
  simpa only [fetched,decodeGlobal,typed,decodeWords,vals,List.map_cons,List.map_nil,segmentValue,admininstr_val,bits] using read

end Exec.Store

namespace Exec.Store
open Aeneas Aeneas.Std SpecExt

def segmentArity : runtime.bytecode.Instr → Nat
  | .MemoryInit _ _ | .TableInit _ _ => 3
  | _ => 0

theorem slot_triple (slots : Slice U64) (capacity : 3 ≤ slots.length) :
    ∃ a b c : U64, slots.val[0]? = some a ∧ slots.val[1]? = some b ∧ slots.val[2]? = some c := by
  change 3 ≤ slots.val.length at capacity
  have h0 : 0 < slots.val.length := by omega
  have h1 : 1 < slots.val.length := by omega
  have h2 : 2 < slots.val.length := by omega
  refine ⟨slots.val[0],slots.val[1],slots.val[2],?_,?_,?_⟩
  all_goals exact List.getElem?_eq_getElem (by omega)

theorem segment_bulk_source {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (sourceCode : CodeInterpretation)
    (store : runtime.store.Store M) (instIndex function : Usize) (slots : Slice U64)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr) (ambient : frame)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[function.val]? = some compiled)
    (ready : SegmentBulkReady store inst compiled instruction)
    (compatible : SegmentBulkCompatible store inst compiled instruction)
    (capacity : segmentArity instruction ≤ slots.length)
    (shape : Shape view store) (sourceSyntax : StoreSyntax sourceCode store) (bounds : SegmentBounds store)
    (ambientWf : wf_frame ambient) (moduleEq : ambient.MODULE = decodeInstance store inst) :
    runtime.interp.bulk.execute memory store instIndex function 0#usize slots instruction
      ⦃ out => StepsH ⟨⟨decodeStore view sourceCode store,ambient⟩,
        vals (segmentPending slots.val (segmentArity instruction)) ++ Code.segmentInstructionSource compiled instruction⟩ []
        ⟨⟨decodeStore view sourceCode out.2,ambient⟩,segmentResult out.1⟩ ⦄ := by
  cases ready with
  | memory data address memoryAddress mapped issued mappedMemory issuedMemory =>
    obtain ⟨a,b,c,ha,hb,hc⟩ := slot_triple slots capacity
    let dataValue := store.datas.val[address.val]
    let memoryValue := store.memories.val[memoryAddress.index.val]
    have dataFound : store.datas.val[address.val]? = some dataValue := List.getElem?_eq_getElem issued
    have memoryFound : store.memories.val[memoryAddress.index.val]? = some memoryValue := List.getElem?_eq_getElem issuedMemory
    simpa only [segmentArity,segmentPending_three slots.val a b c ha hb hc,Code.segmentInstructionSource] using
      bulk_memory_init_refines memory view laws sourceCode store instIndex function slots inst data address memoryAddress
        memoryValue dataValue a b c ambient found mapped dataFound mappedMemory memoryFound ha hb hc shape sourceSyntax
        ambientWf moduleEq (bounds.data dataValue (List.mem_of_getElem? dataFound))
  | table entry element tableId address tableAddress descriptor mapped issued mappedTable issuedTable =>
    obtain ⟨a,b,c,ha,hb,hc⟩ := slot_triple slots capacity
    let elementValue := store.elems.val[address.val]
    let tableValue := store.tables.val[tableAddress.index.val]
    have elementFound : store.elems.val[address.val]? = some elementValue := List.getElem?_eq_getElem issued
    have tableFound : store.tables.val[tableAddress.index.val]? = some tableValue := List.getElem?_eq_getElem issuedTable
    have sameType := compatible element tableId address tableAddress elementValue tableValue descriptor mapped mappedTable elementFound tableFound
    simpa only [segmentArity,segmentPending_three slots.val a b c ha hb hc,Code.segmentInstructionSource,
      List.getElem!_eq_getElem?_getD,descriptor,Option.getD_some] using
      bulk_table_init_refines memory view sourceCode store instIndex function slots inst compiled entry element tableId address
        tableAddress tableValue elementValue a b c ambient found functionFound descriptor mapped elementFound mappedTable tableFound
        ha hb hc sameType.symm shape sourceSyntax ambientWf moduleEq (bounds.elements elementValue (List.mem_of_getElem? elementFound))
  | dataDrop data address mapped issued =>
    apply WP.spec_mono (bulk_data_drop_refines memory view sourceCode store instIndex function 0#usize slots inst data address ambient
      found mapped issued shape sourceSyntax ambientWf moduleEq)
    rintro out ⟨success,step⟩
    simpa [segmentArity,segmentPending,vals,Code.segmentInstructionSource,success,segmentResult] using Spec.stepsH_single step
  | elementDrop element address mapped issued =>
    apply WP.spec_mono (bulk_element_drop_refines memory view sourceCode store instIndex function 0#usize slots inst element address ambient
      found mapped issued shape sourceSyntax ambientWf moduleEq)
    rintro out ⟨success,step⟩
    simpa [segmentArity,segmentPending,vals,Code.segmentInstructionSource,success,segmentResult] using Spec.stepsH_single step

end Exec.Store

namespace Exec.Store
open Aeneas Aeneas.Std SpecExt

def segmentState {M : Type} (view : M → Slice U8) (source : CodeInterpretation)
    (store : runtime.store.Store M) (ambient : frame) (code : runtime.bytecode.CompiledFunction)
    (slots : List U64) (pending : Nat) (remaining : List runtime.bytecode.Instr) : config :=
  ⟨⟨decodeStore view source store,ambient⟩,vals (segmentPending slots pending) ++ Code.segmentSource code remaining⟩

theorem segmentState_wf {M : Type} (view : M → Slice U8) (source : CodeInterpretation)
    (store : runtime.store.Store M) (ambient : frame) (code : runtime.bytecode.CompiledFunction)
    (slots : List U64) (pending : Nat) (remaining : List runtime.bytecode.Instr)
    (shape : Shape view store) (sourceSyntax : StoreSyntax source store) (frameWf : wf_frame ambient) :
    wf_config (segmentState view source store ambient code slots pending remaining) :=
  Spec.wf_config_make (decodeStore_wf view source store shape sourceSyntax) frameWf
    (Spec.forall_append (Spec.wf_vals (segmentPending_wf slots pending)) (Code.segmentSource_wf code remaining))

theorem segmentPending_one_set (slots : List U64) (word : U64) (inside : 0 < slots.length) :
    segmentPending (slots.set 0 word) 1 = [segmentValue word] := by
  cases slots with
  | nil => simp at inside
  | cons a rest => rfl

end Exec.Store
namespace Exec.Store
open Aeneas Aeneas.Std SpecExt Exec.Interp

variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A) (view : M → Slice U8)
  (sourceCode : CodeInterpretation)

theorem segment_step_constant_source (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (instIndex function : Usize) (position : U32)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction) (dst bits : U32)
    (rest : List runtime.bytecode.Instr)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[function.val]? = some code)
    (frames : exec.frames.val = [initializerFrame instIndex function position])
    (fetched : code.code.val[position.val]? = some (.Const32 dst bits))
    (pcBound : position.val < U32.max) (capacity : dst.val < exec.slots.length)
    (shape : Shape view store) (sourceSyntax : StoreSyntax sourceCode store) (ambient : frame) (ambientWf : wf_frame ambient) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ StepsH
        (segmentState view sourceCode store ambient code exec.slots.val dst.val (.Const32 dst bits :: rest)) []
        (segmentState view sourceCode out.2.2.1 ambient code out.2.1.slots.val (dst.val+1) rest) ⦄ := by
  apply WP.spec_mono (segment_step_const32 memory hooks floats allocator exec store platform instIndex function position
    inst code dst bits found functionFound frames fetched pcBound capacity)
  rintro out ⟨success,next,nextValue,slots,storeEq,platformEq⟩
  refine ⟨success,?_⟩
  rw [storeEq]
  have wf := segmentState_wf view sourceCode store ambient code exec.slots.val dst.val (.Const32 dst bits :: rest)
    shape sourceSyntax ambientWf
  have values := segmentPending_set exec.slots.val dst.val bits capacity
  have same : segmentState view sourceCode store ambient code out.2.1.slots.val (dst.val+1) rest =
      segmentState view sourceCode store ambient code exec.slots.val dst.val (.Const32 dst bits :: rest) := by
    simp only [segmentState,slots.1,values,vals,List.map_append,List.map_cons,List.map_nil,
      admininstr_val,Code.segmentSource,List.flatMap_cons,Code.segmentInstructionSource,List.append_assoc]
    rfl
  rw [same]
  exact .refl wf

theorem segment_step_global_source (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (instIndex function : Usize) (position : U32)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction) (index : U32)
    (address : runtime.GlobalAddr) (value : runtime.store.GlobalInst) (rest : List runtime.bytecode.Instr)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[function.val]? = some code)
    (frames : exec.frames.val = [initializerFrame instIndex function position])
    (fetched : code.code.val[position.val]? = some (.GlobalGet 0#u32 index))
    (pcBound : position.val < U32.max) (capacity : 1 ≤ exec.slots.length)
    (mapped : inst.globals.val[index.val]? = some address) (issued : store.globals.val[address.index.val]? = some value)
    (typed : value.ty.valtype = .I32)
    (shape : Shape view store) (sourceSyntax : StoreSyntax sourceCode store) (ambient : frame) (ambientWf : wf_frame ambient)
    (moduleEq : ambient.MODULE = decodeInstance store inst) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ StepsH
        (segmentState view sourceCode store ambient code exec.slots.val 0 (.GlobalGet 0#u32 index :: rest)) []
        (segmentState view sourceCode out.2.2.1 ambient code out.2.1.slots.val 1 rest) ⦄ := by
  apply WP.spec_mono (segment_step_read memory hooks floats allocator exec store platform instIndex function position
    inst code _ [value.lo] found functionFound (.global index address value mapped issued)
    (by simpa using capacity) frames fetched pcBound)
  rintro out ⟨success,slots,next,nextValue,frames,storeEq,platformEq⟩
  refine ⟨success,?_⟩
  rw [storeEq]
  have read := segment_global_source view sourceCode store inst ambient index address value moduleEq mapped issued typed
    shape sourceSyntax ambientWf
  have lifted := Spec.stepsH_instrs (Spec.stepsH_single read) [] (Code.segmentSource code rest)
    (by simp [Forall]) (Code.segmentSource_wf code rest)
  have values : segmentPending out.2.1.slots.val 1 = [segmentValue value.lo] := by
    rw [slots]
    exact segmentPending_one_set _ _ (by change 1 ≤ exec.slots.val.length at capacity; omega)
  simpa only [Spec.instrContext,segmentState,segmentPending_zero,vals,List.map_nil,List.nil_append,
    Code.segmentSource,List.flatMap_cons,Code.segmentInstructionSource,values] using lifted

theorem segment_step_bulk_source (laws : Platform.MemoryLaws memory view)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (instIndex function : Usize) (position : U32) (inst : runtime.store.ModuleInst)
    (code : runtime.bytecode.CompiledFunction) (instruction : runtime.bytecode.Instr) (rest : List runtime.bytecode.Instr)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[function.val]? = some code)
    (frames : exec.frames.val = [initializerFrame instIndex function position])
    (fetched : code.code.val[position.val]? = some instruction) (pcBound : position.val < U32.max)
    (ready : SegmentBulkReady store inst code instruction) (compatible : SegmentBulkCompatible store inst code instruction)
    (capacity : segmentArity instruction ≤ exec.slots.length)
    (shape : Shape view store) (sourceSyntax : StoreSyntax sourceCode store) (bounds : SegmentBounds store)
    (ambient : frame) (ambientWf : wf_frame ambient) (moduleEq : ambient.MODULE = decodeInstance store inst) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      StepsH (segmentState view sourceCode store ambient code exec.slots.val (segmentArity instruction) (instruction :: rest)) []
        ⟨⟨decodeStore view sourceCode out.2.2.1,ambient⟩,segmentAfter out.1 (Code.segmentSource code rest)⟩ ⦄ := by
  apply WP.spec_mono (segment_step_bulk memory hooks floats allocator exec store platform instIndex function position inst code
    instruction ready.kind found functionFound frames fetched pcBound _
    (segment_bulk_source memory view laws sourceCode store instIndex function (alloc.vec.Vec.deref exec.slots) inst code
      instruction ambient found functionFound ready compatible (by simpa [alloc.vec.Vec.deref,Slice.length,alloc.vec.Vec.length] using capacity) shape sourceSyntax bounds ambientWf moduleEq))
  rintro out ⟨next,nextValue,execution,platform,steps⟩
  have lifted := segment_steps_suffix _ _ _ out.1 (Code.segmentSource code rest) steps (Code.segmentSource_wf code rest)
  simpa only [Spec.instrContext,segmentState,Code.segmentSource,List.flatMap_cons,vals,List.map_nil,List.nil_append,
    List.append_assoc,alloc.vec.Vec.deref,Slice.from_val] using lifted

end Exec.Store

namespace Exec.Store
open Aeneas Aeneas.Std SpecExt Exec.Interp

theorem segment_instruction_source {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (sourceCode : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (instIndex function : Usize) (position : U32) (inst : runtime.store.ModuleInst)
    (code : runtime.bytecode.CompiledFunction) (instruction : runtime.bytecode.Instr) (rest : List runtime.bytecode.Instr)
    (pending : Nat) (flow : Code.SegmentFlow pending (instruction :: rest))
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[function.val]? = some code)
    (frames : exec.frames.val = [initializerFrame instIndex function position])
    (fetched : code.code.val[position.val]? = some instruction) (pcBound : position.val < U32.max)
    (ready : SegmentInstructionReady store inst code exec.slots.length instruction)
    (compatible : SegmentBulkCompatible store inst code instruction)
    (globals : ∀ index address value, instruction = .GlobalGet 0#u32 index →
      inst.globals.val[index.val]? = some address → store.globals.val[address.index.val]? = some value → value.ty.valtype = .I32)
    (shape : Shape view store) (sourceSyntax : StoreSyntax sourceCode store) (bounds : SegmentBounds store)
    (ambient : frame) (ambientWf : wf_frame ambient) (moduleEq : ambient.MODULE = decodeInstance store inst) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      ∃ nextPending, (rest = [] ∧ nextPending = 0 ∨ Code.SegmentFlow nextPending rest) ∧
      StepsH (segmentState view sourceCode store ambient code exec.slots.val pending (instruction :: rest)) []
        ⟨⟨decodeStore view sourceCode out.2.2.1,ambient⟩,
          segmentAfter out.1 (vals (segmentPending out.2.1.slots.val nextPending) ++ Code.segmentSource code rest)⟩ ⦄ := by
  cases flow with
  | done =>
    apply WP.spec_mono (segment_step_return memory hooks floats allocator exec store platform instIndex function position
      inst code 0#u32 found functionFound (by simp) frames fetched pcBound)
    rintro out ⟨success,slots,empty,storeEq,platformEq⟩
    refine ⟨0,Or.inl ⟨rfl,rfl⟩,?_⟩
    have wf := segmentState_wf view sourceCode store ambient code exec.slots.val 0 [.Return 0#u32 0#u32] shape sourceSyntax ambientWf
    simpa [segmentState,segmentPending,vals,Code.segmentSource,Code.segmentInstructionSource,segmentAfter,success,storeEq] using StepsH.refl wf
  | constant pending dst bits rest slot bound next =>
    have capacity : dst.val < exec.slots.length := by
      cases ready with
      | constant _ _ capacity => exact capacity
      | bulk _ impossible _ => cases impossible
    apply WP.spec_mono (segment_step_constant_source memory hooks floats allocator view sourceCode exec store platform
      instIndex function position inst code dst bits rest found functionFound frames fetched pcBound capacity
      shape sourceSyntax ambient ambientWf)
    rintro out ⟨success,steps⟩
    refine ⟨pending+1,Or.inr next,?_⟩
    simpa only [slot,segmentState,success,segmentAfter] using steps
  | global index rest next =>
    cases ready with
    | global _ address value mapped issued capacity =>
      apply WP.spec_mono (segment_step_global_source memory hooks floats allocator view sourceCode exec store platform
        instIndex function position inst code index address value rest found functionFound frames fetched pcBound capacity
        mapped issued (globals index address value rfl mapped issued) shape sourceSyntax ambient ambientWf moduleEq)
      rintro out ⟨success,steps⟩
      refine ⟨1,Or.inr next,?_⟩
      simpa only [segmentState,success,segmentAfter] using steps
    | bulk _ impossible _ => cases impossible
  | memory data rest next | table data rest next | dataDrop data rest next | elementDrop data rest next =>
    cases ready with
    | bulk _ bulkReady capacity =>
      apply WP.spec_mono (segment_step_bulk_source memory hooks floats allocator view sourceCode laws exec store platform
        instIndex function position inst code _ rest found functionFound frames fetched pcBound bulkReady compatible
        (by first | exact capacity ⟨data,Or.inl rfl⟩ | exact capacity ⟨data,Or.inr rfl⟩ | simp [segmentArity])
        shape sourceSyntax bounds ambient ambientWf moduleEq)
      intro out steps
      refine ⟨0,Or.inr next,?_⟩
      simpa only [segmentArity,segmentState,segmentPending_zero,vals,List.map_nil,List.nil_append] using steps

end Exec.Store
