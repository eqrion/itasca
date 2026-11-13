import Itasca.Runtime.Store.Initialization.ElementLoop
import Itasca.Runtime.Spec.SegmentInitCases
import Itasca.Runtime.Spec.Integer
import Itasca.Runtime.Store.Initialization.SegmentLoop
import Itasca.Runtime.Store.Api.GrowthLimits
import Itasca.Runtime.Store.Invariant.Syntax
import Itasca.Runtime.Store.Initialization.SegmentDrop
import Itasca.Runtime.Store.Initialization.SegmentObjectEffects
import Itasca.Runtime.Compiler.Local.Relations.Segments.SegmentTranslation
import Itasca.Runtime.Store.Initialization.SegmentReady
import Itasca.Runtime.Store.Initialization.SegmentSyntheticPreservation
import Itasca.Runtime.Store.Initialization.SegmentExtension
import Itasca.Runtime.Interp.Relations.SourceClosure
import Itasca.Runtime.Interp.Relations.SyntheticInitializerCauses
import Itasca.Runtime.Store.Initialization.SegmentInitializePreservation
import Itasca.Runtime.Compiler.Local.Relations.Segments.SegmentFlowSource

/-!
Sections, each formerly its own module: SegmentLoopSource, SegmentSyntheticSource, SegmentInitializeSource, InitializerResourceCauses.
-/

/-! ## SegmentLoopSource -/

section

/-!
Source correspondence for the segment initialization loop. Pending operand encoding and per-instruction source reductions compose into the loop result, including the terminal return.
-/

/-! ## Segment Pending -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std SpecExt

def segmentValue (word : U64) : val := .CONST .I32 (.mk_num__0 .I32 (.mk_uN (bulkWord word).val))
def segmentPending (slots : List U64) (count : Nat) : List val := (slots.take count).map segmentValue

theorem segment_value_wf (word : U64) : wf_val (segmentValue word) := by
  constructor
  exact .num__case_0 .I32 .I32 _ (by decide) (Spec.Segment.index_wf _ (by scalar_tac)) rfl

theorem segment_pending_wf (slots : List U64) (count : Nat) : Forall wf_val (segmentPending slots count) := by
  intro value member
  obtain ⟨word,_,rfl⟩ := List.mem_map.mp member
  exact segment_value_wf word

theorem segment_pending_zero (slots : List U64) : segmentPending slots 0 = [] := rfl

theorem segment_pending_set (slots : List U64) (count : Nat) (bits : U32) (inside : count < slots.length) :
    segmentPending (slots.set count (UScalar.cast .U64 bits)) (count+1) =
      segmentPending slots count ++ [.CONST .I32 (.mk_num__0 .I32 (.mk_uN bits.val))] := by
  have bound : count < (slots.set count (UScalar.cast .U64 bits)).length := by simpa using inside
  unfold segmentPending
  rw [List.take_succ_eq_append_getElem bound,List.take_set_of_le (Nat.le_refl count)]
  simp only [List.map_append,List.map_cons,List.map_nil,List.getElem_set_self]
  congr 2
  unfold segmentValue
  have exactBits : (bulkWord (UScalar.cast .U64 bits)).val = bits.val := by scalar_tac
  rw [exactBits]

theorem segment_pending_three (slots : List U64) (a b c : U64)
    (first : slots[0]? = some a) (second : slots[1]? = some b) (third : slots[2]? = some c) :
    vals (segmentPending slots 3) = Spec.Segment.operands (bulkWord a).val (bulkWord b).val (bulkWord c).val := by
  cases slots with
  | nil => simp at first
  | cons x xs =>
    simp only [List.getElem?_cons_zero,Option.some.injEq] at first
    subst x
    cases xs with
    | nil => simp at second
    | cons y ys =>
      simp only [List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq] at second
      subst y
      cases ys with
      | nil => simp at third
      | cons z zs =>
        simp only [List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq] at third
        subst z
        rfl

end Itasca.Runtime.Store

end

/-! ## Segment Step Source -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std SpecExt

def segmentAfter (status : core.result.Result Unit runtime.ExecError) (after : List admininstr) : List admininstr :=
  match status with | .Ok _ => after | .Err _ => [.TRAP]

theorem segment_steps_suffix (first : config) (s : store) (f : frame)
    (status : core.result.Result Unit runtime.ExecError) (after : List admininstr)
    (steps : StepsH first [] ⟨⟨s,f⟩,segmentResult status⟩)
    (afterWf : Forall wf_admininstr after) :
    StepsH (Spec.instrContext [] after first) [] ⟨⟨s,f⟩,segmentAfter status after⟩ := by
  have lifted := Spec.steps_h_instrs steps [] after (by simp [Forall]) afterWf
  cases status with
  | Ok _unitValue => simpa [Spec.instrContext,vals,segmentResult,segmentAfter] using lifted
  | Err error =>
    have wf := (Spec.steps_h_wf steps).2
    by_cases empty : after = []
    · subst after
      simpa [Spec.instrContext,vals,segmentResult,segmentAfter] using lifted
    · have input := (Spec.steps_h_wf lifted).2
      have trap : StepH (Spec.instrContext [] after ⟨⟨s,f⟩,segmentResult (.Err error)⟩) [] ⟨⟨s,f⟩,[.TRAP]⟩ :=
        .step (.pure _ _ _ (.trap_vals [] after (Or.inr empty) (by simp [Forall]) afterWf .admininstr_case_73) input wf)
      exact Spec.steps_h_trans lifted (Spec.steps_h_single trap)

end Itasca.Runtime.Store

namespace Itasca.Runtime.Store
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
  have wf := decode_store_wf view code store shape sourceSyntax
  have input := Spec.wf_config_make wf ambientWf
    (show Forall wf_admininstr [.GLOBAL_GET (.mk_uN index.val)] from by
      simpa [Forall] using wf_admininstr.admininstr_case_46 _ (Spec.Segment.index_wf _ (by scalar_tac)))
  have output := Spec.wf_config_vals wf ambientWf (show Forall wf_val [segmentValue value.lo] from by
    simpa [Forall] using segment_value_wf value.lo)
  apply StepH.step
  apply Step.read _ _ _ ?_ input output
  have read := Step_read.global_get ⟨decodeStore view code store,ambient⟩ (.mk_uN index.val) input
  have bits : (bulkWord value.lo).val = value.lo.val % 2^32 := by scalar_tac
  simpa only [fetched,decodeGlobal,typed,decodeWords,vals,List.map_cons,List.map_nil,segmentValue,admininstr_val,bits] using read

end Itasca.Runtime.Store

namespace Itasca.Runtime.Store
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
        vals (segmentPending slots.val (segmentArity instruction)) ++ Compiler.segmentInstructionSource compiled instruction⟩ []
        ⟨⟨decodeStore view sourceCode out.2,ambient⟩,segmentResult out.1⟩ ⦄ := by
  cases ready with
  | memory data address memoryAddress mapped issued mappedMemory issuedMemory =>
    obtain ⟨a,b,c,ha,hb,hc⟩ := slot_triple slots capacity
    let dataValue := store.datas.val[address.val]
    let memoryValue := store.memories.val[memoryAddress.index.val]
    have dataFound : store.datas.val[address.val]? = some dataValue := List.getElem?_eq_getElem issued
    have memoryFound : store.memories.val[memoryAddress.index.val]? = some memoryValue := List.getElem?_eq_getElem issuedMemory
    simpa only [segmentArity,segment_pending_three slots.val a b c ha hb hc,Compiler.segmentInstructionSource] using
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
    simpa only [segmentArity,segment_pending_three slots.val a b c ha hb hc,Compiler.segmentInstructionSource,
      List.getElem!_eq_getElem?_getD,descriptor,Option.getD_some] using
      bulk_table_init_refines memory view sourceCode store instIndex function slots inst compiled entry element tableId address
        tableAddress tableValue elementValue a b c ambient found functionFound descriptor mapped elementFound mappedTable tableFound
        ha hb hc sameType.symm shape sourceSyntax ambientWf moduleEq (bounds.elements elementValue (List.mem_of_getElem? elementFound))
  | dataDrop data address mapped issued =>
    apply WP.spec_mono (bulk_data_drop_refines memory view sourceCode store instIndex function 0#usize slots inst data address ambient
      found mapped issued shape sourceSyntax ambientWf moduleEq)
    rintro out ⟨success,step⟩
    simpa [segmentArity,segmentPending,vals,Compiler.segmentInstructionSource,success,segmentResult] using Spec.steps_h_single step
  | elementDrop element address mapped issued =>
    apply WP.spec_mono (bulk_element_drop_refines memory view sourceCode store instIndex function 0#usize slots inst element address ambient
      found mapped issued shape sourceSyntax ambientWf moduleEq)
    rintro out ⟨success,step⟩
    simpa [segmentArity,segmentPending,vals,Compiler.segmentInstructionSource,success,segmentResult] using Spec.steps_h_single step

end Itasca.Runtime.Store

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std SpecExt

def segmentState {M : Type} (view : M → Slice U8) (source : CodeInterpretation)
    (store : runtime.store.Store M) (ambient : frame) (code : runtime.bytecode.CompiledFunction)
    (slots : List U64) (pending : Nat) (remaining : List runtime.bytecode.Instr) : config :=
  ⟨⟨decodeStore view source store,ambient⟩,vals (segmentPending slots pending) ++ Compiler.segmentSource code remaining⟩

theorem segment_state_wf {M : Type} (view : M → Slice U8) (source : CodeInterpretation)
    (store : runtime.store.Store M) (ambient : frame) (code : runtime.bytecode.CompiledFunction)
    (slots : List U64) (pending : Nat) (remaining : List runtime.bytecode.Instr)
    (shape : Shape view store) (sourceSyntax : StoreSyntax source store) (frameWf : wf_frame ambient) :
    wf_config (segmentState view source store ambient code slots pending remaining) :=
  Spec.wf_config_make (decode_store_wf view source store shape sourceSyntax) frameWf
    (Spec.forall_append (Spec.wf_vals (segment_pending_wf slots pending)) (Compiler.segment_source_wf code remaining))

theorem segment_pending_one_set (slots : List U64) (word : U64) (inside : 0 < slots.length) :
    segmentPending (slots.set 0 word) 1 = [segmentValue word] := by
  cases slots with
  | nil => simp at inside
  | cons a rest => rfl

end Itasca.Runtime.Store
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

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
  have wf := segment_state_wf view sourceCode store ambient code exec.slots.val dst.val (.Const32 dst bits :: rest)
    shape sourceSyntax ambientWf
  have values := segment_pending_set exec.slots.val dst.val bits capacity
  have same : segmentState view sourceCode store ambient code out.2.1.slots.val (dst.val+1) rest =
      segmentState view sourceCode store ambient code exec.slots.val dst.val (.Const32 dst bits :: rest) := by
    simp only [segmentState,slots.1,values,vals,List.map_append,List.map_cons,List.map_nil,
      admininstr_val,Compiler.segmentSource,List.flatMap_cons,Compiler.segmentInstructionSource,List.append_assoc]
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
  have lifted := Spec.steps_h_instrs (Spec.steps_h_single read) [] (Compiler.segmentSource code rest)
    (by simp [Forall]) (Compiler.segment_source_wf code rest)
  have values : segmentPending out.2.1.slots.val 1 = [segmentValue value.lo] := by
    rw [slots]
    exact segment_pending_one_set _ _ (by change 1 ≤ exec.slots.val.length at capacity; omega)
  simpa only [Spec.instrContext,segmentState,segment_pending_zero,vals,List.map_nil,List.nil_append,
    Compiler.segmentSource,List.flatMap_cons,Compiler.segmentInstructionSource,values] using lifted

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
        ⟨⟨decodeStore view sourceCode out.2.2.1,ambient⟩,segmentAfter out.1 (Compiler.segmentSource code rest)⟩ ⦄ := by
  apply WP.spec_mono (segment_step_bulk memory hooks floats allocator exec store platform instIndex function position inst code
    instruction ready.kind found functionFound frames fetched pcBound _
    (segment_bulk_source memory view laws sourceCode store instIndex function (alloc.vec.Vec.deref exec.slots) inst code
      instruction ambient found functionFound ready compatible (by simpa [alloc.vec.Vec.deref,Slice.length,alloc.vec.Vec.length] using capacity) shape sourceSyntax bounds ambientWf moduleEq))
  rintro out ⟨next,nextValue,execution,platform,steps⟩
  have lifted := segment_steps_suffix _ _ _ out.1 (Compiler.segmentSource code rest) steps (Compiler.segment_source_wf code rest)
  simpa only [Spec.instrContext,segmentState,Compiler.segmentSource,List.flatMap_cons,vals,List.map_nil,List.nil_append,
    List.append_assoc,alloc.vec.Vec.deref,Slice.from_val] using lifted

end Itasca.Runtime.Store

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

theorem segment_instruction_source {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (sourceCode : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (instIndex function : Usize) (position : U32) (inst : runtime.store.ModuleInst)
    (code : runtime.bytecode.CompiledFunction) (instruction : runtime.bytecode.Instr) (rest : List runtime.bytecode.Instr)
    (pending : Nat) (flow : Compiler.SegmentFlow pending (instruction :: rest))
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
      ∃ nextPending, (rest = [] ∧ nextPending = 0 ∨ Compiler.SegmentFlow nextPending rest) ∧
      StepsH (segmentState view sourceCode store ambient code exec.slots.val pending (instruction :: rest)) []
        ⟨⟨decodeStore view sourceCode out.2.2.1,ambient⟩,
          segmentAfter out.1 (vals (segmentPending out.2.1.slots.val nextPending) ++ Compiler.segmentSource code rest)⟩ ⦄ := by
  cases flow with
  | done =>
    apply WP.spec_mono (segment_step_return memory hooks floats allocator exec store platform instIndex function position
      inst code 0#u32 found functionFound (by simp) frames fetched pcBound)
    rintro out ⟨success,slots,empty,storeEq,platformEq⟩
    refine ⟨0,Or.inl ⟨rfl,rfl⟩,?_⟩
    have wf := segment_state_wf view sourceCode store ambient code exec.slots.val 0 [.Return 0#u32 0#u32] shape sourceSyntax ambientWf
    simpa [segmentState,segmentPending,vals,Compiler.segmentSource,Compiler.segmentInstructionSource,segmentAfter,success,storeEq] using StepsH.refl wf
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
      simpa only [segmentArity,segmentState,segment_pending_zero,vals,List.map_nil,List.nil_append] using steps

end Itasca.Runtime.Store

end

/-! ## Segment Loop Source -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

private theorem flow_return {pending : Nat} {instruction : runtime.bytecode.Instr} {rest : List runtime.bytecode.Instr}
    (flow : Compiler.SegmentFlow pending (instruction :: rest)) (returns : segmentReturns instruction = true) :
    rest = [] := by
  cases flow <;> simp_all [segmentReturns]

theorem segment_loop_source {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (sourceCode : CodeInterpretation)
    (store : runtime.store.Store M) (platform : P) (exec : runtime.interp.Execution)
    (instIndex function : Usize) (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (position : U32) (pending : Nat)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[function.val]? = some code)
    (frames : exec.frames.val = [initializerFrame instIndex function position])
    (positionBound : position.val < code.code.length)
    (ready : SegmentCodeReady store inst code exec.slots.length)
    (flow : Compiler.SegmentFlow pending (code.code.val.drop position.val))
    (compatible : ∀ instruction ∈ code.code.val, SegmentBulkCompatible store inst code instruction)
    (globals : ∀ index address value, .GlobalGet 0#u32 index ∈ code.code.val →
      inst.globals.val[index.val]? = some address → store.globals.val[address.index.val]? = some value → value.ty.valtype = .I32)
    (shape : Shape view store) (sourceSyntax : StoreSyntax sourceCode store) (bounds : SegmentBounds store)
    (ambient : frame) (ambientWf : wf_frame ambient) (moduleEq : ambient.MODULE = decodeInstance store inst) :
    runtime.interp.run_synthetic_loop memory hooks floats allocator store platform exec (.Ok ()) ⦃ out =>
      StepsH (segmentState view sourceCode store ambient code exec.slots.val pending (code.code.val.drop position.val)) []
        ⟨⟨decodeStore view sourceCode out.1,ambient⟩,segmentResult out.2.2.2⟩ ⦄ := by
  let origin := segmentState view sourceCode store ambient code exec.slots.val pending (code.code.val.drop position.val)
  unfold runtime.interp.run_synthetic_loop
  apply loop.spec_decr_nat (fun state => segmentRemaining code state.2.2.1 state.2.2.2)
    (fun state => Shape view state.1 ∧ SegmentTypes store state.1 ∧ SegmentObjectMetadata view store state.1 ∧
      state.2.1 = platform ∧ state.2.2.1.slots.length = exec.slots.length ∧ SegmentStatus state.2.2.2 ∧
      ((state.2.2.1.frames.val = [] ∧ StepsH origin [] ⟨⟨decodeStore view sourceCode state.1,ambient⟩,segmentResult state.2.2.2⟩) ∨
        ∃ pc : U32, ∃ n : Nat, state.2.2.1.frames.val = [initializerFrame instIndex function pc] ∧
          pc.val < code.code.length ∧ Compiler.SegmentFlow n (code.code.val.drop pc.val) ∧
          StepsH origin [] ⟨⟨decodeStore view sourceCode state.1,ambient⟩,
            segmentAfter state.2.2.2 (vals (segmentPending state.2.2.1.slots.val n) ++ Compiler.segmentSource code (code.code.val.drop pc.val))⟩))
  · rintro ⟨current,host,machine,result⟩ ⟨currentShape,types,objects,hostEq,slots,status,cursor⟩
    dsimp only at currentShape types objects hostEq slots status cursor ⊢
    subst host
    cases result with
    | Err error =>
      simp only [runtime.interp.run_synthetic_loop.body,core.result.Result.is_ok,bind_ok,Bool.false_eq_true,↓reduceIte,ite_self,WP.spec_ok]
      rcases cursor with ⟨_,history⟩ | ⟨pc,n,_,_,_,history⟩
      · exact history
      · exact history
    | Ok unitValue =>
      cases unitValue
      rcases cursor with ⟨empty,history⟩ | ⟨pc,n,currentFrames,pcBound,currentFlow,history⟩
      · rw [synthetic_body_done memory hooks floats allocator machine current platform empty]
        simpa only [WP.spec_ok] using history
      · rw [synthetic_body_active memory hooks floats allocator machine current platform
          (by simp [alloc.vec.Vec.length,currentFrames])]
        have currentFound : current.instances.val[instIndex.val]? = some inst := by rw [objects.space.instances]; exact found
        have currentReady : SegmentCodeReady current inst code machine.slots.length := by
          rw [slots]; exact ready.transport objects.space
        let instruction := code.code.val[pc.val]
        let rest := code.code.val.drop (pc.val+1)
        have fetched : code.code.val[pc.val]? = some instruction := List.getElem?_eq_getElem pcBound
        have tail : code.code.val.drop pc.val = instruction :: rest := List.drop_eq_getElem_cons pcBound
        have currentCompatible := (compatible instruction (List.mem_of_getElem? fetched)).transport types
        have currentSyntax := sourceSyntax.instances_eq objects.space.instances
        have currentModuleEq : ambient.MODULE = decodeInstance current inst := by
          simpa only [decodeInstance,objects.space.signatures] using moduleEq
        have safe := segment_instruction_total memory hooks floats allocator view laws machine current platform instIndex function pc
          inst code instruction currentFound functionFound currentFrames fetched (lt_trans pcBound ready.size)
          (currentReady.instructions instruction (List.mem_of_getElem? fetched))
        have shaped := segment_instruction_shape memory hooks floats allocator view laws machine current platform instIndex function pc
          inst code instruction currentFound functionFound currentFrames fetched (lt_trans pcBound ready.size)
          (currentReady.instructions instruction (List.mem_of_getElem? fetched)) currentCompatible currentShape
        have metadata := segment_instruction_object_metadata memory hooks floats allocator view laws machine current platform instIndex function pc
          inst code instruction currentFound functionFound currentFrames fetched (lt_trans pcBound ready.size)
          (currentReady.instructions instruction (List.mem_of_getElem? fetched))
        have simulated := segment_instruction_source memory hooks floats allocator view laws sourceCode machine current platform instIndex function pc
          inst code instruction rest n (tail ▸ currentFlow) currentFound functionFound currentFrames fetched (lt_trans pcBound ready.size)
          (currentReady.instructions instruction (List.mem_of_getElem? fetched)) currentCompatible
          (by intro index address value instructionEq mapped issued
              apply globals index address value (instructionEq ▸ List.mem_of_getElem? fetched) mapped
              rw [objects.space.globals] at issued; exact issued)
          currentShape currentSyntax (objects.segment_bounds bounds) ambient ambientWf currentModuleEq
        step with segment_specs_and (segment_specs_and safe shaped) (segment_specs_and metadata simulated)
          as ⟨result,next,after,host,effect,newShape,newTypes,newObjects,nextPending,residual,reduction⟩
        change SegmentStepEffect machine current platform instIndex function pc instruction (result,next,after,host) at effect
        change (rest = [] ∧ nextPending = 0 ∨ Compiler.SegmentFlow nextPending rest) at residual
        have nextObjects := objects.trans newObjects
        have nextTypes := types.trans newTypes
        have nextSlots := effect.slots.trans slots
        have nextHost := effect.platform
        dsimp only at nextObjects nextTypes nextSlots nextHost
        subst host
        have combined : StepsH origin [] ⟨⟨decodeStore view sourceCode after,ambient⟩,
            segmentAfter result (vals (segmentPending next.slots.val nextPending) ++ Compiler.segmentSource code rest)⟩ := by
          have previous : StepsH origin [] (segmentState view sourceCode current ambient code machine.slots.val n (instruction::rest)) := by
            simpa only [segmentState,segmentAfter,tail] using history
          exact Spec.steps_h_trans previous reduction
        have nextFrames := effect.frames
        cases returns : segmentReturns instruction with
        | true =>
          have tailNil : rest = [] := flow_return (tail ▸ currentFlow) returns
          have pendingZero : nextPending = 0 := by
            rcases residual with ⟨_,same⟩ | flow
            · exact same
            · rw [tailNil] at flow; cases flow
          simp only [returns,↓reduceIte] at nextFrames
          refine ⟨newShape,nextTypes,nextObjects,rfl,nextSlots,effect.status,Or.inl ⟨nextFrames,?_⟩,?_⟩
          · cases result <;> simpa [pendingZero,tailNil,segmentPending,vals,Compiler.segmentSource,segmentAfter,segmentResult] using combined
          · cases result <;> simp [segmentRemaining,nextFrames,currentFrames,initializerFrame]
        | false =>
          simp only [returns,Bool.false_eq_true,↓reduceIte] at nextFrames
          obtain ⟨nextPc,nextValue,nextFrames⟩ := nextFrames
          have nextBound : nextPc.val < code.code.length := by have := ready.next_bound fetched returns; omega
          have nextFlow : Compiler.SegmentFlow nextPending rest := by
            rcases residual with ⟨empty,_⟩ | flow
            · have tooFar := List.drop_eq_nil_iff.mp empty
              change code.code.val.length ≤ pc.val+1 at tooFar
              change nextPc.val < code.code.val.length at nextBound
              omega
            · exact flow
          refine ⟨newShape,nextTypes,nextObjects,rfl,nextSlots,effect.status,
            Or.inr ⟨nextPc,nextPending,nextFrames,nextBound,?_,?_⟩,?_⟩
          · simpa only [nextValue] using nextFlow
          · simpa only [nextValue] using combined
          · cases result <;> simp only [segmentRemaining,nextFrames,currentFrames,initializerFrame]
            all_goals omega
  · refine ⟨shape,.refl _,.refl _ _,rfl,rfl,Or.inl rfl,Or.inr ⟨position,pending,frames,positionBound,flow,?_⟩⟩
    exact StepsH.refl (segment_state_wf view sourceCode store ambient code exec.slots.val pending _ shape sourceSyntax ambientWf)

end Itasca.Runtime.Store

end

end

/-! ## SegmentSyntheticSource -/

section

/-!
Source correspondence and resource-cause classification for synthetic segment execution. This is separate from the lightweight totality and metadata certificates.
-/

/-! ## Segment Synthetic Source -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std SpecExt
open Itasca.Runtime.Interp

/-- Segment execution can fail only at a memory or table range check. -/
def SegmentExecutionStatus {T : Type} (result : core.result.Result T runtime.ExecError) : Prop :=
  match result with
  | .Ok _ => True
  | .Err error => error = .Trap .MemoryOutOfBounds ∨ error = .Trap .TableOutOfBounds

end Itasca.Runtime.Store

end

/-! ## Segment Synthetic Causes -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std SpecExt
open Itasca.Runtime.Interp

/-- The actual synthetic segment entry point either refuses setup allocation
without changing the store, or follows the generated source reductions through
success or a range trap, retaining any earlier segment writes. -/
theorem segment_synthetic_source_causes {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex function : Usize)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[function.val]? = some code)
    (ready : SegmentCodeReady store inst code code.slot_count.val)
    (sourceCode : CodeInterpretation) (flow : Compiler.SegmentFlow 0 code.code.val)
    (compatible : ∀ instruction ∈ code.code.val, SegmentBulkCompatible store inst code instruction)
    (globals : ∀ index address value, .GlobalGet 0#u32 index ∈ code.code.val →
      inst.globals.val[index.val]? = some address → store.globals.val[address.index.val]? = some value → value.ty.valtype = .I32)
    (shape : Shape view store) (sourceSyntax : StoreSyntax sourceCode store) (bounds : SegmentBounds store)
    (ambient : frame) (ambientWf : wf_frame ambient) (moduleEq : ambient.MODULE = decodeInstance store inst) :
    runtime.interp.run_synthetic memory hooks floats allocator store platform instIndex function
      ⦃ out => (∃ reason, out.1 = .Err (.Exhausted reason) ∧ out.2.1 = store ∧
        SyntheticPreparationCause allocator store code (.Exhausted reason)) ∨
        SegmentExecutionStatus out.1 ∧ StepsH ⟨⟨decodeStore view sourceCode store,ambient⟩,Compiler.segmentSource code code.code.val⟩ []
          ⟨⟨decodeStore view sourceCode out.2.1,ambient⟩, match out.1 with | .Ok _ => [] | .Err _ => [.TRAP]⟩ ⦄ := by
  unfold runtime.interp.run_synthetic
  step with vec_index_given store.instances instIndex inst found as ⟨actual, equal⟩
  subst actual
  step with vec_index_given inst.module.functions function code functionFound as ⟨actual, equal⟩
  subst actual
  simp only [lift, bind_ok, runtime.interp.Execution.new]
  step with ensure_effect allocator law _ _ _ as ⟨status, prepared, ensured⟩
  cases status with
  | Err error =>
    have cause : SyntheticPreparationCause allocator store code error := by
      cases error <;> simp only [EnsureEffect] at ensured <;> try contradiction
      rename_i resource
      cases resource <;> simp only [EnsureEffect] at ensured <;> try contradiction
      · exact ensured.1
      · obtain ⟨within,needed,same,n,amount,refused⟩ := ensured
        have nEq : n = UScalar.cast .Usize code.slot_count := by
          apply UScalar.eq_of_val_eq
          simpa [alloc.vec.Vec.new,alloc.vec.Vec.length] using amount
        exact Or.inl (by simpa only [nEq] using refused)
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    left
    cases error <;> simp_all [EnsureEffect]
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
      have frameEq : prepared.frames = alloc.vec.Vec.new runtime.interp.Frame := alloc.vec.Vec.ext _ _ frames
      have cause : SyntheticPreparationCause allocator store code (.Exhausted .Allocation) :=
        Or.inr (by simpa only [frameEq] using reserved)
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,cause]
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
      have total := segment_loop_total memory hooks floats allocator view laws store platform
        {prepared with frames := pushed} instIndex function inst code 0#u32 found functionFound pushedFrames
        (by simpa using nonempty) (by simpa only [capacity] using ready)
      have typed := segment_loop_source memory hooks floats allocator view laws sourceCode store platform
        {prepared with frames := pushed} instIndex function inst code 0#u32 0 found functionFound pushedFrames
        (by simpa using nonempty) (by simpa only [capacity] using ready)
        (by simpa using flow) compatible globals shape sourceSyntax bounds ambient ambientWf moduleEq
      step with segment_specs_and total typed
        as ⟨after, host, finalSlots, result, metadata, hostEq, width, status, objects⟩
      subst host
      cases result with
      | Err error =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        exact Or.inr ⟨by simpa [SegmentStatus,SegmentExecutionStatus] using status,
          by simpa [segmentState,segmentPending,vals,segmentResult] using objects⟩
      | Ok unitValue =>
        cases unitValue
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step with get_effect finalSlots.deref 0#usize
        step with get_effect finalSlots.deref 1#usize
        exact Or.inr ⟨trivial, by simpa [segmentState,segmentPending,vals,segmentResult] using objects⟩

end Itasca.Runtime.Store

end

end

/-! ## SegmentInitializeSource -/

section

/-!
Source correspondence and resource causes for complete segment initialization. Setup failures remain distinct from executed segment effects.
-/

/-! ## Segment Initialize Source -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std SpecExt

/-- Ordered source instructions for the retained element and data initialization programs. -/
def segmentModuleSource (module : runtime.compiler.ExecutableModule) : List admininstr :=
  (Spec.Segment.elementPrograms (module.module.env.elements.val.map (fun entry =>
    Itasca.ModuleElaboration.element (Itasca.ModuleEnv.rawElement entry)))).flatten.map admininstr_instr ++
  (Spec.Segment.dataPrograms (module.module.tail.data.val.map (fun entry =>
    Itasca.ModuleData.translate (Itasca.ModuleData.raw entry)))).flatten.map admininstr_instr

/-- Source program indexed by the independent binary module witness. -/
def segmentRawSource (raw : Itasca.ModuleBinary.Module) : List admininstr :=
  (Spec.Segment.elementPrograms (raw.elements.map Itasca.ModuleElaboration.element)).flatten.map admininstr_instr ++
  (Spec.Segment.dataPrograms (raw.data.map Itasca.ModuleData.translate)).flatten.map admininstr_instr

theorem segment_module_source_raw (module : runtime.compiler.ExecutableModule)
    (raw : Itasca.ModuleBinary.Module)
    (matched : Itasca.ModuleElaboration.Matches module.module.env module.module.tail raw) :
    segmentModuleSource module = segmentRawSource raw := by
  have elements := congrArg Itasca.ModuleBinary.Module.elements matched.1
  have datas := congrArg Itasca.ModuleBinary.Module.data matched.1
  simp only [segmentRawSource, elements, datas, Itasca.ModuleElaboration.fromEnv,
    List.map_map, Function.comp_def,segmentModuleSource]

end Itasca.Runtime.Store

end

/-! ## Segment Initialize Causes -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std SpecExt

/-- Exact setup cause for the actual compiled segment initializer. The function
lookup and checked syntactic program prevent an arbitrary slot demand witness. -/
def SegmentSetupCause {M A : Type} (allocator : runtime.platform.Alloc A)
    (store : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (error : runtime.ExecError) : Prop :=
  ∃ code, module.functions.val[module.initialization.val]? = some code ∧
    Compiler.SegmentProgram module code ∧ Interp.SyntheticPreparationCause allocator store code error

theorem initialize_segments_source_causes {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex : Usize)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[inst.module.initialization.val]? = some code)
    (ready : SegmentCodeReady store inst code code.slot_count.val)
    (sourceCode : CodeInterpretation) (flow : Compiler.SegmentFlow 0 code.code.val)
    (compatible : ∀ instruction ∈ code.code.val, SegmentBulkCompatible store inst code instruction)
    (globals : ∀ index address value, .GlobalGet 0#u32 index ∈ code.code.val →
      inst.globals.val[index.val]? = some address → store.globals.val[address.index.val]? = some value → value.ty.valtype = .I32)
    (shape : Shape view store) (sourceSyntax : StoreSyntax sourceCode store) (bounds : SegmentBounds store)
    (ambient : frame) (ambientWf : wf_frame ambient) (moduleEq : ambient.MODULE = decodeInstance store inst) :
    runtime.interp.initialize_segments memory hooks floats allocator store platform instIndex
      ⦃ out => (∃ reason, out.1 = .Err (.Exhausted reason) ∧ out.2.1 = store ∧
        Interp.SyntheticPreparationCause allocator store code (.Exhausted reason)) ∨
        SegmentExecutionStatus out.1 ∧ StepsH ⟨⟨decodeStore view sourceCode store,ambient⟩,Compiler.segmentSource code code.code.val⟩ []
          ⟨⟨decodeStore view sourceCode out.2.1,ambient⟩, segmentResult out.1⟩ ⦄ := by
  unfold runtime.interp.initialize_segments
  step with Interp.vec_index_given store.instances instIndex inst found as ⟨actual, equal⟩
  subst actual
  step with segment_synthetic_source_causes memory hooks floats allocator view laws law store platform instIndex
    inst.module.initialization inst code found functionFound ready sourceCode flow compatible globals
    shape sourceSyntax bounds ambient ambientWf moduleEq as ⟨result,after,host,outcome⟩
  cases result <;> simp_all [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,segmentResult,SegmentExecutionStatus]

/-- Accepted compilation supplies the complete segment program correspondence;
only setup exhaustion can precede the source execution. -/
theorem initialize_segments_compiled_source_causes {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex : Usize)
    (inst : runtime.store.ModuleInst) (bytes : Slice U8)
    (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes limits = .ok (.Ok inst.module))
    (found : store.instances.val[instIndex.val]? = some inst)
    (sourceCode : CodeInterpretation) (shape : Shape view store)
    (sourceSyntax : StoreSyntax sourceCode store) (bounds : SegmentBounds store)
    (imports : InitializerImports store inst) (bindings : InitializerBindings store inst)
    (types : SegmentTypeBindings store inst)
    (ambient : frame) (ambientWf : wf_frame ambient) (moduleEq : ambient.MODULE = decodeInstance store inst) :
    runtime.interp.initialize_segments memory hooks floats allocator store platform instIndex
      ⦃ out => (∃ reason, out.1 = .Err (.Exhausted reason) ∧ out.2.1 = store ∧
        SegmentSetupCause allocator store inst.module (.Exhausted reason)) ∨
        SegmentExecutionStatus out.1 ∧ StepsH ⟨⟨decodeStore view sourceCode store,ambient⟩,segmentModuleSource inst.module⟩ []
          ⟨⟨decodeStore view sourceCode out.2.1,ambient⟩,segmentResult out.1⟩ ⦄ := by
  obtain ⟨witness⟩ := Compiler.compile_accepted allocator bytes limits inst.module accepted
  obtain ⟨code, functionFound, program⟩ := witness.segment_program law
  obtain ⟨valid, dataValid⟩ := witness.semantic law
  have pcBound := Compiler.segment_compile_pc_bound allocator law bytes limits inst.module accepted code program
  have instanceShape := shape.instances inst (List.mem_of_getElem? found)
  have ready := segment_program_ready store inst code program pcBound instanceShape imports bindings valid.elements dataValid
  have compatible := segment_program_compatible store inst code program types valid.elements
  have globals : ∀ index address value, .GlobalGet 0#u32 index ∈ code.code.val →
      inst.globals.val[index.val]? = some address → store.globals.val[address.index.val]? = some value → value.ty.valtype = .I32 := by
    intro index address value member mapped issued
    obtain ⟨ty,declared,integer,imported⟩ := program.global_types valid.elements dataValid 0#u32 index member
    obtain ⟨actualAddress,actualValue,actualMapped,actualIssued,actualType⟩ := imports.globals index ty declared imported
    have sameAddress := Option.some.inj (actualMapped.symm.trans mapped)
    subst actualAddress
    have sameValue := Option.some.inj (actualIssued.symm.trans issued)
    subst actualValue
    rw [actualType]
    exact integer
  have checked := initialize_segments_source_causes memory hooks floats allocator view laws law store platform instIndex inst code
    found functionFound ready sourceCode (program.flow valid.elements dataValid) compatible globals
    shape sourceSyntax bounds ambient ambientWf moduleEq
  apply WP.spec_mono checked
  intro out outcome
  rcases outcome with ⟨reason,failed,same,cause⟩ | reduced
  · exact Or.inl ⟨reason,failed,same,code,functionFound,program,cause⟩
  · exact Or.inr (by simpa only [program.source valid.elements dataValid,segmentModuleSource] using reduced)

/-- Segment initialization composes with the source start-call continuation.
Setup exhaustion leaves the store unchanged; successful writes reach the exact
continuation, while any range trap absorbs it. -/
theorem initialize_segments_raw_source_causes {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex : Usize)
    (inst : runtime.store.ModuleInst) (bytes : Slice U8)
    (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes limits = .ok (.Ok inst.module))
    (found : store.instances.val[instIndex.val]? = some inst)
    (sourceCode : CodeInterpretation) (shape : Shape view store)
    (sourceSyntax : StoreSyntax sourceCode store) (bounds : SegmentBounds store)
    (imports : InitializerImports store inst) (bindings : InitializerBindings store inst)
    (types : SegmentTypeBindings store inst)
    (ambient : frame) (ambientWf : wf_frame ambient) (moduleEq : ambient.MODULE = decodeInstance store inst)
    (raw : Itasca.ModuleBinary.Module)
    (matched : Itasca.ModuleElaboration.Matches inst.module.module.env inst.module.module.tail raw)
    (after : List admininstr) (afterWf : Forall wf_admininstr after) :
    runtime.interp.initialize_segments memory hooks floats allocator store platform instIndex
      ⦃ out => (∃ reason, out.1 = .Err (.Exhausted reason) ∧ out.2.1 = store ∧
        SegmentSetupCause allocator store inst.module (.Exhausted reason)) ∨
        SegmentExecutionStatus out.1 ∧ StepsH ⟨⟨decodeStore view sourceCode store,ambient⟩,segmentRawSource raw ++ after⟩ []
          ⟨⟨decodeStore view sourceCode out.2.1,ambient⟩,segmentAfter out.1 after⟩ ⦄ := by
  obtain ⟨out,run,outcome⟩ := WP.spec_imp_exists (initialize_segments_compiled_source_causes
    memory hooks floats allocator view laws law store platform instIndex inst bytes limits
    accepted found sourceCode shape sourceSyntax bounds imports bindings types ambient ambientWf moduleEq)
  rw [run,WP.spec_ok]
  rcases outcome with exhausted | reduced
  · exact Or.inl exhausted
  · rcases reduced with ⟨status,reduced⟩
    refine Or.inr ⟨status,?_⟩
    have contextual := segment_steps_suffix _ _ _ out.1 after reduced afterWf
    simpa only [Spec.instrContext,vals,List.map_nil,List.nil_append,
      segment_module_source_raw inst.module raw matched] using contextual

end Itasca.Runtime.Store

end

end

/-! ## InitializerResourceCauses -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem eval_const_resource_causes (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex function : Usize)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType) (words : List U64)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hc : inst.module.functions.val[function.val]? = some code)
    (compiled : Compiler.InitializerCode code expr ty)
    (resolved : Interp.InitializerResolution store inst expr ty words)
    (referenceBound : ty = .FuncRef ∨ ty = .ExternRef → ((words[0]?).getD 0#u64).val ≤ Usize.max) :
    runtime.interp.eval_const memory hooks floats allocator store platform instIndex function ty
      ⦃ out => out.2.1 = store ∧ out.2.2 = platform ∧
        (∀ value, out.1 = .Ok value → Interp.rawType value = ty ∧
          Interp.sourceValue value = decodeWords ty ((words[0]?).getD 0#u64) ((words[1]?).getD 0#u64)) ∧
        (∀ error, out.1 = .Err error → Interp.SyntheticPreparationCause allocator store code error) ⦄ := by
  unfold runtime.interp.eval_const
  step with Interp.synthetic_resolved_initializer_resource_causes memory hooks floats allocator law store platform
    instIndex function inst code expr ty words hi hc compiled resolved
    as ⟨result, store', platform', hs, hp, success, errors⟩
  subst store' platform'
  cases result with
  | Err error =>
    simpa [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using errors error rfl
  | Ok pair =>
    have hpair := success pair rfl
    subst pair
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with Interp.decode_value_boundary ty ((words[0]?).getD 0#u64) ((words[1]?).getD 0#u64)
      store.id referenceBound as ⟨value, hty, hvalue⟩
    simp_all

end Itasca.Runtime.Store

end
