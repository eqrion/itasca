import Itasca.Runtime.Store.Initialization.BulkTable
import Itasca.Runtime.Spec.SegmentInitCases
import Itasca.Runtime.Spec.Context
import Itasca.Runtime.Store.Initialization.SegmentInstruction
import Itasca.Runtime.Store.Api.TableInit
import Itasca.Runtime.Store.Invariant.Syntax
import Itasca.Runtime.Store.Api.MemoryInit
import Itasca.Runtime.Store.Initialization.SegmentDrop
import Itasca.Runtime.Store.Initialization.SegmentCompatible
import Itasca.Runtime.Compiler.Local.Relations.Segments.SegmentTranslation
import Itasca.Runtime.Store.Initialization.SegmentStep
import Itasca.Runtime.Store.Initialization.SegmentLoopPreservation
import Itasca.Runtime.Store.Initialization.SegmentExtension

/-!
Source correspondence for the segment initialization loop. Pending operand encoding and per-instruction source reductions compose into the loop result, including the terminal return.
-/

/-! ## Segment Pending -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std SpecExt

def segmentValue (word : U64) : val := .CONST .I32 (.mk_num__0 .I32 (.mk_uN (bulkWord word).val))
def segmentPending (slots : List U64) (count : Nat) : List val := (slots.take count).map segmentValue

theorem segmentValue_wf (word : U64) : wf_val (segmentValue word) := by
  constructor
  exact .num__case_0 .I32 .I32 _ (by decide) (Spec.Segment.index_wf _ (by scalar_tac)) rfl

theorem segmentPending_wf (slots : List U64) (count : Nat) : Forall wf_val (segmentPending slots count) := by
  intro value member
  obtain ⟨word,_,rfl⟩ := List.mem_map.mp member
  exact segmentValue_wf word

theorem segmentPending_zero (slots : List U64) : segmentPending slots 0 = [] := rfl

theorem segmentPending_set (slots : List U64) (count : Nat) (bits : U32) (inside : count < slots.length) :
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

theorem segmentPending_three (slots : List U64) (a b c : U64)
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

end Itasca.Runtime.Store

namespace Itasca.Runtime.Store
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

end Itasca.Runtime.Store

end

/-! ## Segment Loop Source -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

private theorem flow_return {pending : Nat} {instruction : runtime.bytecode.Instr} {rest : List runtime.bytecode.Instr}
    (flow : Code.SegmentFlow pending (instruction :: rest)) (returns : segmentReturns instruction = true) :
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
    (flow : Code.SegmentFlow pending (code.code.val.drop position.val))
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
          pc.val < code.code.length ∧ Code.SegmentFlow n (code.code.val.drop pc.val) ∧
          StepsH origin [] ⟨⟨decodeStore view sourceCode state.1,ambient⟩,
            segmentAfter state.2.2.2 (vals (segmentPending state.2.2.1.slots.val n) ++ Code.segmentSource code (code.code.val.drop pc.val))⟩))
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
        change (rest = [] ∧ nextPending = 0 ∨ Code.SegmentFlow nextPending rest) at residual
        have nextObjects := objects.trans newObjects
        have nextTypes := types.trans newTypes
        have nextSlots := effect.slots.trans slots
        have nextHost := effect.platform
        dsimp only at nextObjects nextTypes nextSlots nextHost
        subst host
        have combined : StepsH origin [] ⟨⟨decodeStore view sourceCode after,ambient⟩,
            segmentAfter result (vals (segmentPending next.slots.val nextPending) ++ Code.segmentSource code rest)⟩ := by
          have previous : StepsH origin [] (segmentState view sourceCode current ambient code machine.slots.val n (instruction::rest)) := by
            simpa only [segmentState,segmentAfter,tail] using history
          exact Spec.stepsH_trans previous reduction
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
          · cases result <;> simpa [pendingZero,tailNil,segmentPending,vals,Code.segmentSource,segmentAfter,segmentResult] using combined
          · cases result <;> simp [segmentRemaining,nextFrames,currentFrames,initializerFrame]
        | false =>
          simp only [returns,Bool.false_eq_true,↓reduceIte] at nextFrames
          obtain ⟨nextPc,nextValue,nextFrames⟩ := nextFrames
          have nextBound : nextPc.val < code.code.length := by have := ready.next_bound fetched returns; omega
          have nextFlow : Code.SegmentFlow nextPending rest := by
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
    exact StepsH.refl (segmentState_wf view sourceCode store ambient code exec.slots.val pending _ shape sourceSyntax ambientWf)

end Itasca.Runtime.Store

end
