import Itasca.Runtime.Interp.Machine.SuspendedPoint
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdEmission
import Itasca.Runtime.SourceMachine.Simd.Source
import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission
import Itasca.Runtime.Compiler.Local.Control.Segments.Structured
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredComposition
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels
import Itasca.Runtime.Interp.Control.StructuredLinear
import Itasca.Runtime.SourceMachine.Measure
import Itasca.Runtime.Interp.Machine.Progress.SupportedAdvance
import Itasca.Runtime.SourceMachine.Simd.Step
import Itasca.Runtime.Interp.Simd.Execution.PureValuesExecute
import Itasca.Runtime.Interp.Simd.Relations.NumericResultSlots
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdSignature
import Itasca.Runtime.SourceMachine.Simd.MemoryTransition
import Itasca.Runtime.Interp.Simd.Execution.PureSound
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdSourceSignature
import Itasca.Runtime.Interp.Simd.Memory.ExecuteError
import Itasca.Runtime.Compiler.Local.Capacity.SimdMeaningBound
import Itasca.Runtime.Interp.Simd.Memory.ValuesExecute
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdMemoryValid
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdPureSignature
import Itasca.Runtime.Interp.Simd.Execution.ShuffleValuesExecute

/-!
Sections, each formerly its own module: Point, Continue, ExecutionJoin, ConstantFrame, FrameOutcome, Prepare, LaneFrame, MemoryFrame, PureFrame, ShuffleFrame, FrameStep.
-/

/-! ## Point -/

section

/-!
Inversion of a SIMD code point.

Main declarations: `simd_point_head`. A direct consumer is `Interp.Machine.Simd.Prepare`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas.Std

variable {jumpTables : List Aeneas.Std.U32}
theorem simd_point_head {emission : ContextEmission} {immediates constants C returns code labels stack pc next output}
    (source : instr) (after : List instr)
    (allowed : SourceMachine.SimdInstr source)
    (project : ∀ before emitted result, emission C before source emitted result →
      Compiler.SimdEmission immediates constants C before source emitted result)
    (point : Compiler.StructuredCode.Point (emission C) C.TYPES C.FUNCS returns C.LOCALS
      code jumpTables labels stack (source::after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Compiler.StructuredCode.Point (emission C) C.TYPES C.FUNCS returns C.LOCALS
        code jumpTables labels stack (source::after) target.val next output) ∨
    (∃ (instruction : Compiler.Bytecode) (result : List valtype),
      Compiler.SimdEmission immediates constants C stack source [instruction] result ∧
      code[pc]? = some instruction ∧
      Compiler.StructuredCode.Point (emission C) C.TYPES C.FUNCS returns C.LOCALS
        code jumpTables labels result after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : source::after = cursor at relation
  cases relation with
  | linear head ordinary fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    have projected := project _ _ _ head
    have length := projected.length_one
    cases projected with
    | instruction front input output source opcode operand entry immediate instruction meaning metadata made position =>
      have fetch := fragment.fetch (index := 0) (by rfl)
      obtain ⟨_,_,_,_,nextEq⟩ := fragment
      refine Or.inr ⟨instruction,front++output,.instruction front input output _ opcode operand entry immediate
        instruction meaning metadata made position,by simpa using fetch,?_⟩
      exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
    | constant front bits dst entry metadata position =>
      have fetch := fragment.fetch (index := 0) (by rfl)
      obtain ⟨_,_,_,_,nextEq⟩ := fragment
      refine Or.inr ⟨.ConstV128 dst entry,stack++[.V128],.constant stack bits dst entry metadata position,
        by simpa using fetch,?_⟩
      exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
  | skip forward instruction rest =>
    subst_vars
    exact Or.inl ⟨_,forward,instruction,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | _ =>
    cases allowed with
    | pure signature => cases signature <;> simp at sourceEq
    | constant => simp at sourceEq
    | memory signature => cases signature <;> simp at sourceEq
end Itasca.Runtime.Interp.Machine

end

/-! ## Continue -/

section

/-!
Reuse the retained SIMD continuation after the exact operand suffix has been replaced. The store may change only through a checked source extension.

Main declarations: `frame_point_continue`. A direct consumer is `Interp.Machine.Simd.ConstantFrame`.
-/

namespace Itasca.Runtime.Interp.Machine.Simd
open Aeneas.Std

/-- Reuse the retained SIMD continuation after the exact operand suffix has
been replaced. The store may change only through a checked source extension. -/
theorem frame_point_continue
    {before afterStore raw f compiled C targets next output}
    (point : FramePoint before raw f compiled C targets next output)
    (extension : Extend_store before afterStore)
    (front operands results : List val) (after : List instr)
    (values : f.vals = front ++ operands)
    (heights : ∀ label ∈ f.labels, label.height ≤ front.length)
    (tail : Compiler.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val compiled.jump_tables.val targets (front.map Compiler.valueType ++ results.map Compiler.valueType)
      after (raw.pc.val+1) next output)
    (pc : U32) (pcNext : pc.val = raw.pc.val+1) :
    FramePoint afterStore {raw with pc := pc} {f with code := after,vals := front ++ results}
      compiled C targets next output := by
  refine ⟨point.bindings.extend extension,point.locals,?_,?_⟩
  · have labels := point.labels
    rw [values] at labels
    exact labels.replace_suffix heights
  · simpa only [List.map_append,pcNext] using tail

end Itasca.Runtime.Interp.Machine.Simd

end

/-! ## ExecutionJoin -/

section

/-!
Actual SIMD frame effects preserve the complete stack of compiled callers. Source typing, supported syntax, ownership, and source bounds follow from the checked source SIMD step rather than additional runtime postulates.

Main declarations: `Execution.simd`. A direct consumer is `Interp.Machine.Simd.ConstantFrame`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas.Std

/-- Actual SIMD frame effects preserve the complete stack of compiled callers.
Source typing, supported syntax, ownership, and source bounds follow from the
checked source SIMD step rather than additional runtime postulates. -/
theorem Execution.simd {M : Type}
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    {store nextStore : runtime.store.Store M} {exec after : runtime.interp.Execution}
    (ambient : frame) (source updated : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (expected : List valtype) (beforePC : Nat) (beforePending : Bool)
    (machine : Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,source::rest,[]⟩ expected beforePC beforePending)
    (stores : FrameStoreMetadata store nextStore)
    (raw : runtime.interp.Frame) (index : Usize) (pc : U32)
    (last : index.val+1 = exec.frames.length) (lookup : exec.frames.val[index.val]? = some raw)
    {compiled C targets next output}
    (program : FrameProgram store raw compiled (source.locals.map Compiler.valueType) source.resultTypes C.FUNCS)
    (point : FramePoint (Store.decodeStore view code nextStore) {raw with pc := pc}
      updated compiled C targets next output)
    (slots : FrameSlots after {raw with pc := pc} updated)
    (metadata : FrameMetadata source updated)
    (effect : {after with slots := exec.slots} = {exec with frames := exec.frames.set index {raw with pc := pc}})
    (preserved : SlotPrefix raw.base.val exec.slots.val after.slots.val)
    (step : SourceMachine.Simd.Step ⟨Store.decodeStore view code store,ambient,source::rest,[]⟩
      (.next ⟨Store.decodeStore view code nextStore,ambient,updated::rest,[]⟩)) :
    Execution view code nextStore after
      ⟨Store.decodeStore view code nextStore,ambient,updated::rest,[]⟩ expected pc.val false ∧
    ConcreteSim compiled.code.length beforePC pc.val beforePending false
      ⟨Store.decodeStore view code store,ambient,source::rest,[]⟩
      ⟨Store.decodeStore view code nextStore,ambient,updated::rest,[]⟩ ∧
    (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds ⟨Store.decodeStore view code store,ambient,source::rest,[]⟩ →
      SourceMachine.Ownership.StatefulOwned bounds ⟨Store.decodeStore view code nextStore,ambient,updated::rest,[]⟩) ∧
    (∀ bound, SourceMachine.CodeBound bound ⟨Store.decodeStore view code store,ambient,source::rest,[]⟩ →
      SourceMachine.CodeBound bound ⟨Store.decodeStore view code nextStore,ambient,updated::rest,[]⟩) := by
  refine ⟨?_,ConcreteSim.of_source _ _ _ _ _ (step.next_simulation machine.typed),
    fun _ owned => step.next_owned owned,fun _ bounded => step.next_bound bounded⟩
  exact machine.ordinary view code ambient source updated rest expected beforePC beforePending stores
    (step.next_extension machine.typed) raw index pc last lookup program (.ready point) slots metadata effect preserved
    (step.next_typed machine.typed) (step.next_supported machine.core)

end Itasca.Runtime.Interp.Machine

end

/-! ## ConstantFrame -/

section

/-!
SIMD constant execution at a structured frame point.

Main declarations: `step_constant_frame`. A direct consumer is `Interp.Machine.Simd.FrameStep`.
-/

namespace Itasca.Runtime.Interp.Machine.Simd
open Aeneas Aeneas.Std Itasca.ResultFacts

private theorem constant_bounds (compiled : runtime.bytecode.CompiledFunction) (dst entry : U32)
    (valid : runtime.bytecode.CompiledFunction.instruction_valid compiled (.ConstV128 dst entry)=.ok true) :
    dst.val+2≤compiled.slot_count.val := by
  simp only [runtime.bytecode.CompiledFunction.instruction_valid,runtime.bytecode.CompiledFunction.other_valid,runtime.bytecode.Instr.scalar,
    runtime.bytecode.Instr.load,runtime.bytecode.Instr.store,runtime.bytecode.Instr.simd,bind_ok] at valid
  obtain ⟨fits,run,valid⟩ := bind_ok_inv _ _ _ valid
  cases fits with
  | false => simp at valid
  | true => exact Compiler.slots_fit_true compiled dst 2#u32 run

theorem step_constant_frame {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (interpretation : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (raw : runtime.interp.Frame) (index : Usize) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Compiler.LabelTarget)
    (next : Nat) (output : List valtype) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (bits : U128) (dst entry : U32)
    (last : index.val+1=exec.frames.length) (hf : exec.frames.val[index.val]?=some raw)
    (hi : store.instances.val[raw.instance.val]?=some inst)
    (hc : inst.module.functions.val[raw.function.val]?=some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS)
    (allocated : raw.base.val+compiled.slot_count.val≤exec.slots.length)
    (typed : SourceMachine.CoreTyped ⟨Store.decodeStore view interpretation store,ambient,
      {f with code:=.VCONST .V128 (.mk_uN bits.val)::after}::rest,[]⟩)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view interpretation store) raw
      {f with code:=.VCONST .V128 (.mk_uN bits.val)::after} compiled C targets next output)
    (immediate : compiled.v128_pool.val[entry.val]?=some bits)
    (position : dst.val=Compiler.slots C.LOCALS+Compiler.slots (f.vals.map Compiler.valueType))
    (fetch : compiled.code.val[raw.pc.val]?=some (.ConstV128 dst entry))
    (tail : Compiler.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val compiled.jump_tables.val targets (f.vals.map Compiler.valueType++[.V128]) after (raw.pc.val+1) next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1=.Ok () ∧ out.2.2.2=platform ∧ SimdStoreMutation view store out.2.2.1 ∧
      FrameStoreMetadata store out.2.2.1 ∧ ∃ pc : U32, ∃ updated : SourceMachine.AFrame,
      pc.val=raw.pc.val+1 ∧
      {out.2.1 with slots:=exec.slots}={exec with frames:=exec.frames.set index {raw with pc:=pc}} ∧
      SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ∧
      FrameSlots out.2.1 {raw with pc:=pc} updated ∧
      FrameMetadata {f with code:=.VCONST .V128 (.mk_uN bits.val)::after} updated ∧
      FramePoint (Store.decodeStore view interpretation out.2.2.1) {raw with pc:=pc}
        updated compiled C targets next output ∧
      SourceMachine.Simd.Step ⟨Store.decodeStore view interpretation store,ambient,{f with code:=.VCONST .V128 (.mk_uN bits.val)::after}::rest,[]⟩
        (.next ⟨Store.decodeStore view interpretation out.2.2.1,ambient,updated::rest,[]⟩) ⦄ := by
  have bounds := constant_bounds compiled dst entry (Compiler.well_formed_fetched compiled program.checked _ _ fetch)
  have capacity : raw.base.val+dst.val+2≤exec.slots.length := by omega
  have frameTyped : SourceMachine.FrameTyped (Store.decodeStore view interpretation store)
      {f with code:=.VCONST .V128 (.mk_uN bits.val)::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  have position' : dst.val=Compiler.slots ((f.locals++f.vals).map Compiler.valueType) := by
    simpa only [List.map_append,Compiler.slots_append,point.locals] using position
  apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled (.ConstV128 dst entry)
    last hf hi hc fetch (program.fetched_bound _ fetch)
  intro pc pcNext
  apply WP.spec_mono (dispatch_const_v128_values memory hooks floats allocator
    {exec with frames:=exec.frames.set index {raw with pc:=pc}} store platform index raw.instance raw.function raw.base
    dst entry inst compiled bits (f.locals++f.vals) hi hc immediate position' slots capacity)
  rintro out ⟨ok,same,platformEq,effect,resultSlots⟩
  rw [same]
  let updated : SourceMachine.AFrame := {f with code:=after,vals:=f.vals++[.VCONST .V128 (.mk_uN bits.val)]}
  refine ⟨ok,platformEq,Or.inl rfl,.refl store,pc,updated,pcNext,effect.2,?_,?_,⟨rfl,rfl,rfl,rfl⟩,?_,.constant⟩
  · rw [effect.1]
    exact .simd_result raw.base.val exec.slots.val (raw.base.val+dst.val) 2#u32 bits (by omega)
  · simpa only [FrameSlots,updated,List.append_assoc] using resultSlots
  · dsimp only [updated]
    refine ⟨point.bindings,point.locals,?_,?_⟩
    · have labels : LabelsMatch (f.vals++[]) f.labels targets := by simpa only [List.append_nil] using point.labels
      exact labels.replace_suffix (show ∀ label ∈ f.labels, label.height ≤ f.vals.length from SourceMachine.frame_typed_heights (f := {f with code:=.VCONST .V128 (.mk_uN bits.val)::after}) frameTyped)
    · simpa only [List.map_append,List.map_cons,List.map_nil,Compiler.valueType,pcNext] using tail

end Itasca.Runtime.Interp.Machine.Simd

end

/-! ## FrameOutcome -/

section

/-!
The postcondition of a SIMD frame step.

Main declarations: `FrameOutcome`. A direct consumer is `Interp.Machine.Simd.FrameStep`.
-/

namespace Itasca.Runtime.Interp.Machine.Simd
open Aeneas.Std

def FrameOutcome {M P : Type} (view : M → Slice U8)
    (interpretation : Store.CodeInterpretation) (store : runtime.store.Store M)
    (exec : runtime.interp.Execution) (platform : P) (raw : runtime.interp.Frame) (index : Usize)
    (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Compiler.LabelTarget)
    (next : Nat) (output : List valtype) (ambient : frame) (source : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P) : Prop :=
  out.2.2.2=platform ∧ SimdStoreMutation view store out.2.2.1 ∧ FrameStoreMetadata store out.2.2.1 ∧
  ∃ pc : U32, pc.val=raw.pc.val+1 ∧
  ((out.1=.Ok () ∧ ∃ updated : SourceMachine.AFrame,
    {out.2.1 with slots:=exec.slots}={exec with frames:=exec.frames.set index {raw with pc:=pc}} ∧
    SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ∧
    FrameSlots out.2.1 {raw with pc:=pc} updated ∧ FrameMetadata source updated ∧
    FramePoint (Store.decodeStore view interpretation out.2.2.1) {raw with pc:=pc} updated compiled C targets next output ∧
    SourceMachine.Simd.Step ⟨Store.decodeStore view interpretation store,ambient,source::rest,[]⟩
      (.next ⟨Store.decodeStore view interpretation out.2.2.1,ambient,updated::rest,[]⟩)) ∨
  (out.1=.Err (.Trap .MemoryOutOfBounds) ∧
    out.2.1={exec with frames:=exec.frames.set index {raw with pc:=pc}} ∧
    Store.decodeStore view interpretation out.2.2.1=Store.decodeStore view interpretation store ∧
    SourceMachine.Simd.Step ⟨Store.decodeStore view interpretation store,ambient,source::rest,[]⟩ .trap))

end Itasca.Runtime.Interp.Machine.Simd

end

/-! ## Prepare -/

section

/-!
Source operands and head preparation for a SIMD frame instruction.

Main declarations: `instruction_operands` and `frame_point_head`. A direct consumer is `Interp.Machine.Simd.LaneFrame`.
-/

namespace Itasca.Runtime.Interp.Machine.Simd
open Aeneas.Std SpecExt Itasca.Runtime.Spec

theorem instruction_operands {s : store} {f : SourceMachine.AFrame} {after : List instr}
    {C opcode immediate input source output frontTypes}
    (meaning : Compiler.SimdImmediateMeaning C opcode immediate input source output)
    (typed : SourceMachine.FrameTyped s {f with code := source :: after} [])
    (stack : f.vals.map Compiler.valueType = frontTypes ++ input) :
    ∃ front operands, f.vals = front ++ operands ∧ front.map Compiler.valueType = frontTypes ∧
      operands.map Compiler.valueType = input ∧ Forall wf_val operands ∧
      (∀ label ∈ f.labels, label.height ≤ front.length) := by
  obtain ⟨front,operands,values,frontTypesEq,operandTypes⟩ := List.map_eq_append_iff.mp stack
  obtain ⟨D,actualFront,actualOperands,ins,outs,_,_,operation,split,actualTypes,_,heights⟩ :=
    SourceMachine.frame_typed_operands_bounds typed
  obtain ⟨rfl,rfl⟩ := meaning.principal operation
  have actualLength := results_typed_length actualTypes
  have operandLength := congrArg List.length operandTypes
  have frontLength := congrArg List.length (values.symm.trans split)
  simp only [List.length_append,List.length_map] at operandLength frontLength
  have equal : actualFront.length = front.length := by omega
  have valid := (SourceMachine.frame_typed_wf typed).2.2.1
  change Forall wf_val f.vals at valid
  refine ⟨front,operands,values,frontTypesEq,operandTypes,?_,?_⟩
  · intro value member
    apply valid value
    rw [values]
    exact List.mem_append_right _ member
  · simpa only [equal] using heights

theorem frame_point_head
    {s : store} {raw : runtime.interp.Frame} {f : SourceMachine.AFrame}
    {compiled : runtime.bytecode.CompiledFunction} {C : context} {targets : List Compiler.LabelTarget}
    {next : Nat} {output : List valtype} (source : instr) (after : List instr)
    (allowed : SourceMachine.SimdInstr source)
    (project : ∀ before emitted result, emission compiled C before source emitted result →
      Compiler.SimdEmission compiled.simd.val compiled.v128_pool.val C before source emitted result)
    (point : FramePoint s raw {f with code := source :: after} compiled C targets next output) :
    (∃ target : U32, raw.pc.val < target.val ∧ compiled.code.val[raw.pc.val]? = some (.Jump target) ∧
      FramePoint s {raw with pc := target} {f with code := source :: after} compiled C targets next output) ∨
    (∃ instruction result,
      Compiler.SimdEmission compiled.simd.val compiled.v128_pool.val C (f.vals.map Compiler.valueType) source [instruction] result ∧
      compiled.code.val[raw.pc.val]? = some instruction ∧
      Compiler.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
        compiled.code.val compiled.jump_tables.val targets result after (raw.pc.val+1) next output) := by
  rcases simd_point_head source after allowed project point.code with jump | head
  · obtain ⟨target,forward,fetch,tail⟩ := jump
    exact Or.inl ⟨target,forward,fetch,⟨point.bindings,point.locals,point.labels,tail⟩⟩
  · exact Or.inr head

end Itasca.Runtime.Interp.Machine.Simd

end

/-! ## LaneFrame -/

section

/-!
SIMD lane-operation execution at a structured frame point.

Main declarations: `step_lane_frame`. A direct consumer is `Interp.Machine.Simd.FrameStep`.
-/

namespace Itasca.Runtime.Interp.Machine.Simd
open Aeneas Aeneas.Std Itasca.Wasm2.Simd
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem step_lane_frame {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (interpretation : Store.CodeInterpretation)
    (memoryLaws : Platform.MemoryLaws memory view)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (raw : runtime.interp.Frame) (index : Usize) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Compiler.LabelTarget)
    (next : Nat) (output : List valtype) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (frontTypes : List valtype) (op : LaneOperation) (lane : U8)
    (opcode operand entry : U32) (imm : runtime.bytecode.SimdImmediate) (instruction : Compiler.Bytecode)
    (last : index.val+1=exec.frames.length) (hf : exec.frames.val[index.val]?=some raw)
    (hi : store.instances.val[raw.instance.val]?=some inst)
    (hc : inst.module.functions.val[raw.function.val]?=some compiled)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS)
    (allocated : raw.base.val+compiled.slot_count.val≤exec.slots.length)
    (typed : SourceMachine.CoreTyped ⟨Store.decodeStore view interpretation store,ambient,
      {f with code:=(op.instruction (.mk_uN lane.val))::after}::rest,[]⟩)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view interpretation store) raw
      {f with code:=(op.instruction (.mk_uN lane.val))::after} compiled C targets next output)
    (stack : f.vals.map Compiler.valueType=frontTypes++op.inputs)
    (meaning : laneMeaning opcode.val=some op)
    (lanePosition : imm.lane.val=lane.val)
    (immediate : compiled.simd.val[entry.val]?=some imm)
    (made : runtime.bytecode.Instr.make_simd opcode operand operand entry=.ok (some instruction))
    (position : operand.val=Compiler.slots C.LOCALS+Compiler.slots frontTypes)
    (fetch : compiled.code.val[raw.pc.val]?=some instruction)
    (tail : Compiler.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val compiled.jump_tables.val targets (frontTypes++op.outputs) after (raw.pc.val+1) next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1=.Ok () ∧ out.2.2.2=platform ∧ SimdStoreMutation view store out.2.2.1 ∧
      FrameStoreMetadata store out.2.2.1 ∧ ∃ pc : U32, ∃ updated : SourceMachine.AFrame,
      pc.val=raw.pc.val+1 ∧
      {out.2.1 with slots:=exec.slots}={exec with frames:=exec.frames.set index {raw with pc:=pc}} ∧
      SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ∧
      FrameSlots out.2.1 {raw with pc:=pc} updated ∧
      FrameMetadata {f with code:=(op.instruction (.mk_uN lane.val))::after} updated ∧
      FramePoint (Store.decodeStore view interpretation out.2.2.1) {raw with pc:=pc}
        updated compiled C targets next output ∧
      SourceMachine.Simd.Step ⟨Store.decodeStore view interpretation store,ambient,{f with code:=(op.instruction (.mk_uN lane.val))::after}::rest,[]⟩
        (.next ⟨Store.decodeStore view interpretation out.2.2.1,ambient,updated::rest,[]⟩) ⦄ := by
  have sig := Compiler.lane_source_signature op (.mk_uN lane.val)
  have immediateMeaning := Compiler.SimdImmediateMeaning.lane (C:=C) opcode imm op meaning lane lanePosition
  have frameTyped : SourceMachine.FrameTyped (Store.decodeStore view interpretation store) {f with code:=(op.instruction (.mk_uN lane.val))::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨front,values,split,frontEq,types,wf,heights⟩ := instruction_operands immediateMeaning frameTyped stack
  have simdView := Compiler.make_simd_roundtrip_bounded opcode operand operand entry instruction
    immediateMeaning.opcode_bound made
  obtain ⟨space,lastSpace,capacity⟩ := program.simd_capacity exec.slots.slice allocated instruction opcode operand entry
    _ _ _ _ fetch simdView immediateMeaning.shape
  obtain ⟨D,actualFront,actualValues,ins,outs,_,_,operation,_⟩ := SourceMachine.frame_typed_operands_bounds frameTyped
  have laneValid : imm.lane.val < op.count := by
    rw [lanePosition]
    exact op.bound (SourceMachine.labelContext D f.labels) (.mk_uN lane.val) ins outs operation
  have memories := module_memories_issued view interpretation store inst C (moduleEq ▸ point.bindings)
  have represented : ValuesAt exec.slots.val raw.base.val ((f.locals++front)++values) := by
    simpa only [FrameSlots,split,List.append_assoc] using slots
  have position' : operand.val=Compiler.slots ((f.locals++front).map Compiler.valueType) := by
    simpa only [List.map_append,Compiler.slots_append,point.locals,frontEq] using position
  apply step_simd_of_view memory hooks floats allocator exec store platform index raw inst compiled instruction
    opcode operand operand entry last hf hi hc fetch (program.fetched_bound _ fetch) simdView
  intro pc pcNext
  apply WP.spec_mono (execute_simd_lane_values memory floats interpretation view memoryLaws
    {exec with frames:=exec.frames.set index {raw with pc:=pc}} store raw.instance raw.function raw.base
    opcode operand entry inst compiled imm op (f.locals++front) values hi hc immediate meaning laneValid memories
    position' represented wf types space lastSpace capacity)
  rintro out ⟨mutation,value,source,ok,decoded,metadata,effect,resultSlots⟩
  rw [lanePosition] at source
  let updated : SourceMachine.AFrame := {f with code:=after,vals:=front++[Interp.Simd.laneResult op value.bv]}
  have resultType : SourceMachine.valueType (Interp.Simd.laneResult op value.bv)=Compiler.simdLaneOutput op := by
    cases op <;> rfl
  have step : SourceMachine.Simd.Step ⟨Store.decodeStore view interpretation store,ambient,{f with code:=(op.instruction (.mk_uN lane.val))::after}::rest,[]⟩
      (.next ⟨Store.decodeStore view interpretation out.2.2,ambient,updated::rest,[]⟩) := by
    rw [decoded]
    apply SourceMachine.Simd.Step.pure sig
    exact .next front values _ split
      (by simpa only [show Compiler.valueType=SourceMachine.valueType from funext value_type_eq_abs] using types) ⟨source,resultType⟩
  refine ⟨ok,rfl,mutation,metadata,pc,updated,pcNext,effect.2,?_,?_,?_,?_,step⟩
  · rw [effect.1]
    exact .simd_result raw.base.val exec.slots.val (raw.base.val+operand.val) _ value (by omega)
  · simpa only [FrameSlots,updated,List.append_assoc] using resultSlots
  · exact ⟨rfl,rfl,rfl,rfl⟩
  · apply frame_point_continue point (step.next_extension typed) front values [_] after split heights _ pc pcNext
    have outputEq : [Compiler.valueType (Interp.Simd.laneResult op value.bv)]=op.outputs := by
      cases op <;> rfl
    simpa only [List.map_cons,List.map_nil,outputEq,frontEq] using tail

end Itasca.Runtime.Interp.Machine.Simd

end

/-! ## MemoryFrame -/

section

/-!
SIMD memory-operation execution at a structured frame point.

Main declarations: `step_memory_frame`. A direct consumer is `Interp.Machine.Simd.FrameStep`.
-/

namespace Itasca.Runtime.Interp.Machine.Simd
open Aeneas Aeneas.Std Itasca.Wasm2.Simd
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem step_memory_frame {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (interpretation : Store.CodeInterpretation)
    (memoryLaws : Platform.MemoryLaws memory view)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (raw : runtime.interp.Frame) (index : Usize) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Compiler.LabelTarget)
    (next : Nat) (output : List valtype) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (frontTypes : List valtype) (op : MemoryOperation) (argument : memarg) (lane : U8)
    (opcode operand entry : U32) (imm : runtime.bytecode.SimdImmediate) (instruction : Compiler.Bytecode)
    (last : index.val+1=exec.frames.length) (hf : exec.frames.val[index.val]?=some raw)
    (hi : store.instances.val[raw.instance.val]?=some inst)
    (hc : inst.module.functions.val[raw.function.val]?=some compiled)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS)
    (allocated : raw.base.val+compiled.slot_count.val≤exec.slots.length)
    (typed : SourceMachine.CoreTyped ⟨Store.decodeStore view interpretation store,ambient,
      {f with code:=(op.instruction argument (.mk_uN lane.val))::after}::rest,[]⟩)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view interpretation store) raw
      {f with code:=(op.instruction argument (.mk_uN lane.val))::after} compiled C targets next output)
    (stack : f.vals.map Compiler.valueType=frontTypes++op.inputs)
    (meaning : memoryMeaning opcode.val=some op)
    (memoryType : memtype) (available : C.MEMS[0]?=some memoryType)
    (offset : argument.OFFSET=.mk_uN imm.offset.val)
    (lanePosition : op.laneCount ≠ 0 → imm.lane.val=lane.val)
    (immediate : compiled.simd.val[entry.val]?=some imm)
    (made : runtime.bytecode.Instr.make_simd opcode operand operand entry=.ok (some instruction))
    (position : operand.val=Compiler.slots C.LOCALS+Compiler.slots frontTypes)
    (fetch : compiled.code.val[raw.pc.val]?=some instruction)
    (tail : Compiler.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val compiled.jump_tables.val targets (frontTypes++op.outputs) after (raw.pc.val+1) next output) :
    let initial : SourceMachine.AState := ⟨Store.decodeStore view interpretation store,ambient,
      {f with code:=op.instruction argument (.mk_uN lane.val)::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.2=platform ∧ SimdStoreMutation view store out.2.2.1 ∧
      FrameStoreMetadata store out.2.2.1 ∧ ∃ pc : U32, pc.val=raw.pc.val+1 ∧
      ((out.1=.Ok () ∧ ∃ updated : SourceMachine.AFrame,
        {out.2.1 with slots:=exec.slots}={exec with frames:=exec.frames.set index {raw with pc:=pc}} ∧
        SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ∧
        FrameSlots out.2.1 {raw with pc:=pc} updated ∧
        FrameMetadata {f with code:=op.instruction argument (.mk_uN lane.val)::after} updated ∧
        FramePoint (Store.decodeStore view interpretation out.2.2.1) {raw with pc:=pc}
          updated compiled C targets next output ∧
        SourceMachine.Simd.Step initial (.next ⟨Store.decodeStore view interpretation out.2.2.1,ambient,updated::rest,[]⟩)) ∨
      (out.1=.Err (.Trap .MemoryOutOfBounds) ∧
        out.2.1={exec with frames:=exec.frames.set index {raw with pc:=pc}} ∧
        Store.decodeStore view interpretation out.2.2.1=Store.decodeStore view interpretation store ∧
        SourceMachine.Simd.Step initial .trap)) ⦄ := by
  dsimp only
  have sig := Compiler.memory_source_signature op argument (.mk_uN lane.val)
  have immediateMeaning := Compiler.SimdImmediateMeaning.memory (C:=C) opcode imm op meaning argument lane
    memoryType available offset lanePosition
  have frameTyped : SourceMachine.FrameTyped (Store.decodeStore view interpretation store)
      {f with code:=op.instruction argument (.mk_uN lane.val)::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨front,values,split,frontEq,types,wf,heights⟩ := instruction_operands immediateMeaning frameTyped stack
  have simdView := Compiler.make_simd_roundtrip_bounded opcode operand operand entry instruction
    immediateMeaning.opcode_bound made
  obtain ⟨space,lastSpace,capacity⟩ := program.simd_capacity exec.slots.slice allocated instruction opcode operand entry
    _ _ _ _ fetch simdView immediateMeaning.shape
  obtain ⟨D,actualFront,actualValues,ins,outs,_,_,operation,_⟩ := SourceMachine.frame_typed_operands_bounds frameTyped
  have laneValid : op.laneCount ≠ 0 → imm.lane.val < op.laneCount := by
    intro nonzero
    rw [lanePosition nonzero]
    exact Compiler.simd_memory_lane_valid op (SourceMachine.labelContext D f.labels) argument (.mk_uN lane.val) ins outs operation nonzero
  have sourceEq : op.instruction argument (.mk_uN imm.lane.val)=op.instruction argument (.mk_uN lane.val) := by
    by_cases nonzero : op.laneCount ≠ 0
    · rw [lanePosition nonzero]
    · cases op <;> first | rfl | simp [MemoryOperation.laneCount] at nonzero
  obtain ⟨ma,object,mapped,issued⟩ := Stateful.memory_binding_raw view interpretation store inst C memoryType
    (moduleEq ▸ point.bindings) available
  have represented : ValuesAt exec.slots.val raw.base.val ((f.locals++front)++values) := by
    simpa only [FrameSlots,split,List.append_assoc] using slots
  have position' : operand.val=Compiler.slots ((f.locals++front).map Compiler.valueType) := by
    simpa only [List.map_append,Compiler.slots_append,point.locals,frontEq] using position
  have frameWf := (SourceMachine.frame_typed_wf frameTyped).1
  have operationWf : wf_admininstr (admininstr_instr (op.instruction argument (.mk_uN imm.lane.val))) := by
    rw [sourceEq]
    exact Spec.wf_admininstr_instr ((SourceMachine.frame_typed_wf frameTyped).2.2.2 _ (by simp))
  apply step_simd_of_view memory hooks floats allocator exec store platform index raw inst compiled instruction
    opcode operand operand entry last hf hi hc fetch (program.fetched_bound _ fetch) simdView
  intro pc pcNext
  apply WP.spec_mono (execute_simd_memory_values memory floats interpretation view memoryLaws
    {exec with frames:=exec.frames.set index {raw with pc:=pc}} store raw.instance raw.function raw.base
    opcode operand entry inst compiled imm op (f.locals++front) values hi hc immediate meaning ma object mapped issued
    position' represented wf types space lastSpace capacity f.toFrame argument moduleEq typed.typed.store frameWf
    operationWf (by rw [offset]; rfl) laneValid)
  rintro out ⟨mutation,effect⟩
  refine ⟨rfl,Or.inr ⟨ma,object,issued,mutation⟩,mutation.frame_metadata,pc,pcNext,?_⟩
  cases status : out.1 with
  | Ok unit =>
    cases unit
    rw [status] at effect
    obtain ⟨value,slotsEffect,resultSlots,source,change⟩ := effect
    rw [sourceEq] at source
    let results := Spec.Simd.operandValues op.outputs value.bv 0 0
    let updated : SourceMachine.AFrame := {f with code:=after,vals:=front++results}
    have step : SourceMachine.Simd.Step ⟨Store.decodeStore view interpretation store,ambient,
        {f with code:=op.instruction argument (.mk_uN lane.val)::after}::rest,[]⟩
        (.next ⟨Store.decodeStore view interpretation out.2.2,ambient,updated::rest,[]⟩) := by
      apply SourceMachine.Simd.Step.memory sig
      exact Interp.Simd.memory_values_transition _ _ _ after op argument lane.val front values value _ split types change source
    refine Or.inl ⟨rfl,updated,slotsEffect.2,?_,?_,⟨rfl,rfl,rfl,rfl⟩,?_,step⟩
    · rw [slotsEffect.1]
      exact .simd_result raw.base.val exec.slots.val (raw.base.val+operand.val) _ value (by omega)
    · simpa only [FrameSlots,updated,List.append_assoc] using resultSlots
    · apply frame_point_continue point (step.next_extension typed) front values results after split heights _ pc pcNext
      have resultTypes : results.map Compiler.valueType=op.outputs := by
        simpa only [show Compiler.valueType=SourceMachine.valueType from funext value_type_eq_abs] using Interp.Simd.memory_result_types op value.bv
      simpa only [resultTypes,frontEq] using tail
  | Err error =>
    rw [status] at effect
    obtain ⟨rfl,same,decoded,source⟩ := effect
    rw [sourceEq] at source
    refine Or.inr ⟨rfl,same,decoded,?_⟩
    apply SourceMachine.Simd.Step.memory sig
    exact Interp.Simd.memory_values_trap _ _ _ after op argument lane.val front values split types source

end Itasca.Runtime.Interp.Machine.Simd

end

/-! ## PureFrame -/

section

/-!
Pure SIMD operation execution at a structured frame point.

Main declarations: `step_pure_frame`. A direct consumer is `Interp.Machine.Simd.FrameStep`.
-/

namespace Itasca.Runtime.Interp.Machine.Simd
open Aeneas Aeneas.Std Itasca.Wasm2.Simd
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem step_pure_frame {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (interpretation : Store.CodeInterpretation)
    (memoryLaws : Platform.MemoryLaws memory view) (floatLaws : Platform.FloatOpsCorrect floats)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (raw : runtime.interp.Frame) (index : Usize) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Compiler.LabelTarget)
    (next : Nat) (output : List valtype) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (frontTypes : List valtype) (op : Operation)
    (opcode operand entry : U32) (imm : runtime.bytecode.SimdImmediate) (instruction : Compiler.Bytecode)
    (last : index.val+1=exec.frames.length) (hf : exec.frames.val[index.val]?=some raw)
    (hi : store.instances.val[raw.instance.val]?=some inst)
    (hc : inst.module.functions.val[raw.function.val]?=some compiled)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS)
    (allocated : raw.base.val+compiled.slot_count.val≤exec.slots.length)
    (typed : SourceMachine.CoreTyped ⟨Store.decodeStore view interpretation store,ambient,
      {f with code:=op.instruction::after}::rest,[]⟩)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view interpretation store) raw
      {f with code:=op.instruction::after} compiled C targets next output)
    (stack : f.vals.map Compiler.valueType=frontTypes++op.signature.inputs)
    (meaning : pureMeaning opcode.val=some op)
    (immediate : compiled.simd.val[entry.val]?=some imm)
    (made : runtime.bytecode.Instr.make_simd opcode operand operand entry=.ok (some instruction))
    (position : operand.val=Compiler.slots C.LOCALS+Compiler.slots frontTypes)
    (fetch : compiled.code.val[raw.pc.val]?=some instruction)
    (tail : Compiler.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val compiled.jump_tables.val targets (frontTypes++op.signature.outputs) after (raw.pc.val+1) next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1=.Ok () ∧ out.2.2.2=platform ∧ SimdStoreMutation view store out.2.2.1 ∧
      FrameStoreMetadata store out.2.2.1 ∧ ∃ pc : U32, ∃ updated : SourceMachine.AFrame,
      pc.val=raw.pc.val+1 ∧
      {out.2.1 with slots:=exec.slots}={exec with frames:=exec.frames.set index {raw with pc:=pc}} ∧
      SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ∧
      FrameSlots out.2.1 {raw with pc:=pc} updated ∧
      FrameMetadata {f with code:=op.instruction::after} updated ∧
      FramePoint (Store.decodeStore view interpretation out.2.2.1) {raw with pc:=pc}
        updated compiled C targets next output ∧
      SourceMachine.Simd.Step ⟨Store.decodeStore view interpretation store,ambient,{f with code:=op.instruction::after}::rest,[]⟩
        (.next ⟨Store.decodeStore view interpretation out.2.2.1,ambient,updated::rest,[]⟩) ⦄ := by
  have sig := Compiler.pure_source_signature meaning
  have immediateMeaning := Compiler.SimdImmediateMeaning.pure (C:=C) opcode imm op meaning
  have frameTyped : SourceMachine.FrameTyped (Store.decodeStore view interpretation store) {f with code:=op.instruction::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨front,values,split,frontEq,types,wf,heights⟩ := instruction_operands immediateMeaning frameTyped stack
  have simdView := Compiler.make_simd_roundtrip_bounded opcode operand operand entry instruction
    (Itasca.Wasm2.Simd.pure_bound meaning) made
  obtain ⟨space,lastSpace,capacity⟩ := program.simd_capacity exec.slots.slice allocated instruction opcode operand entry
    _ _ _ _ fetch simdView immediateMeaning.shape
  have memories := module_memories_issued view interpretation store inst C (moduleEq ▸ point.bindings)
  have represented : ValuesAt exec.slots.val raw.base.val ((f.locals++front)++values) := by
    simpa only [FrameSlots,split,List.append_assoc] using slots
  have position' : operand.val=Compiler.slots ((f.locals++front).map Compiler.valueType) := by
    simpa only [List.map_append,Compiler.slots_append,point.locals,frontEq] using position
  apply step_simd_of_view memory hooks floats allocator exec store platform index raw inst compiled instruction
    opcode operand operand entry last hf hi hc fetch (program.fetched_bound _ fetch) simdView
  intro pc pcNext
  apply WP.spec_mono (execute_simd_pure_values_mutation_bounded memory floats interpretation view memoryLaws floatLaws
    {exec with frames:=exec.frames.set index {raw with pc:=pc}} store raw.instance raw.function raw.base
    opcode operand entry inst compiled imm op (f.locals++front) values hi hc immediate meaning memories
    position' represented wf types space lastSpace capacity)
  rintro out ⟨mutation,value,source,ok,decoded,metadata,effect,resultSlots⟩
  let updated : SourceMachine.AFrame := {f with code:=after,vals:=front++[Interp.Simd.pureResult op.signature value.bv]}
  have resultType : SourceMachine.valueType (Interp.Simd.pureResult op.signature value.bv)=Compiler.simdPureOutput op.signature := by
    cases op.signature <;> rfl
  have step : SourceMachine.Simd.Step ⟨Store.decodeStore view interpretation store,ambient,{f with code:=op.instruction::after}::rest,[]⟩
      (.next ⟨Store.decodeStore view interpretation out.2.2,ambient,updated::rest,[]⟩) := by
    rw [decoded]
    apply SourceMachine.Simd.Step.pure sig
    exact .next front values _ split
      (by simpa only [show Compiler.valueType=SourceMachine.valueType from funext value_type_eq_abs] using types) ⟨source,resultType⟩
  refine ⟨ok,rfl,mutation,metadata,pc,updated,pcNext,effect.2,?_,?_,?_,?_,step⟩
  · rw [effect.1]
    exact .simd_result raw.base.val exec.slots.val (raw.base.val+operand.val) _ value (by omega)
  · simpa only [FrameSlots,updated,List.append_assoc] using resultSlots
  · exact ⟨rfl,rfl,rfl,rfl⟩
  · apply frame_point_continue point (step.next_extension typed) front values [_] after split heights _ pc pcNext
    have outputEq : [Compiler.valueType (Interp.Simd.pureResult op.signature value.bv)]=op.signature.outputs := by
      cases op.signature <;> rfl
    simpa only [List.map_cons,List.map_nil,outputEq,frontEq] using tail

end Itasca.Runtime.Interp.Machine.Simd

end

/-! ## ShuffleFrame -/

section

/-!
SIMD shuffle execution at a structured frame point.

Main declarations: `step_shuffle_frame`. A direct consumer is `Interp.Machine.Simd.FrameStep`.
-/

namespace Itasca.Runtime.Interp.Machine.Simd
open Aeneas Aeneas.Std Itasca.Wasm2.Simd
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem step_shuffle_frame {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (interpretation : Store.CodeInterpretation)
    (memoryLaws : Platform.MemoryLaws memory view)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (raw : runtime.interp.Frame) (index : Usize) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Compiler.LabelTarget)
    (next : Nat) (output : List valtype) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (frontTypes : List valtype) (low high : U64)
    (operand entry : U32) (imm : runtime.bytecode.SimdImmediate) (instruction : Compiler.Bytecode)
    (last : index.val+1=exec.frames.length) (hf : exec.frames.val[index.val]?=some raw)
    (hi : store.instances.val[raw.instance.val]?=some inst)
    (hc : inst.module.functions.val[raw.function.val]?=some compiled)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS)
    (allocated : raw.base.val+compiled.slot_count.val≤exec.slots.length)
    (typed : SourceMachine.CoreTyped ⟨Store.decodeStore view interpretation store,ambient,
      {f with code:=(shuffle low high)::after}::rest,[]⟩)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view interpretation store) raw
      {f with code:=(shuffle low high)::after} compiled C targets next output)
    (stack : f.vals.map Compiler.valueType=frontTypes++[valtype.V128,valtype.V128])
    (combined : imm.bits.val=low.val+high.val*2^64)
    (immediate : compiled.simd.val[entry.val]?=some imm)
    (made : runtime.bytecode.Instr.make_simd 13#u32 operand operand entry=.ok (some instruction))
    (position : operand.val=Compiler.slots C.LOCALS+Compiler.slots frontTypes)
    (fetch : compiled.code.val[raw.pc.val]?=some instruction)
    (tail : Compiler.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val compiled.jump_tables.val targets (frontTypes++[valtype.V128]) after (raw.pc.val+1) next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1=.Ok () ∧ out.2.2.2=platform ∧ SimdStoreMutation view store out.2.2.1 ∧
      FrameStoreMetadata store out.2.2.1 ∧ ∃ pc : U32, ∃ updated : SourceMachine.AFrame,
      pc.val=raw.pc.val+1 ∧
      {out.2.1 with slots:=exec.slots}={exec with frames:=exec.frames.set index {raw with pc:=pc}} ∧
      SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ∧
      FrameSlots out.2.1 {raw with pc:=pc} updated ∧
      FrameMetadata {f with code:=(shuffle low high)::after} updated ∧
      FramePoint (Store.decodeStore view interpretation out.2.2.1) {raw with pc:=pc}
        updated compiled C targets next output ∧
      SourceMachine.Simd.Step ⟨Store.decodeStore view interpretation store,ambient,{f with code:=(shuffle low high)::after}::rest,[]⟩
        (.next ⟨Store.decodeStore view interpretation out.2.2.1,ambient,updated::rest,[]⟩) ⦄ := by
  have sig : SourceMachine.Simd.PureSignature (shuffle low high) [.V128,.V128] .V128 := by
    with_unfolding_all exact .shuffle _ _
  have immediateMeaning := Compiler.SimdImmediateMeaning.shuffle (C:=C) imm low high combined
  have frameTyped : SourceMachine.FrameTyped (Store.decodeStore view interpretation store) {f with code:=(shuffle low high)::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨front,values,split,frontEq,types,wf,heights⟩ := instruction_operands immediateMeaning frameTyped stack
  have simdView := Compiler.make_simd_roundtrip_bounded 13#u32 operand operand entry instruction
    (by decide) made
  obtain ⟨space,lastSpace,capacity⟩ := program.simd_capacity exec.slots.slice allocated instruction 13#u32 operand entry
    _ _ _ _ fetch simdView immediateMeaning.shape
  obtain ⟨D,actualFront,actualValues,ins,outs,_,_,operation,_⟩ := SourceMachine.frame_typed_operands_bounds frameTyped
  have valid : ∀ lane ∈ shuffleIndices low high, proj_uN_0 lane < 32 := by
    cases operation
    cases_type fun_dim
    assumption
  have memories := module_memories_issued view interpretation store inst C (moduleEq ▸ point.bindings)
  have represented : ValuesAt exec.slots.val raw.base.val ((f.locals++front)++values) := by
    simpa only [FrameSlots,split,List.append_assoc] using slots
  have position' : operand.val=Compiler.slots ((f.locals++front).map Compiler.valueType) := by
    simpa only [List.map_append,Compiler.slots_append,point.locals,frontEq] using position
  apply step_simd_of_view memory hooks floats allocator exec store platform index raw inst compiled instruction
    13#u32 operand operand entry last hf hi hc fetch (program.fetched_bound _ fetch) simdView
  intro pc pcNext
  apply WP.spec_mono (execute_simd_shuffle_values memory floats interpretation view memoryLaws
    {exec with frames:=exec.frames.set index {raw with pc:=pc}} store raw.instance raw.function raw.base
    operand entry inst compiled imm low high (f.locals++front) values hi hc immediate combined valid memories
    position' represented wf types (by change raw.base.val+operand.val+2+2≤Usize.max at space; omega) capacity)
  rintro out ⟨mutation,value,source,ok,decoded,metadata,effect,resultSlots⟩
  let updated : SourceMachine.AFrame := {f with code:=after,vals:=front++[Spec.Simd.valueOfBits .V128 value.bv]}
  have resultType : SourceMachine.valueType (Spec.Simd.valueOfBits .V128 value.bv)=valtype.V128 := by
    rfl
  have step : SourceMachine.Simd.Step ⟨Store.decodeStore view interpretation store,ambient,{f with code:=(shuffle low high)::after}::rest,[]⟩
      (.next ⟨Store.decodeStore view interpretation out.2.2,ambient,updated::rest,[]⟩) := by
    rw [decoded]
    apply SourceMachine.Simd.Step.pure sig
    exact .next front values _ split
      (by simpa only [show Compiler.valueType=SourceMachine.valueType from funext value_type_eq_abs] using types) ⟨source,resultType⟩
  refine ⟨ok,rfl,mutation,metadata,pc,updated,pcNext,effect.2,?_,?_,?_,?_,step⟩
  · rw [effect.1]
    exact .simd_result raw.base.val exec.slots.val (raw.base.val+operand.val) _ value (by omega)
  · simpa only [FrameSlots,updated,List.append_assoc] using resultSlots
  · exact ⟨rfl,rfl,rfl,rfl⟩
  · apply frame_point_continue point (step.next_extension typed) front values [_] after split heights _ pc pcNext
    have outputEq : [Compiler.valueType (Spec.Simd.valueOfBits .V128 value.bv)]=[valtype.V128] := by
      rfl
    simpa only [List.map_cons,List.map_nil,outputEq,frontEq] using tail

end Itasca.Runtime.Interp.Machine.Simd

end

/-! ## FrameStep -/

section

/-!
SIMD execution from a prepared frame point.

Main declarations: `frame_point_step`. A direct consumer is `Interp.Machine.Simd.Execution`.
-/

namespace Itasca.Runtime.Interp.Machine.Simd
open Aeneas Aeneas.Std Itasca.Wasm2.Simd
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

theorem frame_point_step {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (interpretation : Store.CodeInterpretation)
    (memoryLaws : Platform.MemoryLaws memory view) (floatLaws : Platform.FloatOpsCorrect floats)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (raw : runtime.interp.Frame) (index : Usize) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Compiler.LabelTarget)
    (next : Nat) (output : List valtype) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (source : instr) (after : List instr)
    (last : index.val+1=exec.frames.length) (hf : exec.frames.val[index.val]?=some raw)
    (hi : store.instances.val[raw.instance.val]?=some inst)
    (hc : inst.module.functions.val[raw.function.val]?=some compiled)
    (moduleEq : f.module=Store.decodeInstance store inst)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS)
    (allocated : raw.base.val+compiled.slot_count.val≤exec.slots.length)
    (typed : SourceMachine.CoreTyped ⟨Store.decodeStore view interpretation store,ambient,{f with code:=source::after}::rest,[]⟩)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view interpretation store) raw
      {f with code:=source::after} compiled C targets next output)
    (allowed : SourceMachine.SimdInstr source)
    (project : ∀ before emitted result, Interp.emission compiled C before source emitted result →
      Compiler.SimdEmission compiled.simd.val compiled.v128_pool.val C before source emitted result) :
    (∃ target : U32, raw.pc.val<target.val ∧ compiled.code.val[raw.pc.val]?=some (.Jump target) ∧
      FramePoint (Store.decodeStore view interpretation store) {raw with pc:=target}
        {f with code:=source::after} compiled C targets next output) ∨
    (runtime.interp.step memory hooks floats allocator exec store platform ⦃ FrameOutcome view interpretation
      store exec platform raw index compiled C targets next output ambient {f with code:=source::after} rest ⦄) := by
  rcases frame_point_head source after allowed project point with jump | ⟨instruction,result,head,fetch,tail⟩
  · exact Or.inl jump
  · apply Or.inr
    generalize stackEq : f.vals.map Compiler.valueType=stack at head
    cases head with
    | instruction front inputs outputs source opcode operand entry imm instruction meaning immediate made position =>
      cases meaning with
      | pure opcode imm op meaning =>
        apply WP.spec_mono (step_pure_frame memory hooks floats allocator view interpretation memoryLaws floatLaws
          exec store platform raw index inst compiled C targets next output ambient f rest after front op
          opcode operand entry imm instruction last hf hi hc moduleEq program allocated typed slots point stackEq
          meaning immediate made position fetch tail)
        rintro out ⟨ok,platformEq,mutation,metadata,pc,g,pcNext,effect⟩
        exact ⟨platformEq,mutation,metadata,pc,pcNext,Or.inl ⟨ok,g,effect⟩⟩
      | lane opcode imm op meaning lane lanePosition =>
        apply WP.spec_mono (step_lane_frame memory hooks floats allocator view interpretation memoryLaws
          exec store platform raw index inst compiled C targets next output ambient f rest after front op lane
          opcode operand entry imm instruction last hf hi hc moduleEq program allocated typed slots point stackEq
          meaning lanePosition immediate made position fetch tail)
        rintro out ⟨ok,platformEq,mutation,metadata,pc,g,pcNext,effect⟩
        exact ⟨platformEq,mutation,metadata,pc,pcNext,Or.inl ⟨ok,g,effect⟩⟩
      | memory opcode imm op meaning argument lane memoryType available offset lanePosition =>
        exact step_memory_frame memory hooks floats allocator view interpretation memoryLaws
          exec store platform raw index inst compiled C targets next output ambient f rest after front op argument lane
          opcode operand entry imm instruction last hf hi hc moduleEq program allocated typed slots point stackEq
          meaning memoryType available offset lanePosition immediate made position fetch tail
      | shuffle imm low high combined =>
        apply WP.spec_mono (step_shuffle_frame memory hooks floats allocator view interpretation memoryLaws
          exec store platform raw index inst compiled C targets next output ambient f rest after front low high
          operand entry imm instruction last hf hi hc moduleEq program allocated typed slots point stackEq
          combined immediate made position fetch tail)
        rintro out ⟨ok,platformEq,mutation,metadata,pc,g,pcNext,effect⟩
        exact ⟨platformEq,mutation,metadata,pc,pcNext,Or.inl ⟨ok,g,effect⟩⟩
    | constant front bits dst entry immediate position =>
      rw [←stackEq] at position tail
      apply WP.spec_mono (step_constant_frame memory hooks floats allocator view interpretation
        exec store platform raw index inst compiled C targets next output ambient f rest after bits dst entry
        last hf hi hc program allocated typed slots point immediate position fetch tail)
      rintro out ⟨ok,platformEq,mutation,metadata,pc,g,pcNext,effect⟩
      exact ⟨platformEq,mutation,metadata,pc,pcNext,Or.inl ⟨ok,g,effect⟩⟩

end Itasca.Runtime.Interp.Machine.Simd

end
