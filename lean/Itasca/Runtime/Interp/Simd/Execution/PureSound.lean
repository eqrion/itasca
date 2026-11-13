import Itasca.Runtime.Interp.Simd.Relations.Mutation
import Itasca.Runtime.Interp.Simd.Memory.Execute
import Itasca.Runtime.Interp.Memory.MemorySize
import Itasca.Runtime.Interp.Relations.FrameStoreMetadata
import Itasca.Runtime.Interp.Simd.Relations.InputValues
import Itasca.Runtime.Interp.Simd.Relations.NumericResultSlots
import Itasca.Runtime.Interp.Simd.Lanes.LaneEntries
import Itasca.Runtime.Interp.Simd.Relations.PureRelation
import Itasca.Runtime.Interp.Simd.Integer.Compare
import Itasca.Runtime.Interp.Simd.Float.Compare
import Itasca.Runtime.Interp.Simd.Float.PureEntries
import Itasca.Runtime.Interp.Simd.Integer.PureInteger
import Itasca.Runtime.Interp.Simd.Execution.PureUnary
import Mathlib.Tactic.IntervalCases

/-!
Sections, each formerly its own module: ExecuteSource, LaneValuesExecute, PureCompare, PureSound.
-/

/-! ## ExecuteSource -/

section

/-!
Bounded SIMD execution with source store-mutation correspondence.

Main declarations: `execute_simd_source_mutation_bounded`. A direct consumer is `Interp.Simd.Execution.LaneValuesExecute`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem execute_simd_source_mutation_bounded {M F : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (interpretation : Itasca.Runtime.Store.CodeInterpretation) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instIndex function base : Usize) (op dst a entry : U32)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (imm : runtime.bytecode.SimdImmediate) (wa wb wc wr : U32)
    (source : U128 → Prop)
    (found : store.instances.val[instIndex.val]? = some inst)
    (compiled : inst.module.functions.val[function.val]? = some code)
    (immediate : code.simd.val[entry.val]? = some imm)
    (shape : runtime.bytecode.simd_shape op = .ok (some (wa,wb,wc,wr)))
    (memories : ∀ ma, inst.memories.val[0]? = some ma →
      ∃ object, store.memories.val[ma.index.val]? = some object)
    (space : base.val + a.val + wa.val + wb.val ≤ Usize.max)
    (lastSpace : wc = 2#u32 → base.val + a.val + wa.val + wb.val < Usize.max)
    (capacity : base.val + dst.val + wr.val ≤ exec.slots.length)
    (numeric : ∀ bytes, runtime.interp.simd.simd floats op imm.offset imm.lane imm.bits
      (simdInput exec.slots.val (base.val+a.val) wa)
      (simdInput exec.slots.val (base.val+a.val+wa.val) wb)
      (simdInput exec.slots.val (base.val+a.val+wa.val+wb.val) wc) bytes
      ⦃ result => ∃ value, result = (.Ok value,bytes) ∧ source value ⦄) :
    runtime.interp.execute_simd memory floats exec store instIndex function base op dst a entry
      ⦃ out => SimdStoreMutation view store out.2.2 ∧ ∃ value, source value ∧ out.1 = .Ok () ∧
        Itasca.Runtime.Store.decodeStore view interpretation out.2.2 = Itasca.Runtime.Store.decodeStore view interpretation store ∧
        FrameStoreMetadata store out.2.2 ∧ SlotsEffect exec out.2.1
        (simdResultSlots exec.slots.val (base.val+dst.val) wr value) ⦄ := by
  cases lookup : inst.memories.val[0]? with
  | none =>
    have empty : inst.memories.val = [] := by
      cases h : inst.memories.val with
      | nil => rfl
      | cons first rest => simp [h] at lookup
    obtain ⟨result,run,value,resultEq,allowed⟩ := WP.spec_imp_exists (numeric none)
    rw [resultEq] at run
    apply WP.spec_mono (execute_simd_no_memory_bounded memory floats exec store instIndex function base
      op dst a entry inst code imm wa wb wc wr value found compiled immediate shape empty space lastSpace capacity run)
    rintro out ⟨ok,unchanged,slots⟩
    rw [unchanged]
    exact ⟨Or.inl rfl,value,allowed,ok,rfl,⟨rfl,rfl,rfl,rfl⟩,slots⟩
  | some ma =>
    obtain ⟨object,issued⟩ := memories ma lookup
    obtain ⟨result,run,value,resultEq,allowed⟩ := WP.spec_imp_exists (numeric (some (view object.buf)))
    rw [resultEq] at run
    apply WP.spec_mono (execute_simd_pure_memory_bounded memory floats view laws exec store instIndex function base
      op dst a entry inst code imm wa wb wc wr value found compiled immediate shape ma object lookup issued space lastSpace capacity
      run)
    rintro out ⟨ok,⟨buffer,changed,bytes⟩,slots⟩
    have mutation : SimdStoreMutation view store out.2.2 :=
      Or.inr ⟨ma,object,issued,buffer,changed,by rw [bytes]⟩
    refine ⟨mutation,value,allowed,ok,?_,?_,slots⟩
    · rw [changed]
      exact memory_unchanged_decodes view interpretation store ma object buffer issued bytes
    · rw [changed]
      exact ⟨rfl,rfl,rfl,rfl⟩

end Itasca.Runtime.Interp

end

/-! ## LaneValuesExecute -/

section

/-!
Typed value correspondence for SIMD lane execution.

Main declarations: `ValuesAt.simd_lane_result` and `execute_simd_lane_values`. A direct consumer is `Interp.Machine.Simd.LaneFrame`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std Itasca.Wasm2.Simd

private theorem lane_inputs_numeric (op : LaneOperation) (ty : valtype) (member : ty ∈ op.inputs) :
    ty ≠ .FUNCREF ∧ ty ≠ .EXTERNREF := by
  cases ty <;> cases op <;> simp_all [LaneOperation.inputs,LaneOperation.replace,LaneOperation.scalar,valtype_numtype]

private theorem lane_source_shape (opcode : U32) (op : LaneOperation) (meaning : laneMeaning opcode.val = some op) :
    runtime.bytecode.simd_shape opcode = .ok (some (Compiler.simdSourceShape op.inputs op.outputs)) := by
  exact (Compiler.SimdImmediateMeaning.lane (C := default) opcode ⟨0#u32,0#u32,0#u128⟩ op meaning 0#u8 rfl).shape

theorem ValuesAt.simd_lane_result {words : List U64} {base : Nat} {front : List val}
    (represented : ValuesAt words base front) (op : LaneOperation) (value : U128)
    (bound : Simd.LaneResultBound op value)
    (capacity : base + Compiler.slots (front.map Compiler.valueType) +
      (Compiler.simdSourceWidth op.outputs[0]?).val ≤ words.length) :
    ValuesAt (simdResultSlots words (base+Compiler.slots (front.map Compiler.valueType))
      (Compiler.simdSourceWidth op.outputs[0]?) value) base (front ++ [Simd.laneResult op value.bv]) := by
  let ty := if op.replace then valtype.V128 else valtype_numtype op.scalar
  have outputs : op.outputs = [ty] := by cases op <;> rfl
  have numeric : ty ≠ .FUNCREF ∧ ty ≠ .EXTERNREF ∧ ty ≠ .BOT := by cases op <;> decide
  have small : ty = .I32 ∨ ty = .F32 → value.val < 2^32 := by
    intro small
    cases op <;> first | exact bound rfl | cases small <;> contradiction
  simpa only [outputs,List.getElem?_cons_zero,Simd.laneResult] using
    represented.simd_numeric_result ty value numeric small (by simpa only [outputs,List.getElem?_cons_zero] using capacity)

theorem execute_simd_lane_values {M F : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (interpretation : Store.CodeInterpretation) (view : M → Slice U8) (memoryLaws : Platform.MemoryLaws memory view)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instIndex function base : Usize) (opcode operand entry : U32)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (imm : runtime.bytecode.SimdImmediate) (op : LaneOperation) (front values : List val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (compiled : inst.module.functions.val[function.val]? = some code)
    (immediate : code.simd.val[entry.val]? = some imm)
    (meaning : laneMeaning opcode.val = some op) (valid : imm.lane.val < op.count)
    (memories : ∀ ma, inst.memories.val[0]? = some ma → ∃ object, store.memories.val[ma.index.val]? = some object)
    (position : operand.val = Compiler.slots (front.map Compiler.valueType))
    (represented : ValuesAt exec.slots.val base.val (front ++ values))
    (wellFormed : Forall wf_val values) (typed : values.map Compiler.valueType = op.inputs)
    (space : base.val + operand.val + (Compiler.simdSourceWidth op.inputs[0]?).val +
      (Compiler.simdSourceWidth op.inputs[1]?).val ≤ Usize.max)
    (lastSpace : Compiler.simdSourceWidth op.inputs[2]? = 2#u32 → base.val + operand.val +
      (Compiler.simdSourceWidth op.inputs[0]?).val + (Compiler.simdSourceWidth op.inputs[1]?).val < Usize.max)
    (capacity : base.val + operand.val + (Compiler.simdSourceWidth op.outputs[0]?).val ≤ exec.slots.length) :
    runtime.interp.execute_simd memory floats exec store instIndex function base opcode operand operand entry
      ⦃ out => SimdStoreMutation view store out.2.2 ∧ ∃ value, Step_pure (values.map admininstr_val ++ [admininstr_instr (op.instruction (.mk_uN imm.lane.val))])
          [admininstr_val (Simd.laneResult op value.bv)] ∧
        out.1 = .Ok () ∧ Store.decodeStore view interpretation out.2.2 = Store.decodeStore view interpretation store ∧
        FrameStoreMetadata store out.2.2 ∧
        SlotsEffect exec out.2.1 (simdResultSlots exec.slots.val (base.val+operand.val)
          (Compiler.simdSourceWidth op.outputs[0]?) value) ∧
        ValuesAt out.2.1.slots.val base.val (front ++ [Simd.laneResult op value.bv]) ⦄ := by
  have numeric : ∀ value ∈ values, Compiler.valueType value ≠ .FUNCREF ∧ Compiler.valueType value ≠ .EXTERNREF := by
    intro value member
    have m : Compiler.valueType value ∈ op.inputs := by rw [←typed]; exact List.mem_map_of_mem member
    exact lane_inputs_numeric op _ m
  have arity : values.length ≤ 3 := by
    have length := congrArg List.length typed
    simp only [List.length_map] at length
    have bound : op.inputs.length ≤ 3 := by cases op <;> decide
    omega
  have inputs := represented.operands.simd_operands wellFormed numeric arity
  dsimp only at inputs
  rw [typed,←position] at inputs
  apply WP.spec_mono (execute_simd_source_mutation_bounded memory floats interpretation view memoryLaws exec store instIndex function base
    opcode operand operand entry inst code imm
    (Compiler.simdSourceWidth op.inputs[0]?) (Compiler.simdSourceWidth op.inputs[1]?)
    (Compiler.simdSourceWidth op.inputs[2]?) (Compiler.simdSourceWidth op.outputs[0]?)
    (fun value => Step_pure (values.map admininstr_val ++ [admininstr_instr (op.instruction (.mk_uN imm.lane.val))])
      [admininstr_val (Simd.laneResult op value.bv)] ∧ Simd.LaneResultBound op value)
    found compiled immediate (lane_source_shape opcode op meaning) memories space lastSpace capacity ?_)
  · rintro out ⟨mutation,value,⟨source,bounded⟩,ok,decoded,metadata,slots⟩
    refine ⟨mutation,value,source,ok,decoded,metadata,slots,?_⟩
    rw [slots.1,position]
    exact represented.locals.simd_lane_result op value bounded (by simpa only [position] using capacity)
  · intro bytes
    apply WP.spec_mono (Simd.lane_entry_sound floats opcode op meaning imm.offset imm.lane imm.bits
      (simdInput exec.slots.val (base.val+operand.val) (Compiler.simdSourceWidth op.inputs[0]?))
      (simdInput exec.slots.val (base.val+operand.val+(Compiler.simdSourceWidth op.inputs[0]?).val) (Compiler.simdSourceWidth op.inputs[1]?))
      (simdInput exec.slots.val (base.val+operand.val+(Compiler.simdSourceWidth op.inputs[0]?).val+
        (Compiler.simdSourceWidth op.inputs[1]?).val) (Compiler.simdSourceWidth op.inputs[2]?)) bytes valid)
    rintro result ⟨value,returned,source,bounded⟩
    refine ⟨value,returned,?_,bounded⟩
    unfold Simd.LaneSourceEffect at source
    rw [inputs] at source
    exact source
end Itasca.Runtime.Interp

end

/-! ## PureCompare -/

section

/-!
Source correspondence of pure comparison opcode entries.

Main declarations: `pure_entry_35` and `pure_entry_219`. A direct consumer is `Interp.Simd.Execution.PureSound`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

theorem pure_entry_35 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 35#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure35 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I8 .EQ offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_36 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 36#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure36 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I8 .NE offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_37 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 37#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure37 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I8 (.LT .S) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_38 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 38#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure38 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I8 (.LT .U) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_39 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 39#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure39 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I8 (.GT .S) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_40 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 40#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure40 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I8 (.GT .U) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_41 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 41#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure41 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I8 (.LE .S) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_42 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 42#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure42 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I8 (.LE .U) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_43 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 43#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure43 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I8 (.GE .S) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_44 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 44#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure44 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I8 (.GE .U) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_45 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 45#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure45 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I16 .EQ offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_46 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 46#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure46 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I16 .NE offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_47 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 47#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure47 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I16 (.LT .S) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_48 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 48#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure48 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I16 (.LT .U) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_49 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 49#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure49 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I16 (.GT .S) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_50 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 50#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure50 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I16 (.GT .U) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_51 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 51#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure51 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I16 (.LE .S) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_52 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 52#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure52 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I16 (.LE .U) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_53 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 53#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure53 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I16 (.GE .S) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_54 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 54#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure54 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I16 (.GE .U) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_55 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 55#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure55 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I32 .EQ offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_56 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 56#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure56 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I32 .NE offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_57 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 57#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure57 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I32 (.LT .S) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_58 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 58#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure58 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I32 (.LT .U) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_59 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 59#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure59 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I32 (.GT .S) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_60 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 60#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure60 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I32 (.GT .U) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_61 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 61#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure61 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I32 (.LE .S) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_62 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 62#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure62 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I32 (.LE .U) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_63 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 63#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure63 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I32 (.GE .S) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_64 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 64#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure64 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I32 (.GE .U) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_65 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 65#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure65 = some op at meaning
  cases meaning
  with_unfolding_all exact float_compare_simd_sound floats .F32 .EQ offset laneIndex bits x y z memory

theorem pure_entry_66 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 66#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure66 = some op at meaning
  cases meaning
  with_unfolding_all exact float_compare_simd_sound floats .F32 .NE offset laneIndex bits x y z memory

theorem pure_entry_67 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 67#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure67 = some op at meaning
  cases meaning
  with_unfolding_all exact float_compare_simd_sound floats .F32 .LT offset laneIndex bits x y z memory

theorem pure_entry_68 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 68#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure68 = some op at meaning
  cases meaning
  with_unfolding_all exact float_compare_simd_sound floats .F32 .GT offset laneIndex bits x y z memory

theorem pure_entry_69 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 69#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure69 = some op at meaning
  cases meaning
  with_unfolding_all exact float_compare_simd_sound floats .F32 .LE offset laneIndex bits x y z memory

theorem pure_entry_70 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 70#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure70 = some op at meaning
  cases meaning
  with_unfolding_all exact float_compare_simd_sound floats .F32 .GE offset laneIndex bits x y z memory

theorem pure_entry_71 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 71#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure71 = some op at meaning
  cases meaning
  with_unfolding_all exact float_compare_simd_sound floats .F64 .EQ offset laneIndex bits x y z memory

theorem pure_entry_72 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 72#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure72 = some op at meaning
  cases meaning
  with_unfolding_all exact float_compare_simd_sound floats .F64 .NE offset laneIndex bits x y z memory

theorem pure_entry_73 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 73#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure73 = some op at meaning
  cases meaning
  with_unfolding_all exact float_compare_simd_sound floats .F64 .LT offset laneIndex bits x y z memory

theorem pure_entry_74 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 74#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure74 = some op at meaning
  cases meaning
  with_unfolding_all exact float_compare_simd_sound floats .F64 .GT offset laneIndex bits x y z memory

theorem pure_entry_75 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 75#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure75 = some op at meaning
  cases meaning
  with_unfolding_all exact float_compare_simd_sound floats .F64 .LE offset laneIndex bits x y z memory

theorem pure_entry_76 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 76#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure76 = some op at meaning
  cases meaning
  with_unfolding_all exact float_compare_simd_sound floats .F64 .GE offset laneIndex bits x y z memory

theorem pure_entry_214 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 214#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure214 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I64 .EQ offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_215 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 215#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure215 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I64 .NE offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_216 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 216#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure216 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I64 (.LT .S) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_217 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 217#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure217 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I64 (.GT .S) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_218 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 218#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure218 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I64 (.LE .S) offset laneIndex bits x y z memory (by trivial)

theorem pure_entry_219 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 219#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure219 = some op at meaning
  cases meaning
  with_unfolding_all exact integer_compare_simd_sound floats .I64 (.GE .S) offset laneIndex bits x y z memory (by trivial)

end Itasca.Runtime.Interp.Simd

end

/-! ## PureSound -/

section

/-!
Every source-table pure SIMD operation refines its generated source rule.

Main declarations: `pure_entries` and `pure_dispatch_source`. A direct consumer is `Interp.Simd.Execution.PureValuesExecute`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- Every source-table pure SIMD operation refines its generated source rule. -/
theorem pure_entries {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : Platform.FloatOpsCorrect floats) (opcode : U32) (bounded : opcode.val < 256) :
    PureEntrySound floats opcode := by
  rcases opcode with ⟨⟨n,hn⟩⟩
  change n < 256 at bounded
  interval_cases n
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · exact pure_entry_14 floats
  · exact pure_entry_15 floats
  · exact pure_entry_16 floats
  · exact pure_entry_17 floats
  · exact pure_entry_18 floats
  · exact pure_entry_19 floats
  · exact pure_entry_20 floats
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · exact pure_entry_35 floats
  · exact pure_entry_36 floats
  · exact pure_entry_37 floats
  · exact pure_entry_38 floats
  · exact pure_entry_39 floats
  · exact pure_entry_40 floats
  · exact pure_entry_41 floats
  · exact pure_entry_42 floats
  · exact pure_entry_43 floats
  · exact pure_entry_44 floats
  · exact pure_entry_45 floats
  · exact pure_entry_46 floats
  · exact pure_entry_47 floats
  · exact pure_entry_48 floats
  · exact pure_entry_49 floats
  · exact pure_entry_50 floats
  · exact pure_entry_51 floats
  · exact pure_entry_52 floats
  · exact pure_entry_53 floats
  · exact pure_entry_54 floats
  · exact pure_entry_55 floats
  · exact pure_entry_56 floats
  · exact pure_entry_57 floats
  · exact pure_entry_58 floats
  · exact pure_entry_59 floats
  · exact pure_entry_60 floats
  · exact pure_entry_61 floats
  · exact pure_entry_62 floats
  · exact pure_entry_63 floats
  · exact pure_entry_64 floats
  · exact pure_entry_65 floats
  · exact pure_entry_66 floats
  · exact pure_entry_67 floats
  · exact pure_entry_68 floats
  · exact pure_entry_69 floats
  · exact pure_entry_70 floats
  · exact pure_entry_71 floats
  · exact pure_entry_72 floats
  · exact pure_entry_73 floats
  · exact pure_entry_74 floats
  · exact pure_entry_75 floats
  · exact pure_entry_76 floats
  · exact pure_entry_77 floats
  · exact pure_entry_78 floats
  · exact pure_entry_79 floats
  · exact pure_entry_80 floats
  · exact pure_entry_81 floats
  · exact pure_entry_82 floats
  · exact pure_entry_83 floats
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · exact pure_entry_94 floats laws
  · exact pure_entry_95 floats laws
  · exact pure_entry_96 floats
  · exact pure_entry_97 floats
  · exact pure_entry_98 floats
  · exact pure_entry_99 floats
  · exact pure_entry_100 floats
  · exact pure_entry_101 floats
  · exact pure_entry_102 floats
  · exact pure_entry_103 floats laws
  · exact pure_entry_104 floats laws
  · exact pure_entry_105 floats laws
  · exact pure_entry_106 floats laws
  · exact pure_entry_107 floats
  · exact pure_entry_108 floats
  · exact pure_entry_109 floats
  · exact pure_entry_110 floats
  · exact pure_entry_111 floats
  · exact pure_entry_112 floats
  · exact pure_entry_113 floats
  · exact pure_entry_114 floats
  · exact pure_entry_115 floats
  · exact pure_entry_116 floats laws
  · exact pure_entry_117 floats laws
  · exact pure_entry_118 floats
  · exact pure_entry_119 floats
  · exact pure_entry_120 floats
  · exact pure_entry_121 floats
  · exact pure_entry_122 floats laws
  · exact pure_entry_123 floats
  · exact pure_entry_124 floats
  · exact pure_entry_125 floats
  · exact pure_entry_126 floats
  · exact pure_entry_127 floats
  · exact pure_entry_128 floats
  · exact pure_entry_129 floats
  · exact pure_entry_130 floats
  · exact pure_entry_131 floats
  · exact pure_entry_132 floats
  · exact pure_entry_133 floats
  · exact pure_entry_134 floats
  · exact pure_entry_135 floats
  · exact pure_entry_136 floats
  · exact pure_entry_137 floats
  · exact pure_entry_138 floats
  · exact pure_entry_139 floats
  · exact pure_entry_140 floats
  · exact pure_entry_141 floats
  · exact pure_entry_142 floats
  · exact pure_entry_143 floats
  · exact pure_entry_144 floats
  · exact pure_entry_145 floats
  · exact pure_entry_146 floats
  · exact pure_entry_147 floats
  · exact pure_entry_148 floats laws
  · exact pure_entry_149 floats
  · exact pure_entry_150 floats
  · exact pure_entry_151 floats
  · exact pure_entry_152 floats
  · exact pure_entry_153 floats
  · intro op meaning
    change none = some op at meaning
    contradiction
  · exact pure_entry_155 floats
  · exact pure_entry_156 floats
  · exact pure_entry_157 floats
  · exact pure_entry_158 floats
  · exact pure_entry_159 floats
  · exact pure_entry_160 floats
  · exact pure_entry_161 floats
  · intro op meaning
    change none = some op at meaning
    contradiction
  · exact pure_entry_163 floats
  · exact pure_entry_164 floats
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · exact pure_entry_167 floats
  · exact pure_entry_168 floats
  · exact pure_entry_169 floats
  · exact pure_entry_170 floats
  · exact pure_entry_171 floats
  · exact pure_entry_172 floats
  · exact pure_entry_173 floats
  · exact pure_entry_174 floats
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · exact pure_entry_177 floats
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · exact pure_entry_181 floats
  · exact pure_entry_182 floats
  · exact pure_entry_183 floats
  · exact pure_entry_184 floats
  · exact pure_entry_185 floats
  · exact pure_entry_186 floats
  · intro op meaning
    change none = some op at meaning
    contradiction
  · exact pure_entry_188 floats
  · exact pure_entry_189 floats
  · exact pure_entry_190 floats
  · exact pure_entry_191 floats
  · exact pure_entry_192 floats
  · exact pure_entry_193 floats
  · intro op meaning
    change none = some op at meaning
    contradiction
  · exact pure_entry_195 floats
  · exact pure_entry_196 floats
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · exact pure_entry_199 floats
  · exact pure_entry_200 floats
  · exact pure_entry_201 floats
  · exact pure_entry_202 floats
  · exact pure_entry_203 floats
  · exact pure_entry_204 floats
  · exact pure_entry_205 floats
  · exact pure_entry_206 floats
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · exact pure_entry_209 floats
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · exact pure_entry_213 floats
  · exact pure_entry_214 floats
  · exact pure_entry_215 floats
  · exact pure_entry_216 floats
  · exact pure_entry_217 floats
  · exact pure_entry_218 floats
  · exact pure_entry_219 floats
  · exact pure_entry_220 floats
  · exact pure_entry_221 floats
  · exact pure_entry_222 floats
  · exact pure_entry_223 floats
  · exact pure_entry_224 floats laws
  · exact pure_entry_225 floats laws
  · intro op meaning
    change none = some op at meaning
    contradiction
  · exact pure_entry_227 floats laws
  · exact pure_entry_228 floats laws
  · exact pure_entry_229 floats laws
  · exact pure_entry_230 floats laws
  · exact pure_entry_231 floats laws
  · exact pure_entry_232 floats laws
  · exact pure_entry_233 floats laws
  · exact pure_entry_234 floats laws
  · exact pure_entry_235 floats laws
  · exact pure_entry_236 floats laws
  · exact pure_entry_237 floats laws
  · intro op meaning
    change none = some op at meaning
    contradiction
  · exact pure_entry_239 floats laws
  · exact pure_entry_240 floats laws
  · exact pure_entry_241 floats laws
  · exact pure_entry_242 floats laws
  · exact pure_entry_243 floats laws
  · exact pure_entry_244 floats laws
  · exact pure_entry_245 floats laws
  · exact pure_entry_246 floats laws
  · exact pure_entry_247 floats laws
  · exact pure_entry_248 floats
  · exact pure_entry_249 floats
  · exact pure_entry_250 floats laws
  · exact pure_entry_251 floats laws
  · exact pure_entry_252 floats
  · exact pure_entry_253 floats
  · exact pure_entry_254 floats laws
  · exact pure_entry_255 floats laws

theorem pure_dispatch_source {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : Platform.FloatOpsCorrect floats) (opcode : U32) (op : Itasca.Wasm2.Simd.Operation)
    (meaning : Itasca.Wasm2.Simd.pureMeaning opcode.val = some op)
    (offset laneIndex : U32) (bits x y z : U128) (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats opcode offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧ PureSourceEffect op x.bv y.bv z.bv value.bv ⦄ := by
  exact pure_entries floats laws opcode (Itasca.Wasm2.Simd.pure_bound meaning)
    op meaning offset laneIndex bits x y z memory
end Itasca.Runtime.Interp.Simd

end
