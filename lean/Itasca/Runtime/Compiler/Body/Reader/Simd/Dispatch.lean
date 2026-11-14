import Itasca.Runtime.Compiler.Body.Reader.Simd.SimdEmissions
import Itasca.Runtime.Compiler.Body.Lowering.Simd.SimdCallbackMeaning
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdBitsCallbacks
import Itasca.Runtime.Compiler.Local.Control.Simd.StructuredSimdEmbedding
import Itasca.Runtime.Compiler.Body.Callbacks.Prefix.CompilerPrefixStart
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels
import Itasca.Runtime.Compiler.Local.Relations.Prefix.SuspendedPrefix
import Itasca.Runtime.Compiler.Local.Relations.Prefix.PrefixZipper
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalPrefix
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalDormant
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerTerminalMetadata
import Itasca.Runtime.Compiler.Body.Reader.Replay.MetadataTypes
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerAuxiliaryTables
import Itasca.Runtime.Compiler.Body.Reader.Memory.MemoryEmissions
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdEffects

/-!
Sections, each formerly its own module: CallbackEmission, SimdEvent, Memory, Dispatch.
-/

/-! ## CallbackEmission -/

section

/-!
SIMD constant emission and callback lowering certificates, consumed by structured reader prefixes.
-/

/-! ## Reader Simd Constant Fixed -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem reader_simd_constant_fixed_emission {data env locals index st values position}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (C : context) (a b : U32) (bits : U128)
    (post : Wasm2.ReaderPost p out (.VCONST .V128 (.mk_uN bits.val)) p.current.ctrl.polymorphic_base values)
    (effect : Wasm2.Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals [] (some .V128) values)
    (read : Wasm2.Simd.readFixed {st.core with pos := position} [] (some .V128) = .ok (.Ok (),out))
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (capacity : st.core.vals.val.length < Usize.max)
    (contextLocals : C.LOCALS = compilerLocals before)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before out 524#u16 a b bits = .ok (.Ok (),after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧ after.next_source = out.pos ∧
    after.function.simd = before.function.simd ∧ after.function.v128_pool.val = before.function.v128_pool.val ++ [bits] ∧
    ∃ emitted, TypedLowered before after out.vals.val emitted (Sequence.stackTypes st.core.vals.val ++ [.V128]) ∧
      SimdEmission after.function.simd.val after.function.v128_pool.val C
        (Sequence.stackTypes st.core.vals.val) (.VCONST .V128 (.mk_uN bits.val)) [emitted]
          (Sequence.stackTypes st.core.vals.val ++ [.V128]) := by
  rw [lower_simd_dispatch ops before out 524#u16 a b bits reachable (by decide) (by decide)] at accepted
  have ordinary := compiler_simd_ordinary_result ops law before after out 524#u16 a bits (.Ok ()) accepted
  have sources := compiler_simd_sources ops law before after out 524#u16 a bits accepted
  have cursor := compiler_simd_cursor ops law before after out 524#u16 a bits accepted
  obtain ⟨front,types,oldTypes,concrete,newTypes⟩ := reader_simd_fixed_types post effect read known monomorphic capacity
  simp only [Wasm2.Simd.inputTypes,List.reverse_nil,List.map_nil,List.append_nil] at oldTypes
  have finalTypes : types.map Translate.valueType = Sequence.stackTypes st.core.vals.val ++ [.V128] := by
    change types.map Translate.valueType = front ++ [.V128] at newTypes
    simpa only [oldTypes] using newTypes
  obtain ⟨pool,simd,emitted,lowered,emission⟩ := compiler_simd_const_emission ops law before after out types C
    (Sequence.stackTypes st.core.vals.val) a bits contextLocals layout concrete finalTypes
    codeFits sourceFits coordinateFits accepted
  exact ⟨ordinary,sources,cursor,simd,pool,emitted,⟨lowered,SourceStack.of_map types concrete finalTypes⟩,emission⟩
end Itasca.Runtime.Compiler

end

/-! ## Reader Simd Callback Emission -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Every independently classified SIMD callback yields typed emitted code
and an exact append to the four syntactic function tables. -/
theorem reader_simd_callback_emission {data env locals index st source values position inputs output}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (C : context) (opcode : U16) (sub a b : U32) (bits : U128)
    (number : opcode.val = 512 + sub.val)
    (meaning : SimdCallbackMeaning C sub a bits inputs source output)
    (post : Wasm2.ReaderPost p out source p.current.ctrl.polymorphic_base values)
    (effect : Wasm2.Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals inputs output values)
    (read : Wasm2.Simd.readFixed {st.core with pos := position} inputs output = .ok (.Ok (),out))
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (capacity : st.core.vals.val.length < Usize.max)
    (contextLocals : C.LOCALS = compilerLocals before)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before out opcode a b bits = .ok (.Ok (),after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧ after.next_source = out.pos ∧
    ∃ extra front emitted,
      CompilerTables.ofFunction after.function = (CompilerTables.ofFunction before.function).append extra ∧
      Sequence.stackTypes st.core.vals.val = front ++ Wasm2.Simd.inputTypes inputs ∧
      TypedLowered before after out.vals.val emitted (front ++ Wasm2.Simd.outputTypes output) ∧
      SimdEmission after.function.simd.val after.function.v128_pool.val C
        (front ++ Wasm2.Simd.inputTypes inputs) source [emitted] (front ++ Wasm2.Simd.outputTypes output) := by
  have bounded := meaning.opcode_bound
  obtain ⟨indirect,jumps⟩ := compiler_lower_simd_preserved_tables ops law before after out opcode a b bits (by omega) (by omega) accepted
  cases meaning with
  | instruction meaning =>
    obtain ⟨ordinary,sources,cursor,simd,pool,front,emitted,oldTypes,lowered,emission⟩ :=
      reader_simd_fixed_emission p ops law before after out C opcode sub a b bits number bounded meaning.not_constant
        meaning post effect read known monomorphic capacity contextLocals layout reachable codeFits sourceFits coordinateFits accepted
    refine ⟨ordinary,sources,cursor,⟨[],[simdImmediate sub a bits],[],[]⟩,front,emitted,?_,oldTypes,lowered,emission⟩
    simp only [CompilerTables.ofFunction,CompilerTables.append,indirect,jumps,simd,pool,List.append_nil]
  | constant a bits =>
    have opcodeEq : opcode = 524#u16 := by scalar_tac
    subst opcode
    obtain ⟨ordinary,sources,cursor,simd,pool,emitted,lowered,emission⟩ :=
      reader_simd_constant_fixed_emission p ops law before after out C a b bits post effect read known monomorphic
        capacity contextLocals layout reachable codeFits sourceFits coordinateFits accepted
    refine ⟨ordinary,sources,cursor,⟨[],[],[bits],[]⟩,Sequence.stackTypes st.core.vals.val,emitted,?_,?_,lowered,?_⟩
    · simp only [CompilerTables.ofFunction,CompilerTables.append,indirect,jumps,simd,pool,List.append_nil]
    · simp [Wasm2.Simd.inputTypes]
    · simpa [Wasm2.Simd.inputTypes,Wasm2.Simd.outputTypes,Translate.valueType] using emission
end Itasca.Runtime.Compiler

end

end

/-! ## SimdEvent -/

section

/-!
All information retained from one actually accepted SIMD reader and callback. The source meaning is supplied by the independent opcode tables.

Main declarations: `SimdReaderEvent`. A direct consumer is `Compiler.Body.Reader.Simd.Dispatch`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- All information retained from one actually accepted SIMD reader and
callback. The source meaning is supplied by the independent opcode tables. -/
structure SimdReaderEvent {A : Type} (ops : runtime.platform.Alloc A)
    {data env locals index st} (p : Wasm2.Pending data env locals index st)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState) (C : context) where
  source : instr
  inputs : List wasm_types.ValueType
  output : Option wasm_types.ValueType
  sub : U32
  a : U32
  b : U32
  bits : U128
  opcode : U16
  number : opcode.val = 512 + sub.val
  meaning : SimdCallbackMeaning C sub a bits inputs source output
  values : List code.StackType
  position : Usize
  post : Wasm2.ReaderPost p out source p.current.ctrl.polymorphic_base values
  effect : Wasm2.Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals inputs output values
  read : Wasm2.Simd.readFixed {st.core with pos := position} inputs output = .ok (.Ok (),out)
  callback : runtime.compiler.lower.FunctionCompiler.op ops before out opcode a b bits = .ok (.Ok (),after)
  capacity : st.core.vals.val.length < Usize.max

theorem SimdReaderEvent.capacity_step {A : Type} {ops : runtime.platform.Alloc A}
    {data env locals index st p before after out C}
    (event : @SimdReaderEvent A ops data env locals index st p before after out C)
    (law : Platform.AllocCorrect ops) : CapacityStep before after out := by
  have bound := event.meaning.opcode_bound
  exact (compiler_lower_simd_effects ops law before after out event.opcode event.a event.b event.bits
    (by have number := event.number; omega) (by have number := event.number; omega) event.callback).2.2.2

end Itasca.Runtime.Compiler

end

/-! ## Memory -/

section

/-!
SIMD full-vector and lane-memory reader facts, preserving their distinct access widths and lane obligations.
-/

/-! ## Reader Simd Memory -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Full SIMD memory readers retain both encoded immediates, validated memory
availability and alignment, the exact callback, and the source prefix. -/
theorem reader_simd_memory_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (subopcode : U32) (next : Usize) (op : Wasm2.Simd.MemoryOperation)
    (decoded : Leb128.Decoded data st.core.pos subopcode next)
    (meaning : Wasm2.Simd.memoryMeaning subopcode.val = some op) (full : op.laneCount = 0)
    (byte : data.val[p.start.val]'p.inbounds = 0xfd#u8)
    (accepted : code.step_profile visitor st data env ctx index 0xfd#u8 before =
      .ok (.Ok (),out,after)) :
    ∃ arg middle position, Leb128.Decoded data next arg.align middle ∧
      Leb128.Decoded data middle arg.offset position ∧
      code.check_memory_and_alignment env arg op.runtime.1 = .ok (.Ok ()) ∧
      visitor.on_simd_memory before out.core subopcode arg = .ok (.Ok (),after) ∧
      Wasm2.Simd.readFixed {st.core with pos := position} (Wasm2.Simd.fullMemoryInputs op.store)
        (Wasm2.Simd.memoryOutput op.store) = .ok (.Ok (),out.core) ∧
      out.core.ctrls = st.core.ctrls ∧ out.core.pos = position ∧
      ∃ values, Wasm2.Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals
        (Wasm2.Simd.fullMemoryInputs op.store) (Wasm2.Simd.memoryOutput op.store) values ∧
        Wasm2.ReaderPost p out.core (op.instruction (MemoryMeaning.memArg arg) (.mk_uN 0))
          p.current.ctrl.polymorphic_base values := by
  obtain ⟨capacity,run⟩ := profile_scalar_success visitor st out data env ctx index 0xfd#u8 before after (by decide) accepted
  rw [code.step_wasm2.simd,code.step_simd.eq_runs] at run
  have readLeb := reader.read_u32_leb.complete data st.core.pos subopcode next decoded
  simp only [Wasm2.Simd.prefixStep,readLeb,bind_ok] at run
  rw [Wasm2.Simd.subStep.memory visitor _ data env subopcode before op meaning full] at run
  obtain ⟨arg,read,callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ run
  rw [Wasm2.Simd.full_memory_fixed] at read
  obtain ⟨⟨reply,parsed⟩,take,values,controls,argInfo⟩ := WP.spec_imp_exists
    (code.read_memarg.spec {st.core with pos := next} data)
  dsimp only at controls values argInfo
  cases reply with
  | Err error => simp [Wasm2.Simd.fullMemoryReader,take] at read
  | Ok decodedArg =>
    simp only [Wasm2.Simd.fullMemoryReader,take,bind_ok,uncurry_apply_pair] at read
    obtain ⟨middle,alignment,offset⟩ := argInfo
    obtain ⟨result,check,checked⟩ := WP.spec_imp_exists
      (code.check_memory_and_alignment.spec env decodedArg op.runtime.1)
    rw [check] at read
    cases result with
    | Err error => simp at read
    | Ok unitValue =>
      cases unitValue
      simp only [bind_ok,core.result.Result.Insts.CoreOpsTry.branch] at read
      obtain ⟨argEq,fixed⟩ := simd_carry_success decodedArg arg parsed out.core _ _ read
      subst decodedArg
      have parsedEq : parsed = {st.core with pos := parsed.pos} := Wasm2.Simd.state_of_stacks parsed st.core values controls
      rw [parsedEq] at fixed
      have encoded : Wasm2.At data p.start (.plain (op.instruction (MemoryMeaning.memArg arg) (.mk_uN 0))) parsed.pos := by
        obtain ⟨prefixBytes,first,last,within,leb⟩ := decoded
        obtain ⟨alignBytes,af,al,ab,ae⟩ := alignment
        obtain ⟨offsetBytes,of,ol,ob,oe⟩ := offset
        exact Wasm2.At.of_immediate p.inbounds byte p.pos (.simd subopcode leb (.memory subopcode op arg meaning full ae oe))
          ((show Wasm1.BytesAt data st.core.pos prefixBytes next from ⟨first,last,within⟩).append
            ((show Wasm1.BytesAt data next alignBytes middle from ⟨af,al,ab⟩).append ⟨of,ol,ob⟩))
      refine ⟨arg,middle,parsed.pos,alignment,offset,check,callback,fixed,?_⟩
      exact Wasm2.Pending.fixed_reader_accepted p parsed.pos out.core _ _ _ capacity
        (op.wellFormed _ _ (MemoryMeaning.memArg_wf arg) (by constructor; decide)) (op.declared _ _ _)
        (fun C wf matched => by
          simpa only [op.inputs_full full,Wasm2.Simd.MemoryOperation.outputs_pop,UScalar.ofNatCore_val_eq] using
            op.typed_runtime C env ⟨locals,p.ft.results⟩ wf matched arg 0#u8 checked.1
              (by simpa [Wasm2.Simd.MemoryOperation.runtime] using checked.2) (by simp [full])) encoded fixed
end Itasca.Runtime.Compiler

end

/-! ## Reader Simd Memory Lane -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

private theorem simd_memory_lane_wf (lane : U8) : wf_uN 8 (.mk_uN lane.val) := by
  constructor
  scalar_tac

/-- Lane SIMD memory readers retain both encoded immediates, validated memory
availability and alignment, the exact callback, and the source prefix. -/
theorem reader_simd_memory_lane_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (subopcode : U32) (next : Usize) (op : Wasm2.Simd.MemoryOperation)
    (decoded : Leb128.Decoded data st.core.pos subopcode next)
    (meaning : Wasm2.Simd.memoryMeaning subopcode.val = some op) (laned : op.laneCount ≠ 0)
    (byte : data.val[p.start.val]'p.inbounds = 0xfd#u8)
    (accepted : code.step_profile visitor st data env ctx index 0xfd#u8 before =
      .ok (.Ok (),out,after)) :
    ∃ arg middle ending lane position, Leb128.Decoded data next arg.align middle ∧
      Leb128.Decoded data middle arg.offset ending ∧
      Wasm1.BytesAt data ending [lane] position ∧ lane.val < op.laneCount ∧
      code.check_memory_and_alignment env arg op.runtime.1 = .ok (.Ok ()) ∧
      visitor.on_simd_memory_lane before out.core subopcode arg lane = .ok (.Ok (),after) ∧
      Wasm2.Simd.readFixed {st.core with pos := position} [.V128, .I32]
        (Wasm2.Simd.memoryOutput op.store) = .ok (.Ok (),out.core) ∧
      out.core.ctrls = st.core.ctrls ∧ out.core.pos = position ∧
      ∃ values, Wasm2.Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals
        [.V128, .I32] (Wasm2.Simd.memoryOutput op.store) values ∧
        Wasm2.ReaderPost p out.core (op.instruction (MemoryMeaning.memArg arg) (.mk_uN lane.val))
          p.current.ctrl.polymorphic_base values := by
  obtain ⟨capacity,run⟩ := profile_scalar_success visitor st out data env ctx index 0xfd#u8 before after (by decide) accepted
  rw [code.step_wasm2.simd,code.step_simd.eq_runs] at run
  have readLeb := reader.read_u32_leb.complete data st.core.pos subopcode next decoded
  simp only [Wasm2.Simd.prefixStep,readLeb,bind_ok] at run
  rw [Wasm2.Simd.subStep.memoryLane visitor _ data env subopcode before op meaning laned] at run
  obtain ⟨⟨arg,lane⟩,read,callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ run
  rw [Wasm2.Simd.memory_lane_fixed] at read
  obtain ⟨⟨reply,parsed⟩,take,values,controls,argInfo⟩ := WP.spec_imp_exists
    (code.read_memarg.spec {st.core with pos := next} data)
  dsimp only at controls values argInfo
  cases reply with
  | Err error => simp [Wasm2.Simd.memoryLaneReader,take] at read
  | Ok decodedArg =>
    simp only [Wasm2.Simd.memoryLaneReader,take,bind_ok,uncurry_apply_pair] at read
    obtain ⟨middle,alignment,offset⟩ := argInfo
    obtain ⟨⟨laneReply,finished⟩,takeLane,laneControls,laneValues,laneInfo⟩ := WP.spec_imp_exists
      (Wasm2.Simd.take_lane_spec parsed data op.runtime.2.2)
    rw [takeLane] at read
    cases laneReply with
    | Err error => simp at read
    | Ok decodedLane =>
      simp only [bind_ok,uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch] at read
      obtain ⟨result,check,checked⟩ := WP.spec_imp_exists
        (code.check_memory_and_alignment.spec env decodedArg op.runtime.1)
      rw [check] at read
      cases result with
      | Err error => simp at read
      | Ok unitValue =>
        cases unitValue
        simp only [bind_ok,core.result.Result.Insts.CoreOpsTry.branch] at read
        obtain ⟨argEq,fixed⟩ := simd_carry_success (decodedArg,decodedLane) (arg,lane) finished out.core _ _ read
        cases argEq
        obtain ⟨laneBound,laneSpan⟩ := laneInfo lane rfl
        have laneWf : wf_uN 8 (.mk_uN lane.val) := by exact simd_memory_lane_wf lane
        have parsedEq : finished = {st.core with pos := finished.pos} := Wasm2.Simd.state_of_stacks finished st.core (laneValues.trans values) (laneControls.trans controls)
        rw [parsedEq] at fixed
        have encoded : Wasm2.At data p.start (.plain (op.instruction (MemoryMeaning.memArg arg) (.mk_uN lane.val))) finished.pos := by
          obtain ⟨prefixBytes,first,last,within,leb⟩ := decoded
          obtain ⟨alignBytes,af,al,ab,ae⟩ := alignment
          obtain ⟨offsetBytes,of,ol,ob,oe⟩ := offset
          apply Wasm2.At.of_immediate p.inbounds byte p.pos (.simd subopcode leb (.memoryLane subopcode op arg lane meaning laned ae oe))
          simpa only [List.append_assoc] using
            ((show Wasm1.BytesAt data st.core.pos prefixBytes next from ⟨first,last,within⟩).append
              ((show Wasm1.BytesAt data next alignBytes middle from ⟨af,al,ab⟩).append ((show Wasm1.BytesAt data middle offsetBytes parsed.pos from ⟨of,ol,ob⟩).append laneSpan)))
        refine ⟨arg,middle,parsed.pos,lane,finished.pos,alignment,offset,laneSpan,by simpa only [Wasm2.Simd.MemoryOperation.runtime,U8.ofNatCore_val_eq] using laneBound,check,callback,fixed,?_⟩
        exact Wasm2.Pending.fixed_reader_accepted p finished.pos out.core _ _ _ capacity
          (op.wellFormed _ _ (MemoryMeaning.memArg_wf arg) laneWf) (op.declared _ _ _)
          (fun C wf matched => by
            simpa only [op.inputs_lane laned,Wasm2.Simd.MemoryOperation.outputs_pop,UScalar.ofNatCore_val_eq] using
              op.typed_runtime C env ⟨locals,p.ft.results⟩ wf matched arg lane checked.1
                (by simpa [Wasm2.Simd.MemoryOperation.runtime] using checked.2) (fun _ => by simpa only [Wasm2.Simd.MemoryOperation.runtime,U8.ofNatCore_val_eq] using laneBound)) encoded fixed
end Itasca.Runtime.Compiler

end

end

/-! ## Dispatch -/

section

/-!
Complete SIMD event cases and their dispatch lift, composing the operation-family reader facts.
-/

/-! ## Reader Simd Events -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

def simdCompilerOpcode (sub : U32) : U16 := ⟨BitVec.ofNat 16 (512 + sub.val)⟩
theorem simd_compiler_opcode_val (sub : U32) (bound : sub.val < 256) :
    (simdCompilerOpcode sub).val = 512 + sub.val := by
  change (512 + sub.val) % 2 ^ 16 = 512 + sub.val
  apply Nat.mod_eq_of_lt
  omega

section
variable {data env locals index st} (p : Wasm2.Pending data env locals index st) {A : Type}
  (ops : runtime.platform.Alloc A) (before after : runtime.compiler.FunctionCompiler A)
  (out : code.BodyState) (ctx : code.Context) (C : context)
  (sub : U32) (next : Usize) (decoded : Leb128.Decoded data st.core.pos sub next)
  (byte : data.val[p.start.val]'p.inbounds = 0xfd#u8)
  (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    st data env ctx index 0xfd#u8 before = .ok (.Ok (),out,after))
include decoded byte accepted

theorem simd_reader_event_pure (op : Wasm2.Simd.Operation)
    (meaning : Wasm2.Simd.pureMeaning sub.val = some op) :
    Nonempty (SimdReaderEvent ops p before after out.core C) := by
  obtain ⟨capacity,_⟩ := simd_prefix_success (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    st out data env ctx index before after accepted
  obtain ⟨callback,read,controls,position,values,effect,post⟩ := reader_simd_pure_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx sub next op decoded meaning byte accepted
  have bound := Wasm2.Simd.pure_bound meaning
  rw [compiler_simd_callback ops before out.core sub (simdCompilerOpcode sub) bound (simd_compiler_opcode_val sub bound)] at callback
  have retained : SimdImmediateMeaning C sub (simdImmediate sub 0#u32 0#u128)
      (Wasm2.Simd.inputTypes op.signature.popTypes) op.instruction (Wasm2.Simd.outputTypes (some op.signature.output)) := by
    simpa only [Wasm2.Simd.Signature.inputs_pop,Wasm2.Simd.Signature.outputs_pop] using
      (SimdImmediateMeaning.pure sub (simdImmediate sub 0#u32 0#u128) op meaning : SimdImmediateMeaning C _ _ _ _ _)
  exact ⟨{
    source:=op.instruction,inputs:=op.signature.popTypes,output:=some op.signature.output,
    sub:=sub,a:=0#u32,b:=0#u32,bits:=0#u128,opcode:=simdCompilerOpcode sub,
    number:=simd_compiler_opcode_val sub bound,meaning:=.instruction retained,
    values:=values,position:=next,post:=post,effect:=effect,read:=read,callback:=callback,capacity:=capacity}⟩

theorem simd_reader_event_lane (op : Wasm2.Simd.LaneOperation)
    (meaning : Wasm2.Simd.laneMeaning sub.val = some op) :
    Nonempty (SimdReaderEvent ops p before after out.core C) := by
  obtain ⟨capacity,_⟩ := simd_prefix_success (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    st out data env ctx index before after accepted
  obtain ⟨lane,position,laneBound,span,callback,read,controls,cursor,values,effect,post⟩ := reader_simd_lane_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx sub next op decoded meaning byte accepted
  have retained := simd_lane_callback_meaning C sub op lane meaning
  have bound := retained.opcode_bound
  rw [compiler_simd_lane_callback ops before out.core sub (simdCompilerOpcode sub) bound (simd_compiler_opcode_val sub bound) lane] at callback
  have normalized : SimdImmediateMeaning C sub (simdImmediate sub (UScalar.cast .U32 lane) 0#u128)
      (Wasm2.Simd.inputTypes (Wasm2.Simd.laneInputs op.runtime.1 op.replace)) (op.instruction (.mk_uN lane.val))
      (Wasm2.Simd.outputTypes (Wasm2.Simd.laneOutput op.runtime.1 op.replace)) := by
    simpa only [Wasm2.Simd.LaneOperation.inputs_pop,Wasm2.Simd.LaneOperation.outputs_pop] using retained
  exact ⟨{
    source:=_,inputs:=_,output:=_,sub:=sub,a:=UScalar.cast .U32 lane,b:=0#u32,bits:=0#u128,
    opcode:=simdCompilerOpcode sub,number:=simd_compiler_opcode_val sub bound,meaning:=.instruction normalized,
    values:=values,position:=position,post:=post,effect:=effect,read:=read,callback:=callback,capacity:=capacity}⟩

theorem simd_reader_event_memory (op : Wasm2.Simd.MemoryOperation)
    (meaning : Wasm2.Simd.memoryMeaning sub.val = some op)
    (full : op.laneCount = 0)
    (contextMemories : C.MEMS = env.mem_types.val.map EnvTranslation.memType) :
    Nonempty (SimdReaderEvent ops p before after out.core C) := by
  obtain ⟨capacity,_⟩ := simd_prefix_success (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    st out data env ctx index before after accepted
  obtain ⟨arg,middle,position,alignment,offset,checked,callback,read,controls,cursor,values,effect,post⟩ := reader_simd_memory_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx sub next op decoded meaning full byte accepted
  obtain ⟨memory,available⟩ := memory_reader_available env arg _ C contextMemories checked
  have retained := simd_memory_callback_meaning C sub op arg memory meaning full available
  have bound := retained.opcode_bound
  let opcode := simdCompilerOpcode sub
  have number := simd_compiler_opcode_val sub bound
  have nonconstant := retained.not_constant
  rw [compiler_simd_memory_callback ops before out.core sub opcode bound number arg] at callback
  have normalized : SimdImmediateMeaning C sub (simdImmediate sub arg.offset 0#u128)
      (Wasm2.Simd.inputTypes (Wasm2.Simd.fullMemoryInputs op.store)) (op.instruction (MemoryMeaning.memArg arg) (.mk_uN 0))
      (Wasm2.Simd.outputTypes (Wasm2.Simd.memoryOutput op.store)) := by
    simpa only [op.inputs_full full,Wasm2.Simd.MemoryOperation.outputs_pop] using retained
  exact ⟨{
    source:=_,inputs:=_,output:=_,sub:=sub,a:=arg.offset,b:=arg.align,bits:=0#u128,
    opcode:=opcode,number:=number,meaning:=.instruction normalized,
    values:=values,position:=position,post:=post,effect:=effect,read:=read,callback:=callback,capacity:=capacity}⟩

theorem simd_reader_event_memory_lane (op : Wasm2.Simd.MemoryOperation)
    (meaning : Wasm2.Simd.memoryMeaning sub.val = some op)
    (laned : op.laneCount ≠ 0)
    (contextMemories : C.MEMS = env.mem_types.val.map EnvTranslation.memType) :
    Nonempty (SimdReaderEvent ops p before after out.core C) := by
  obtain ⟨capacity,_⟩ := simd_prefix_success (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    st out data env ctx index before after accepted
  obtain ⟨arg,middle,ending,lane,position,alignment,offset,span,laneBound,checked,callback,read,controls,cursor,values,effect,post⟩ := reader_simd_memory_lane_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx sub next op decoded meaning laned byte accepted
  obtain ⟨memory,available⟩ := memory_reader_available env arg _ C contextMemories checked
  have retained := simd_memory_lane_callback_meaning C sub op arg lane memory meaning laned available
  have bound := retained.opcode_bound
  let opcode := simdCompilerOpcode sub
  have number := simd_compiler_opcode_val sub bound
  have nonconstant := retained.not_constant
  rw [compiler_simd_memory_lane_callback ops before out.core sub opcode bound number arg lane] at callback
  have normalized : SimdImmediateMeaning C sub (simdImmediate sub arg.offset (UScalar.cast .U128 lane))
      (Wasm2.Simd.inputTypes ([.V128,.I32])) (op.instruction (MemoryMeaning.memArg arg) (.mk_uN lane.val))
      (Wasm2.Simd.outputTypes (Wasm2.Simd.memoryOutput op.store)) := by
    simpa only [op.inputs_lane laned,Wasm2.Simd.MemoryOperation.outputs_pop] using retained
  exact ⟨{
    source:=_,inputs:=_,output:=_,sub:=sub,a:=arg.offset,b:=arg.align,bits:=UScalar.cast .U128 lane,
    opcode:=opcode,number:=number,meaning:=.instruction normalized,
    values:=values,position:=position,post:=post,effect:=effect,read:=read,callback:=callback,capacity:=capacity}⟩

theorem simd_reader_event_constant (constant : sub = 12#u32) :
    Nonempty (SimdReaderEvent ops p before after out.core C) := by
  subst sub
  obtain ⟨capacity,_⟩ := simd_prefix_success (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    st out data env ctx index before after accepted
  obtain ⟨low,high,position,bits,callback,read,controls,cursor,values,effect,post⟩ := reader_simd_constant_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx next decoded byte accepted
  rw [compiler_simd_constant_callback ops before out.core low high] at callback
  have normalized : Wasm2.ReaderPost p out.core (.VCONST .V128 (.mk_uN (initializerBits low high).val))
      p.current.ctrl.polymorphic_base values := by
    simpa only [initializer_bits_val,Wasm2.Simd.vectorConstant] using post
  exact ⟨{
    source:=_,inputs:=[],output:=some .V128,sub:=12#u32,a:=0#u32,b:=0#u32,bits:=initializerBits low high,
    opcode:=524#u16,number:=rfl,meaning:=.constant _ _,values:=values,position:=position,
    post:=normalized,effect:=effect,read:=read,callback:=callback,capacity:=capacity}⟩

theorem simd_reader_event_shuffle (shuffle : sub = 13#u32) :
    Nonempty (SimdReaderEvent ops p before after out.core C) := by
  subst sub
  obtain ⟨capacity,_⟩ := simd_prefix_success (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    st out data env ctx index before after accepted
  obtain ⟨low,high,bits,bounds,callback,read,controls,values,effect,post⟩ := reader_simd_shuffle_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx next decoded byte accepted
  rw [compiler_simd_shuffle_callback ops before out.core low high] at callback
  obtain ⟨sourceContext,outer,spine,header,base,prior,ctrls,blocks,stack⟩ := p.opened
  have physicalBase : (Control.base {st.core with pos := next}).val = outer.length := by
    simp [Control.base,ctrls,base]
  obtain ⟨prefixBytes,first,last,within,leb⟩ := decoded
  have fixed := simd_shuffle_fixed {st.core with pos := next} out.core data outer p.current.vals stack physicalBase capacity within low high read
  have retained : SimdImmediateMeaning C 13#u32 (simdImmediate 13#u32 0#u32 (initializerBits low high))
      (Wasm2.Simd.inputTypes [.V128,.V128]) (Wasm2.Simd.shuffle low high) (Wasm2.Simd.outputTypes (some .V128)) :=
    simd_shuffle_callback_meaning C low high
  exact ⟨{
    source:=_,inputs:=[.V128,.V128],output:=some .V128,sub:=13#u32,a:=0#u32,b:=0#u32,
    bits:=initializerBits low high,opcode:=525#u16,number:=rfl,meaning:=.instruction retained,
    values:=values,position:=out.core.pos,post:=post,effect:=effect,read:=fixed,callback:=callback,capacity:=capacity}⟩
end
end Itasca.Runtime.Compiler

end

/-! ## Reader Simd Event Dispatch -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Every accepted SIMD-prefixed reader is one of the independently classified
families and retains a complete canonical reader/callback witness. -/
theorem reader_simd_event_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (before after : runtime.compiler.FunctionCompiler A)
    (out : code.BodyState) (ctx : code.Context) (C : context)
    (contextMemories : C.MEMS = env.mem_types.val.map EnvTranslation.memType)
    (byte : data.val[p.start.val]'p.inbounds = 0xfd#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 0xfd#u8 before = .ok (.Ok (),out,after)) :
    Nonempty (SimdReaderEvent ops p before after out.core C) := by
  obtain ⟨capacity,sub,next,decoded,called⟩ := simd_prefix_success
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx index before after accepted
  cases pure : Wasm2.Simd.pureMeaning sub.val with
  | some op => exact simd_reader_event_pure p ops before after out ctx C sub next decoded byte accepted op pure
  | none =>
    cases lane : Wasm2.Simd.laneMeaning sub.val with
    | some op => exact simd_reader_event_lane p ops before after out ctx C sub next decoded byte accepted op lane
    | none =>
      cases memory : Wasm2.Simd.memoryMeaning sub.val with
      | some op =>
        by_cases full : op.laneCount = 0
        · exact simd_reader_event_memory p ops before after out ctx C sub next decoded byte accepted op memory full contextMemories
        · exact simd_reader_event_memory_lane p ops before after out ctx C sub next decoded byte accepted op memory full contextMemories
      | none =>
        simp only [Wasm2.Simd.subStep,Wasm2.Simd.pure_table,pure,Wasm2.Simd.lane_table,lane,
          Wasm2.Simd.memory_table,memory,Option.map_none,bind_ok] at called
        split at called
        · exact simd_reader_event_constant p ops before after out ctx C 12#u32 next decoded byte accepted rfl
        · exact simd_reader_event_shuffle p ops before after out ctx C 13#u32 next decoded byte accepted rfl
        · simp at called
end Itasca.Runtime.Compiler

end

end
