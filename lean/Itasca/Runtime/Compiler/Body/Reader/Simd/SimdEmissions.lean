import Itasca.Wasm2.Simd.Sound
import Itasca.Runtime.Compiler.Body.Reader.Replay.Post
import Itasca.Runtime.Compiler.Body.Reader.Replay.BulkAndSaturatingAcceptance
import Itasca.Runtime.Compiler.Local.Capacity.SimdAuxiliaryGrowth
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdEffects
import Itasca.Runtime.Compiler.Body.Relations.Stacks.KnownFixedStack
import Itasca.Runtime.Compiler.Body.Reader.Stacks.Values
import Itasca.Runtime.Compiler.Body.Source.TypedLowering

/-!
Sections, each formerly its own module: SimdPure, SimdLane, SimdConstant, Shuffle, SimdMeaning, SimdTypes, SimdEmissions.
-/

/-! ## SimdPure -/

section

/-!
Accepted SIMD prefix decoding retains the exact unsigned LEB and the selected independent subopcode dispatch.

Main declarations: `simd_prefix_success` and `reader_simd_pure_wasm2`. A direct consumer is `Compiler.Body.Reader.Simd.SimdLane`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Accepted SIMD prefix decoding retains the exact unsigned LEB and the
selected independent subopcode dispatch. -/
theorem simd_prefix_success {V : Type} (visitor : code.OpVisitor V)
    (st out : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (index : U32) (before after : V)
    (accepted : code.step_profile visitor st data env ctx index 0xfd#u8 before =
      .ok (.Ok (),out,after)) :
    st.core.vals.val.length < Usize.max ∧ ∃ subopcode next,
      Leb128.Decoded data st.core.pos subopcode next ∧
      Wasm2.Simd.subStep visitor {st.core with pos := next} data env subopcode before =
        .ok (.Ok (),out.core,after) := by
  obtain ⟨capacity,run⟩ := profile_scalar_success visitor st out data env ctx index 0xfd#u8 before after
    (by decide) accepted
  rw [code.step_wasm2.simd,code.step_simd.eq_runs] at run
  obtain ⟨result,read,decoded⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.core.pos)
  cases result with
  | Err error => simp [Wasm2.Simd.prefixStep,read] at run
  | Ok pair =>
    obtain ⟨subopcode,next⟩ := pair
    simp only [Wasm2.Simd.prefixStep,read,bind_ok] at run
    exact ⟨capacity,subopcode,next,decoded,run⟩

/-- Pure SIMD readers retain the exact supplied source prefix and callback. -/
theorem reader_simd_pure_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (subopcode : U32) (next : Usize) (op : Wasm2.Simd.Operation)
    (decoded : Leb128.Decoded data st.core.pos subopcode next)
    (meaning : Wasm2.Simd.pureMeaning subopcode.val = some op)
    (byte : data.val[p.start.val]'p.inbounds = 0xfd#u8)
    (accepted : code.step_profile visitor st data env ctx index 0xfd#u8 before =
      .ok (.Ok (),out,after)) :
    visitor.on_simd before out.core subopcode = .ok (.Ok (),after) ∧
      Wasm2.Simd.readFixed {st.core with pos := next} op.signature.popTypes (some op.signature.output) =
        .ok (.Ok (),out.core) ∧
      out.core.ctrls = st.core.ctrls ∧ out.core.pos = next ∧
      ∃ values, Wasm2.Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals
        op.signature.popTypes (some op.signature.output) values ∧
        Wasm2.ReaderPost p out.core op.instruction p.current.ctrl.polymorphic_base values := by
  obtain ⟨capacity,run⟩ := profile_scalar_success visitor st out data env ctx index 0xfd#u8 before after
    (by decide) accepted
  rw [code.step_wasm2.simd,code.step_simd.eq_runs] at run
  have readLeb := reader.read_u32_leb.complete data st.core.pos subopcode next decoded
  simp only [Wasm2.Simd.prefixStep,readLeb,bind_ok] at run
  rw [Wasm2.Simd.subStep.pure visitor _ data env subopcode before op meaning] at run
  obtain ⟨unitValue,read,callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ run
  cases unitValue
  rw [Wasm2.Simd.signature_fixed] at read
  have encoded : Wasm2.At data p.start (.plain op.instruction) next := by
    obtain ⟨bytes,first,last,within,leb⟩ := decoded
    apply Wasm2.At.of_immediate p.inbounds byte p.pos (.simd subopcode leb (.pure subopcode op meaning))
    simpa only [List.append_nil] using
      (show Wasm1.BytesAt data st.core.pos bytes next from ⟨first,last,within⟩).append
        (Wasm1.BytesAt.nil data next within)
  refine ⟨callback,read,?_⟩
  exact Wasm2.Pending.fixed_reader_accepted p next out.core op.signature.popTypes (some op.signature.output)
    op.instruction capacity op.wellFormed (op.declared _)
    (fun C wf _ => by simpa only [Wasm2.Simd.Signature.inputs_pop,Wasm2.Simd.Signature.outputs_pop]
        using op.typed C wf) encoded read

end Itasca.Runtime.Compiler

end

/-! ## SimdLane -/

section

/-!
A successful fixed checker returns exactly its already decoded payload.

Main declarations: `simd_carry_success` and `reader_simd_lane_wasm2`. A direct consumer is `Compiler.Body.Reader.References.TypedSelect`.
-/

namespace Itasca.Runtime.Compiler
set_option maxRecDepth 4096
open Aeneas Aeneas.Std Itasca Itasca.ResultFacts

private theorem simd_lane_wf (lane : U8) : wf_uN 8 (.mk_uN lane.val) := by
  constructor
  scalar_tac

/-- A successful fixed checker returns exactly its already decoded payload. -/
theorem simd_carry_success {A : Type} (value result : A) (st out : code.OpIterState)
    (inputs : List wasm_types.ValueType) (output : Option wasm_types.ValueType)
    (accepted : Wasm2.Simd.carryFixed value st inputs output = .ok (.Ok result,out)) :
    value = result ∧ Wasm2.Simd.readFixed st inputs output = .ok (.Ok (),out) := by
  unfold Wasm2.Simd.carryFixed at accepted
  obtain ⟨⟨reply,after⟩,read,tail⟩ := bind_ok_inv _ _ _ accepted
  cases reply with
  | Err error => simp [uncurry_apply_pair] at tail
  | Ok unitValue =>
    cases unitValue
    simp only [uncurry_apply_pair,Result.ok.injEq,Prod.mk.injEq,core.result.Result.Ok.injEq] at tail
    obtain ⟨rfl,rfl⟩ := tail
    exact ⟨rfl,read⟩

/-- Accepted SIMD lane readers retain the literal lane, its bound, the exact
callback, and the source zipper after the fixed operand check. -/
theorem reader_simd_lane_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (subopcode : U32) (next : Usize) (op : Wasm2.Simd.LaneOperation)
    (decoded : Leb128.Decoded data st.core.pos subopcode next)
    (meaning : Wasm2.Simd.laneMeaning subopcode.val = some op)
    (byte : data.val[p.start.val]'p.inbounds = 0xfd#u8)
    (accepted : code.step_profile visitor st data env ctx index 0xfd#u8 before =
      .ok (.Ok (),out,after)) :
    ∃ lane position, lane.val < op.count ∧ Wasm1.BytesAt data next [lane] position ∧
      visitor.on_simd_lane before out.core subopcode lane = .ok (.Ok (),after) ∧
      Wasm2.Simd.readFixed {st.core with pos := position}
        (Wasm2.Simd.laneInputs op.runtime.1 op.replace) (Wasm2.Simd.laneOutput op.runtime.1 op.replace) = .ok (.Ok (),out.core) ∧
      out.core.ctrls = st.core.ctrls ∧ out.core.pos = position ∧
      ∃ values, Wasm2.Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals
        (Wasm2.Simd.laneInputs op.runtime.1 op.replace) (Wasm2.Simd.laneOutput op.runtime.1 op.replace) values ∧
        Wasm2.ReaderPost p out.core (op.instruction (.mk_uN lane.val)) p.current.ctrl.polymorphic_base values := by
  obtain ⟨capacity,run⟩ := profile_scalar_success visitor st out data env ctx index 0xfd#u8 before after (by decide) accepted
  rw [code.step_wasm2.simd,code.step_simd.eq_runs] at run
  have readLeb := reader.read_u32_leb.complete data st.core.pos subopcode next decoded
  simp only [Wasm2.Simd.prefixStep,readLeb,bind_ok] at run
  rw [Wasm2.Simd.subStep.lane visitor _ data env subopcode before op meaning] at run
  obtain ⟨lane,read,callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ run
  rw [Wasm2.Simd.lane_fixed] at read
  obtain ⟨⟨reply,middle⟩,take,controls,values,laneInfo⟩ := WP.spec_imp_exists
    (Wasm2.Simd.take_lane_spec {st.core with pos := next} data op.runtime.2.1)
  dsimp only at controls values laneInfo
  cases reply with
  | Err error => simp [Wasm2.Simd.laneReader,take] at read
  | Ok value =>
    simp only [Wasm2.Simd.laneReader,take,bind_ok,uncurry_apply_pair] at read
    obtain ⟨valueEq,fixed⟩ := simd_carry_success value lane middle out.core _ _ read
    subst value
    obtain ⟨laneBound,span⟩ := laneInfo lane rfl
    have middleEq : middle = {st.core with pos := middle.pos} := Wasm2.Simd.state_of_stacks middle st.core values controls
    rw [middleEq] at fixed
    have bound : lane.val < op.count := by simpa only [Wasm2.Simd.LaneOperation.runtime,U8.ofNatCore_val_eq] using laneBound
    have laneWf := simd_lane_wf lane
    have encoded : Wasm2.At data p.start (.plain (op.instruction (.mk_uN lane.val))) middle.pos := by
      obtain ⟨bytes,first,last,within,leb⟩ := decoded
      exact Wasm2.At.of_immediate p.inbounds byte p.pos (.simd subopcode leb (.lane subopcode op lane meaning))
        ((show Wasm1.BytesAt data st.core.pos bytes next from ⟨first,last,within⟩).append span)
    refine ⟨lane,middle.pos,bound,span,callback,fixed,?_⟩
    exact Wasm2.Pending.fixed_reader_accepted p middle.pos out.core _ _ (op.instruction (.mk_uN lane.val))
      capacity (op.wellFormed _ laneWf) (op.declared _ _)
      (fun C wf _ => by simpa only [Wasm2.Simd.LaneOperation.inputs_pop,Wasm2.Simd.LaneOperation.outputs_pop]
          using op.typed C (.mk_uN lane.val) wf laneWf bound) encoded fixed

end Itasca.Runtime.Compiler

end

/-! ## SimdConstant -/

section

/-!
An accepted vector constant retains all sixteen encoded bytes, its exact compiler callback, and the complete independently typed source prefix.

Main declarations: `reader_simd_constant_wasm2`. A direct consumer is `Compiler.Body.Reader.Simd.Dispatch`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- An accepted vector constant retains all sixteen encoded bytes, its exact
compiler callback, and the complete independently typed source prefix. -/
theorem reader_simd_constant_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (next : Usize) (decoded : Leb128.Decoded data st.core.pos 12#u32 next)
    (byte : data.val[p.start.val]'p.inbounds = 0xfd#u8)
    (accepted : code.step_profile visitor st data env ctx index 0xfd#u8 before =
      .ok (.Ok (),out,after)) :
    ∃ low high position, Wasm2.Simd.BitsDecoded data next low high position ∧
      visitor.on_simd_const before out.core low high = .ok (.Ok (),after) ∧
      Wasm2.Simd.readFixed {st.core with pos := position} [] (some .V128) = .ok (.Ok (),out.core) ∧
      out.core.ctrls = st.core.ctrls ∧ out.core.pos = position ∧
      ∃ values, Wasm2.Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals [] (some .V128) values ∧
        Wasm2.ReaderPost p out.core (Wasm2.Simd.vectorConstant low high) p.current.ctrl.polymorphic_base values := by
  obtain ⟨capacity,run⟩ := profile_scalar_success visitor st out data env ctx index 0xfd#u8 before after (by decide) accepted
  rw [code.step_wasm2.simd,code.step_simd.eq_runs] at run
  have readLeb := reader.read_u32_leb.complete data st.core.pos 12#u32 next decoded
  simp only [Wasm2.Simd.prefixStep,readLeb,bind_ok] at run
  rw [Wasm2.Simd.subStep.constant] at run
  obtain ⟨⟨low,high⟩,read,callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ run
  rw [Wasm2.Simd.const_fixed] at read
  obtain ⟨⟨reply,middle⟩,take,controls,values,bits⟩ := WP.spec_imp_exists
    (Wasm2.Simd.take_bits_spec {st.core with pos := next} data)
  dsimp only at controls values bits
  cases reply with
  | Err error => simp [Wasm2.Simd.constReader,take] at read
  | Ok pair =>
    simp only [Wasm2.Simd.constReader,take,bind_ok,uncurry_apply_pair] at read
    obtain ⟨pairEq,fixed⟩ := simd_carry_success pair (low,high) middle out.core _ _ read
    subst pair
    have bitSpan := bits low high rfl
    have middleEq : middle = {st.core with pos := middle.pos} := Wasm2.Simd.state_of_stacks middle st.core values controls
    rw [middleEq] at fixed
    have encoded : Wasm2.At data p.start (.plain (Wasm2.Simd.vectorConstant low high)) middle.pos := by
      obtain ⟨prefixBytes,first,last,within,leb⟩ := decoded
      obtain ⟨lower,upper,lo,hi,span⟩ := bitSpan
      exact Wasm2.At.of_immediate p.inbounds byte p.pos (.simd 12#u32 leb (.constant low high lo hi))
        ((show Wasm1.BytesAt data st.core.pos prefixBytes next from ⟨first,last,within⟩).append span)
    refine ⟨low,high,middle.pos,bitSpan,callback,fixed,?_⟩
    exact Wasm2.Pending.fixed_reader_accepted p middle.pos out.core [] (some .V128) _ capacity
      (Wasm2.Simd.vectorConstant_wf low high) (Wasm2.Simd.vectorConstant_declared _ low high)
      (fun C wf _ => Wasm2.Simd.vectorConstant_typed C low high wf) encoded fixed
end Itasca.Runtime.Compiler

end

/-! ## Shuffle -/

section

/-!
SIMD shuffle reader decoding and fixed-instruction characterization, used by SIMD callback replay.
-/

/-! ## Reader Simd Shuffle -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Shuffle validation retains its checked lane vector, exact source bytes,
compiler callback, and polymorphic operand effect. -/
theorem reader_simd_shuffle_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (next : Usize) (decoded : Leb128.Decoded data st.core.pos 13#u32 next)
    (byte : data.val[p.start.val]'p.inbounds = 0xfd#u8)
    (accepted : code.step_profile visitor st data env ctx index 0xfd#u8 before =
      .ok (.Ok (),out,after)) :
    ∃ low high, Wasm2.Simd.BitsDecoded data next low high out.core.pos ∧
      (∀ lane ∈ Wasm2.Simd.shuffleIndices low high, proj_uN_0 lane < 32) ∧
      visitor.on_simd_shuffle before out.core low high = .ok (.Ok (),after) ∧
      code.read_simd_shuffle {st.core with pos := next} data = .ok (.Ok (low,high),out.core) ∧
      out.core.ctrls = st.core.ctrls ∧
      ∃ values, Wasm2.Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals [.V128,.V128] (some .V128) values ∧
        Wasm2.ReaderPost p out.core (Wasm2.Simd.shuffle low high) p.current.ctrl.polymorphic_base values := by
  obtain ⟨capacity,run⟩ := profile_scalar_success visitor st out data env ctx index 0xfd#u8 before after (by decide) accepted
  rw [code.step_wasm2.simd,code.step_simd.eq_runs] at run
  have readLeb := reader.read_u32_leb.complete data st.core.pos 13#u32 next decoded
  simp only [Wasm2.Simd.prefixStep,readLeb,bind_ok] at run
  rw [Wasm2.Simd.subStep.shuffle] at run
  obtain ⟨⟨low,high⟩,read,callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ run
  have within : next.val ≤ data.length := by
    obtain ⟨_, _, _, bound, _⟩ := decoded
    exact bound
  have effect := p.shuffle_reader next within capacity (by
    intro low high position bits
    obtain ⟨prefixBytes, first, last, within, leb⟩ := decoded
    obtain ⟨lower, upper, lo, hi, span⟩ := bits
    exact Wasm2.At.of_immediate p.inbounds byte p.pos (.simd 13#u32 leb (.shuffle low high lo hi))
      ((show Wasm1.BytesAt data st.core.pos prefixBytes next from ⟨first, last, within⟩).append span))
  rw [read, WP.spec_ok] at effect
  obtain ⟨bits, bounds, controls, values, operands, post⟩ := effect low high rfl
  exact ⟨low, high, bits, bounds, callback, read, controls, values, operands, post⟩
end Itasca.Runtime.Compiler

end

/-! ## Reader Simd Shuffle Fixed -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- The checked shuffle scan is followed by the same fixed operand reader as
the other SIMD families, at the exact final cursor. -/
theorem simd_shuffle_fixed (st out : code.OpIterState) (data : Slice U8)
    (outer segment : List code.StackType) (values : st.vals.val = outer ++ segment)
    (base : (Control.base st).val = outer.length) (capacity : st.vals.val.length < Usize.max)
    (position : st.pos.val ≤ data.length) (low high : U64)
    (accepted : code.read_simd_shuffle st data = .ok (.Ok (low,high),out)) :
    Wasm2.Simd.readFixed {st with pos := out.pos} [.V128,.V128] (some .V128) = .ok (.Ok (),out) := by
  have spec : code.read_simd_shuffle st data ⦃ r => ∀ lo hi, r.1 = .Ok (lo,hi) →
      Wasm2.Simd.readFixed {st with pos := r.2.pos} [.V128,.V128] (some .V128) = .ok (.Ok (),r.2) ⦄ := by
    apply Wasm2.Simd.shuffle_scan st data position
    · intro e; simp
    · intro bytes next span length bounds
      obtain ⟨⟨reply,parsed⟩,take,controls,vals,bits⟩ := WP.spec_imp_exists (Wasm2.Simd.take_bits_spec st data)
      dsimp only at controls vals
      simp only [Wasm2.Simd.shuffleFinish,take,bind_ok,uncurry_apply_pair]
      cases reply with
      | Err error => simp
      | Ok pair =>
        obtain ⟨⟨result,after⟩,read,readControls,cursor,effect⟩ := WP.spec_imp_exists
          (Wasm2.Simd.readFixed.segment parsed [.V128,.V128] (some .V128) outer segment
            (by simpa only [vals] using values) (by simpa only [Control.base,controls] using base)
            (by simpa only [vals] using capacity))
        dsimp only at cursor
        simp only [Wasm2.Simd.carryFixed,read,bind_ok,uncurry_apply_pair]
        cases result with
        | Err error => simp
        | Ok unitValue =>
          cases unitValue
          simp only [WP.spec_ok]
          intro lo hi success
          have parsedEq : parsed = {st with pos := after.pos} := by
            rw [cursor]
            exact Wasm2.Simd.state_of_stacks parsed st vals controls
          simpa only [parsedEq] using read
  rw [accepted,WP.spec_ok] at spec
  exact spec low high rfl
end Itasca.Runtime.Compiler

end

end

/-! ## SimdMeaning -/

section

/-!
Ordinary lane callbacks encode the checked lane index in the first scalar immediate, outside the separate memory-lane opcode range.

Main declarations: `simd_lane_callback_meaning` and `SimdImmediateMeaning.not_constant`. A direct consumer is `Compiler.Body.Reader.Simd.Dispatch`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Wasm2.Simd

/-- Ordinary lane callbacks encode the checked lane index in the first scalar
immediate, outside the separate memory-lane opcode range. -/
theorem simd_lane_callback_meaning (C : context) (sub : U32) (op : LaneOperation) (lane : U8)
    (meaning : laneMeaning sub.val = some op) :
    SimdImmediateMeaning C sub (simdImmediate sub (UScalar.cast .U32 lane) 0#u128)
      op.inputs (op.instruction (.mk_uN lane.val)) op.outputs := by
  have small : sub.val < 84 := by
    unfold laneMeaning at meaning
    split at meaning <;> first | contradiction | omega
  apply SimdImmediateMeaning.lane sub _ op meaning lane
  have outside : ¬ 84#u32 ≤ sub := by scalar_tac
  simp only [simdImmediate,simdLane,if_neg outside,UScalar.cast_val_eq]
  exact Nat.mod_eq_of_lt (by scalar_tac)

theorem simd_memory_callback_meaning (C : context) (sub : U32) (op : MemoryOperation)
    (arg : code.MemArg) (memory : memtype)
    (meaning : memoryMeaning sub.val = some op) (full : op.laneCount = 0)
    (available : C.MEMS[0]? = some memory) :
    SimdImmediateMeaning C sub (simdImmediate sub arg.offset 0#u128)
      op.inputs (op.instruction (MemoryMeaning.memArg arg) (.mk_uN 0)) op.outputs := by
  apply SimdImmediateMeaning.memory sub _ op meaning (MemoryMeaning.memArg arg) 0#u8 memory available rfl
  simp only [full,ne_eq,not_true_eq_false,false_implies]

theorem simd_memory_lane_callback_meaning (C : context) (sub : U32) (op : MemoryOperation)
    (arg : code.MemArg) (lane : U8) (memory : memtype)
    (meaning : memoryMeaning sub.val = some op) (laned : op.laneCount ≠ 0)
    (available : C.MEMS[0]? = some memory) :
    SimdImmediateMeaning C sub (simdImmediate sub arg.offset (UScalar.cast .U128 lane))
      op.inputs (op.instruction (MemoryMeaning.memArg arg) (.mk_uN lane.val)) op.outputs := by
  have range : 84 ≤ sub.val ∧ sub.val ≤ 91 := by
    unfold memoryMeaning at meaning
    split at meaning <;> first | contradiction | cases meaning
    all_goals simp_all [MemoryOperation.laneCount]
  apply SimdImmediateMeaning.memory sub _ op meaning (MemoryMeaning.memArg arg) lane memory available rfl
  intro _
  have lower : 84#u32 ≤ sub := by scalar_tac
  have upper : sub ≤ 91#u32 := by scalar_tac
  simp only [simdImmediate,simdLane,if_pos lower,if_pos upper,UScalar.cast_val_eq]
  rw [Nat.mod_eq_of_lt (by scalar_tac),Nat.mod_eq_of_lt (by scalar_tac)]

theorem simd_shuffle_callback_meaning (C : context) (lo hi : U64) :
    SimdImmediateMeaning C 13#u32 (simdImmediate 13#u32 0#u32 (initializerBits lo hi))
      [.V128,.V128] (shuffle lo hi) [.V128] := by
  exact .shuffle _ lo hi (initializer_bits_val lo hi)

theorem SimdImmediateMeaning.not_constant {C sub immediate input source output}
    (meaning : SimdImmediateMeaning C sub immediate input source output) : sub.val ≠ 12 := by
  intro equal
  cases meaning with
  | pure sub immediate op meaning => rw [equal] at meaning; cases meaning
  | lane sub immediate op meaning lane position => rw [equal] at meaning; cases meaning
  | memory sub immediate op meaning arg lane memory available offset position => rw [equal] at meaning; cases meaning
  | shuffle => contradiction
end Itasca.Runtime.Compiler

end

/-! ## SimdTypes -/

section

/-!
Successful live SIMD operand checks expose exact complete source stacks; the physical reader also proves the absence of unknown stack entries.

Main declarations: `reader_simd_fixed_types`. A direct consumer is `Compiler.Body.Reader.Acceptance.SourceBoundTypedSelectAcceptance`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Successful live SIMD operand checks expose exact complete source stacks;
the physical reader also proves the absence of unknown stack entries. -/
theorem reader_simd_fixed_types {data env locals index st out source values position inputs output}
    {p : Wasm2.Pending data env locals index st}
    (post : Wasm2.ReaderPost p out source p.current.ctrl.polymorphic_base values)
    (effect : Wasm2.Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals inputs output values)
    (read : Wasm2.Simd.readFixed {st.core with pos := position} inputs output = .ok (.Ok (),out))
    (known : ConcreteStack st.core.vals.val)
    (monomorphic : p.current.ctrl.polymorphic_base = false)
    (capacity : st.core.vals.val.length < Usize.max) :
    ∃ (front : List valtype) (types : List Itasca.wasm_types.ValueType), Sequence.stackTypes st.core.vals.val = front ++ Wasm2.Simd.inputTypes inputs ∧
      out.vals.val = types.map code.StackType.Val ∧
      types.map Translate.valueType = front ++ Wasm2.Simd.outputTypes output := by
  obtain ⟨_,outer,_,_,base,_,ctrls,_,stack⟩ := p.opened
  have physicalBase : (Control.base {st.core with pos := position}).val = outer.length := by
    simp [Control.base,ctrls,base]
  have afterKnown := read_fixed_known {st.core with pos := position} out outer p.current.vals
    inputs output stack physicalBase capacity known read
  obtain ⟨old,new⟩ := post.values
  have currentKnown := (concrete_stack_append.mp (old ▸ known)).2
  rw [monomorphic] at effect
  obtain ⟨front,beforeTypes,afterTypes⟩ := fixed_effect_types currentKnown effect
  obtain ⟨types,concrete⟩ := (concrete_stack_iff out.vals.val).mp afterKnown
  refine ⟨Sequence.stackTypes (p.parents.flatMap Wasm2.Frames.Saved.vals) ++ front,
    types,?_,concrete,?_⟩
  · conv_lhs => rw [old]
    simp only [Sequence.stackTypes,List.map_append]
    change _ ++ Sequence.stackTypes p.current.vals = _
    rw [beforeTypes,List.append_assoc]
  · have decoded : Sequence.stackTypes out.vals.val =
        (Sequence.stackTypes (p.parents.flatMap Wasm2.Frames.Saved.vals) ++ front) ++ Wasm2.Simd.outputTypes output := by
      rw [new]
      simp only [Sequence.stackTypes,List.map_append]
      change _ ++ Sequence.stackTypes values = _
      rw [afterTypes,List.append_assoc]
    simpa only [concrete,Sequence.stackTypes,List.map_map,Function.comp_def] using decoded

end Itasca.Runtime.Compiler

end

/-! ## SimdEmissions -/

section

/-!
Canonical SIMD reader effects and the actual accepted callback produce exact typed emitted-code evidence, including appended metadata.

Main declarations: `reader_simd_fixed_emission`. A direct consumer is `Compiler.Body.Reader.Simd.CallbackEmission`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Canonical SIMD reader effects and the actual accepted callback produce
exact typed emitted-code evidence, including appended metadata. -/
theorem reader_simd_fixed_emission {data env locals index st source values position inputs output}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (C : context) (opcode : U16) (sub a b : U32) (bits : U128)
    (number : opcode.val = 512 + sub.val) (bounded : sub.val < 256) (nonconstant : sub.val ≠ 12)
    (meaning : SimdImmediateMeaning C sub (simdImmediate sub a bits)
      (Wasm2.Simd.inputTypes inputs) source (Wasm2.Simd.outputTypes output))
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
    after.function.simd.val = before.function.simd.val ++ [simdImmediate sub a bits] ∧
    after.function.v128_pool = before.function.v128_pool ∧
    ∃ front emitted, Sequence.stackTypes st.core.vals.val = front ++ Wasm2.Simd.inputTypes inputs ∧
      TypedLowered before after out.vals.val emitted (front ++ Wasm2.Simd.outputTypes output) ∧
      SimdEmission after.function.simd.val after.function.v128_pool.val C
        (front ++ Wasm2.Simd.inputTypes inputs) source [emitted] (front ++ Wasm2.Simd.outputTypes output) := by
  rw [lower_simd_dispatch ops before out opcode a b bits reachable (by omega) (by omega)] at accepted
  have ordinary := compiler_simd_ordinary_result ops law before after out opcode a bits (.Ok ()) accepted
  have sources := compiler_simd_sources ops law before after out opcode a bits accepted
  have cursor := compiler_simd_cursor ops law before after out opcode a bits accepted
  obtain ⟨front,types,oldTypes,concrete,newTypes⟩ := reader_simd_fixed_types post effect read known monomorphic capacity
  rw [oldTypes] at layout
  obtain ⟨simd,pool,emitted,lowered,emission⟩ := compiler_simd_emission ops law before after out types C front _ _ source
    opcode sub a bits number bounded nonconstant meaning contextLocals layout concrete newTypes
    codeFits sourceFits coordinateFits accepted
  exact ⟨ordinary,sources,cursor,simd,pool,front,emitted,oldTypes,
    ⟨lowered,SourceStack.of_map types concrete newTypes⟩,emission⟩
end Itasca.Runtime.Compiler

end
