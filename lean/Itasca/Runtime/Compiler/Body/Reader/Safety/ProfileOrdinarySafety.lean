import Itasca.Runtime.Compiler.Body.Reader.Safety.OrdinarySafety
import Itasca.Runtime.Compiler.Body.Reader.Replay.ProfileSafety
import Itasca.Runtime.Compiler.Body.Reader.Calls.Safety

/-!
Normal return of profile-filtered ordinary reader steps.

Main declarations: `compiler_reader_profile_wasm2_ordinary_total`. A direct consumer is `Compiler.Body.Reader.Replay.ReachedSafety`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem compiler_reader_profile_wasm2_ordinary_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (index : U32) (opcode : U8)
    (ready : OrdinaryCallbackReady compiler env ctx st.core.vals.val)
    (shape : Control.Shape st.core)
    (ordinary : opcode.val ∉ [2,3,4,5,11,12,13,14,15]) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 opcode compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.core.vals.val ⦄ := by
  by_cases call : opcode = 16#u8
  · subst opcode
    exact compiler_reader_call_wasm2_total ops law compiler st data env ctx index ready shape
  by_cases indirect : opcode = 17#u8
  · subst opcode
    exact compiler_reader_call_indirect_wasm2_total ops law compiler st data env ctx index ready shape
  have scalar : opcode.val ∉ Wasm2.controlOpcodes := by
    simp only [Wasm2.controlOpcodes,List.mem_cons,List.not_mem_nil,or_false,not_or] at ordinary ⊢
    have callNe : opcode.val ≠ 16 := fun h => call (UScalar.eq_of_val_eq h)
    have indirectNe : opcode.val ≠ 17 := fun h => indirect (UScalar.eq_of_val_eq h)
    tauto
  apply reader_profile_scalar_reached _ st data env ctx index opcode compiler
    (fun state after => ObservedStack after state.vals.val) scalar
  intro capacity
  exact compiler_reader_wasm2_total ops law compiler st.core data env ctx ready shape capacity opcode scalar
end Itasca.Runtime.Compiler
