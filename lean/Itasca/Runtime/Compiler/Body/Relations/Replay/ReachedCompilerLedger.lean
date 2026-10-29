import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CallbackSafety
import Itasca.Runtime.Compiler.Body.Reader.Replay.OrdinaryLedger
import Itasca.Runtime.Compiler.Body.Reader.Control.ControlLedger

/-!
The numerical callback ledger at a complete source-instruction boundary.

Main declarations: `ReachedCompilerLedger`. A direct consumer is `Compiler.Body.Reader.Acceptance.SourceBoundStatefulAcceptance`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- The numerical callback ledger at a complete source-instruction boundary. -/
structure ReachedCompilerLedger {A} (compiler : runtime.compiler.FunctionCompiler A)
    (values : List code.StackType) : Prop where
  observed : ObservedStack compiler values
  indirect : compiler.function.indirect.val.length ≤ compiler.function.code.val.length
  simd : compiler.function.simd.val.length ≤ compiler.function.code.val.length
  constants : compiler.function.v128_pool.val.length ≤ compiler.function.code.val.length
  fixups : FixupBudget compiler.frames.val compiler.function.code.val.length

theorem ReachedCompilerLedger.advance {A} {before after : runtime.compiler.FunctionCompiler A}
    {values next : List code.StackType} (held : ReachedCompilerLedger before values)
    (observed : ObservedStack after next) (growth : AuxiliaryGrowth before after)
    (fixups : FixupBudget after.frames.val after.function.code.val.length) : ReachedCompilerLedger after next := by
  obtain ⟨i,s,c⟩ := growth.bounded held.indirect held.simd held.constants
  exact ⟨observed,i,s,c,fixups⟩

theorem ReachedCompilerLedger.reader_wasm2 {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) {before after : runtime.compiler.FunctionCompiler A}
    {data env locals index st} (p : Wasm2.Pending data env .Wasm2 locals index st)
    (out : code.BodyState) (ctx : code.Context)
    (held : ReachedCompilerLedger before st.core.vals.val) (observed : ObservedStack after out.core.vals.val)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (data.val[p.start.val]'p.inbounds) before = .ok (.Ok (),out,after)) :
    ReachedCompilerLedger after out.core.vals.val := by
  by_cases control : (data.val[p.start.val]'p.inbounds).val ∈ [2,3,4,5,11,12,13,14,15]
  · obtain ⟨growth,fixups⟩ := reader_control_ledger_wasm2 ops law before after st out data env ctx index _ control held.fixups accepted
    exact held.advance observed growth fixups
  · have fresh := reader_ordinary_ledger_wasm2 p ops law before after out ctx _ control rfl accepted
    exact held.advance observed fresh.auxiliary (fresh.fixups held.fixups)

end Itasca.Runtime.Compiler
