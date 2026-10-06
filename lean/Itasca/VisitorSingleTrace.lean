import Itasca.VisitorRunTrace
import Itasca.VisitorTraceBytes
import Itasca.WasmInvariant

open Aeneas Aeneas.Std

namespace Itasca.VisitorTrace

/-- An ordinary step return records its exact independently encoded callback chunk. -/
def StepRecords {data env ctx bt st} (p : Wasm.Pending data env ctx bt st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation) (opcode : U8) : Prop :=
  ∀ v result final v', code.step visitor st data env ctx opcode v = .ok (result, final, v') →
    ∃ observations, observe v' = observe v ++ observations ∧
      StepTrace data p.start observations result final

/-- Lift independent success-byte provenance through a single recorded callback.
Failure before the callback is silent; the callback's own rejection is retained. -/
theorem run_step_trace {A V : Type} (data : Slice U8) (start : Usize)
    (read : Result (core.result.Result A error.OpError × code.OpIterState))
    (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe) (action : A → Action)
    (hbytes : ∀ s a, read = .ok (.Ok a, s) → ∃ token,
      (action a).token [] = some token ∧ (action a).opcode ≠ some 0x0E#u8 ∧
      Wasm.At data start token s.pos)
    (v : V) (result : BodyResult) (final : code.OpIterState) (v' : V)
    (h : CoreVisitor.run read (fun v s a => invoke visitor v (.op s (action a))) v =
      .ok (result, final, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      StepTrace data start observations result final := by
  rcases CoreVisitor.run.recorded read visitor observe hrecords (fun s a => .op s (action a))
      v result final v' h with ⟨err, _, rfl, hlog⟩ | ⟨a, reply, hr, rfl, hlog⟩
  · exact ⟨[], by simpa using hlog, .silent err final (Outcomes.empty _)⟩
  · obtain ⟨token, ht, hn, hb⟩ := hbytes final a hr
    refine ⟨[⟨.op final (action a), reply⟩], hlog,
      .complete (.single final (action a) reply token ht hn hb) ?_⟩
    exact Outcomes.single (.op final (action a)) reply

end Itasca.VisitorTrace
