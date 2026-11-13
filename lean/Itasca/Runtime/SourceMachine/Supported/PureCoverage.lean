import Itasca.Runtime.SourceMachine.Measure
import Itasca.Runtime.SourceMachine.Core.Trap
import Itasca.Runtime.SourceMachine.BrTable
import Itasca.Runtime.SourceMachine.Numeric.Transition
import Itasca.Runtime.SourceMachine.Bound

/-!
Sections, each formerly its own module: CoreStuck, Invoke, PureCoverage.
-/

/-! ## CoreStuck -/

section

namespace Itasca.Runtime.SourceMachine

/-- `Core.instruction` never executes the head; another transition relation handles it. -/
def CoreStuck (op : instr) : Prop :=
  ∀ s ambient f rest after, Core.instruction s ambient f rest op after = .stuck

theorem float_core_stuck (op : Float.Instruction) : CoreStuck op.source := by
  intro s ambient f rest after
  cases op <;> simp [Core.instruction,Float.Instruction.source,astep,Numeric.decodeInstruction]

theorem stateful_core_stuck (op : Stateful.Instruction) : CoreStuck op.source := by
  intro s ambient f rest after
  cases op <;> simp [Core.instruction,Stateful.Instruction.source,astep,Numeric.decodeInstruction]

theorem indirect_core_stuck (table : tableidx) (type : typeidx) : CoreStuck (.CALL_INDIRECT table type) := by
  intro s ambient f rest after
  simp [Core.instruction,astep,Numeric.decodeInstruction]

theorem SimdInstr.core_stuck {op : instr} (supported : SimdInstr op) : CoreStuck op := by
  intro s ambient f rest after
  cases supported with
  | pure signature => cases signature <;> rfl
  | constant => rfl
  | memory signature => cases signature <;> rfl

theorem BinaryInstr.core_head {op} (allowed : BinaryInstr op) : CoreHead op ∨ CoreStuck op := by
  cases allowed with
  | nop => exact .inl (.pure .nop)
  | unreachable => exact .inl (.pure .unreachable)
  | drop => exact .inl (.pure .drop)
  | const ty value => exact .inl (.const ty value)
  | numeric op => exact .inl (.pure (.numeric op))
  | float op => exact .inr (float_core_stuck op)
  | select => exact .inl .select
  | typed_select ty => exact .inr fun _ _ _ _ _ => rfl
  | local_get index => exact .inl (.pure (.local_get index))
  | local_set index => exact .inl (.pure (.local_set index))
  | local_tee index => exact .inl (.pure (.local_tee index))
  | global_get index => exact .inl (.global_get index)
  | global_set index => exact .inl (.global_set index)
  | load op argument => exact .inl (.load op argument)
  | store op argument => exact .inl (.store op argument)
  | stateful op => exact .inr (stateful_core_stuck op)
  | simd simd => exact .inr simd.core_stuck
  | block ty body _ => exact .inl (.pure (.block ty body))
  | loop ty body _ => exact .inl (.pure (.loop ty body))
  | ifelse ty yes no _ _ => exact .inl (.pure (.ifelse ty yes no))
  | br depth => exact .inl (.pure (.br depth))
  | br_if depth => exact .inl (.pure (.br_if depth))
  | br_table labels fallback => exact .inr fun _ _ _ _ _ => rfl
  | call index => exact .inl (.pure (.call index))
  | call_indirect table type => exact .inr (indirect_core_stuck table type)
  | ret => exact .inl (.pure .ret)

end Itasca.Runtime.SourceMachine

end

/-! ## Invoke -/

section

namespace Itasca.Runtime.SourceMachine
open SpecExt Itasca.Runtime.Spec

/-- A real defined function address and typed arguments construct the initial
abstract state and its generated specification call reduction. -/
theorem defined_supported_invocation (s : store) (ambient : frame) (address : funcaddr)
    (moduleInst : moduleinst) (typeIndex : idx) (params results : List valtype)
    (locals : List «local») (body : List instr) (args : List val)
    (hs : wf_store s) (ha : wf_frame ambient) (functions : FunctionsTyped s)
    (covered : FunctionsSupported s)
    (lookup : s.FUNCS[address]? = some ⟨⟨.mk_list params, .mk_list results⟩, moduleInst,
      .FUNC typeIndex locals body⟩)
    (arguments : ResultsTyped s params args) :
    ∃ defaults, defaultLocals locals = some defaults ∧
      ATyped (entryState s ambient address moduleInst results body args defaults) ∧
      SupportedState (entryState s ambient address moduleInst results body args defaults) ∧
      StepH ⟨⟨s, ambient⟩, vals args ++ [.CALL_ADDR address]⟩ []
        (decode (entryState s ambient address moduleInst results body args defaults)) := by
  have member := List.mem_of_getElem? lookup
  have hfunc := functions _ member
  obtain ⟨C, bindings, emptyLocals, emptyLabels, _, hfunc⟩ := hfunc
  obtain ⟨defaults, hdefaults, hcallee⟩ := callee_frame_typed hs (function_module_wf hs member)
    bindings emptyLocals emptyLabels hfunc arguments address
  refine ⟨defaults, hdefaults, ?_, ?_, ?_⟩
  · refine ⟨hs, functions, ha, .cons hcallee (.nil results), by simp [entryState, Forall], by simp [entryState], ?_⟩
    intro frame hm
    simp only [entryState, List.mem_singleton] at hm
    subst frame
    exact frame_typed_heights hcallee
  · refine ⟨?_, covered⟩
    intro frame hm
    simp only [entryState, List.mem_singleton] at hm
    subst frame
    exact ⟨covered _ member, by simp [Forall]⟩
  · obtain ⟨types, hlocals, nonbot⟩ := function_local_types hfunc
    subst locals
    have result := call_invoke s ambient address typeIndex moduleInst params results types body args defaults
      hs ha lookup nonbot hdefaults (results_typed_wf arguments) (results_typed_length arguments)
    simpa [entryState, decode, decodeFrames, decodeLabels, vals, AFrame.arity, AFrame.toFrame, Label.arity] using result

end Itasca.Runtime.SourceMachine

end

/-! ## PureCoverage -/

section

namespace Itasca.Runtime.SourceMachine.Supported

theorem replace_frame {s : store} {ambient : frame} {f f' : AFrame}
    {rest : List AFrame} (h : SupportedState ⟨s, ambient, f :: rest, []⟩)
    (hf : FrameSupported f') : SupportedState ⟨s, ambient, f' :: rest, []⟩ := by
  refine ⟨?_, h.functions⟩
  intro frame hm
  simp only [List.mem_cons] at hm
  rcases hm with rfl | hm
  · exact hf
  · exact h.active frame (by simp [hm])

theorem advance_covered {s : store} {ambient : frame} {f f' : AFrame}
    {rest : List AFrame} {next : AState} (h : SupportedState ⟨s, ambient, f :: rest, []⟩)
    (step : advance ⟨s, ambient, f :: rest, []⟩ f' rest = .next next)
    (hf : FrameSupported f') : SupportedState next := by
  simp only [advance, AResult.next.injEq] at step
  rw [← step]
  exact replace_frame h hf

theorem return_frame_covered {s : store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {next : AState} (h : SupportedState ⟨s, ambient, f :: rest, []⟩)
    (step : returnFrame ⟨s, ambient, f :: rest, []⟩ f rest = .next next) : SupportedState next := by
  simp only [returnFrame] at step
  split at step
  · cases rest with
    | nil =>
      simp only [AResult.next.injEq] at step
      rw [← step]
      exact ⟨by simp [Forall], h.functions⟩
    | cons caller callers =>
      simp only [advance, AResult.next.injEq] at step
      rw [← step]
      refine ⟨?_, h.functions⟩
      intro frame hm
      simp only [List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact h.active caller (by simp)
      · exact h.active frame (by simp [hm])
  · contradiction

theorem branch_covered {s : store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {depth : Nat} {next : AState} (h : SupportedState ⟨s, ambient, f :: rest, []⟩)
    (step : branch ⟨s, ambient, f :: rest, []⟩ f rest depth = .next next) : SupportedState next := by
  simp only [branch] at step
  split at step
  · contradiction
  · rename_i target lookup
    split at step
    · apply advance_covered h step
      have ht := (h.active f (by simp)).2 target (List.mem_of_getElem? lookup)
      refine ⟨?_, ?_⟩
      · intro i hi
        rcases List.mem_append.mp hi with hi | hi
        · exact ht.1 i hi
        · exact ht.2 i hi
      · intro label hm
        exact (h.active f (by simp)).2 label (List.mem_of_mem_drop hm)
    · contradiction

/-- Code-bearing store entries are unchanged by the integer slice; a defined
call selects a body already covered by the store's slice invariant. -/
theorem call_covered {s : store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {index : Nat} {after : List instr} {next : AState}
    (h : SupportedState ⟨s, ambient, f :: rest, []⟩) (ha : Forall BinaryInstr after)
    (step : call ⟨s, ambient, f :: rest, []⟩ f rest index after = .next next) : SupportedState next := by
  cases resolve : f.module.FUNCS[index]? with
  | none => simp [call, resolve] at step
  | some address =>
    cases lookup : s.FUNCS[address]? with
    | none => simp [call, resolve, lookup] at step
    | some fn =>
      have hfn := h.functions fn (List.mem_of_getElem? lookup)
      cases ht : fn.TYPE with
      | mk_functype params results =>
        cases params with
        | mk_list params =>
          cases results with
          | mk_list results =>
            cases hc : fn.CODE with
            | HOST host =>
              simp only [call,resolve,lookup,ht,hc] at step
              repeat' first | split at step | contradiction
            | FUNC fi locals body =>
              simp only [hc] at hfn
              simp only [call, resolve, lookup, ht, hc] at step
              repeat' first | split at step | contradiction
              simp only [AResult.next.injEq] at step
              rw [← step]
              refine ⟨?_, h.functions⟩
              intro frame hm
              simp only [List.mem_cons] at hm
              rcases hm with rfl | rfl | hm
              · exact ⟨hfn, by simp [Forall]⟩
              · exact ⟨ha, (h.active f (by simp)).2⟩
              · exact h.active frame (by simp [hm])


/-- The source instruction families are closed under each successful abstract
transition, including code introduced by structured control. -/
theorem slice_instruction_covered (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr) (next : AState)
    (descriptor : PureHead op)

    (slice : SupportedState ⟨s, ambient, { f with code := op :: after } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := op :: after } :: rest, []⟩ = .next next) :
    SupportedState next := by
  have hf := slice.active { f with code := op :: after } (by simp)
  have ha : Forall BinaryInstr after := fun i hm => hf.1 i (by simp [hm])
  have hl := hf.2
  cases descriptor with
  | numeric descriptor =>
    obtain ⟨values, rfl⟩ := Numeric.astep_effect ⟨s, ambient, [], []⟩ f rest after descriptor next step
    exact advance_covered slice rfl ⟨ha, hl⟩
  | nop => exact advance_covered slice step ⟨ha, hl⟩
  | unreachable => simp [astep] at step
  | const ty value =>
    simp only [astep, integerBinary] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_covered slice step ⟨ha, hl⟩
  | drop =>
    simp only [astep, integerBinary] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_covered slice step ⟨ha, hl⟩
  | local_get index =>
    simp only [astep, integerBinary] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_covered slice step ⟨ha, hl⟩
  | local_set index =>
    simp only [astep, integerBinary] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_covered slice step ⟨ha, hl⟩
  | local_tee index =>
    simp only [astep, integerBinary] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_covered slice step ⟨ha, hl⟩
  | br index => cases index with | mk_uN i => exact branch_covered slice step
  | call index => cases index with | mk_uN i => exact call_covered slice ha step
  | ret => exact return_frame_covered slice step
  | block bt body =>
    have hb := SourceMachine.BinaryInstr.block_body (hf.1 _ (List.mem_cons_self ..))
    simp only [astep, enterLabel, Bool.false_eq_true, ite_false] at step
    repeat' first | split at step | contradiction
    all_goals
      apply advance_covered slice step
      refine ⟨hb, ?_⟩
      intro label hm
      simp only [List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact ⟨by simp [Forall], ha⟩
      · exact hl label hm
  | loop bt body =>
    have hb := SourceMachine.BinaryInstr.loop_body (hf.1 _ (List.mem_cons_self ..))
    simp only [astep, enterLabel, ite_true] at step
    repeat' first | split at step | contradiction
    all_goals
      apply advance_covered slice step
      refine ⟨hb, ?_⟩
      intro label hm
      simp only [List.mem_cons] at hm
      rcases hm with rfl | hm
      · refine ⟨?_, ha⟩
        intro i hi
        simp only [List.mem_singleton] at hi
        subst i
        exact hf.1 _ (List.mem_cons_self ..)
      · exact hl label hm
  | ifelse bt yes no =>
    obtain ⟨hy, hn⟩ := SourceMachine.BinaryInstr.if_bodies (hf.1 _ (List.mem_cons_self ..))
    simp only [astep] at step
    repeat' first | split at step | contradiction
    all_goals
      apply advance_covered slice step
      refine ⟨?_, hl⟩
      intro i hi
      simp only [List.mem_cons] at hi
      rcases hi with rfl | hi
      · apply SourceMachine.BinaryInstr.block
        first | assumption | split <;> assumption
      · exact ha i hi
  | br_if index =>
    cases index with
    | mk_uN i =>
      simp only [astep] at step
      repeat' first | split at step | contradiction
      all_goals
        apply advance_covered slice step
        first
        | exact ⟨ha, hl⟩
        | refine ⟨?_, hl⟩
          intro op hm
          simp only [List.mem_cons] at hm
          rcases hm with rfl | hm
          · exact SourceMachine.BinaryInstr.br _
          · exact ha op hm


end Itasca.Runtime.SourceMachine.Supported

end
