import Exec.Abs.Core.Step
import Exec.Abs.Sim.Instruction

namespace Exec.Abs.Core
open SpecExt Exec.Spec

theorem instruction_slice (s : _root_.store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr)
    (covered : SliceInstr op)
    (typed : FrameTyped s {f with code := op :: after} []) :
    instruction s ambient f rest op after =
      astep ⟨s,ambient,{f with code := op :: after} :: rest,[]⟩ := by
  cases covered with
  | numeric descriptor =>
    cases descriptor with
    | conversion conversion => cases conversion <;> rfl
    | _ => rfl
  | const ty value =>
    have progress := const_progress s ambient f rest after ty value typed
    simp only [instruction,astep] at progress ⊢
    split <;> simp_all [advance]
  | local_get index => cases index; rfl
  | local_set index => cases index; rfl
  | local_tee index => cases index; rfl
  | br index => cases index; rfl
  | br_if index => cases index; rfl
  | call index => cases index; rfl
  | _ => rfl

/-- All numeric constants, including floating encodings, are administrative
moves with identical source decoding and a strictly decreasing potential. -/
theorem constant_progress (s : _root_.store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (after : List instr) (ty : numtype) (value : num_)
    (typed : CoreTyped ⟨s,ambient,{f with code := .CONST ty value :: after} :: rest,[]⟩) :
    ∃ next, instruction s ambient f rest (.CONST ty value) after = .next next ∧ CoreTyped next ∧
      NextSim ⟨s,ambient,{f with code := .CONST ty value :: after} :: rest,[]⟩ next := by
  let next : AState := ⟨s,ambient,{f with code := after, vals := f.vals ++ [.CONST ty value]} :: rest,[]⟩
  have fresh := const_preservation s ambient f rest after ty value [] typed.typed
  have frameTyped : FrameTyped s {f with code := .CONST ty value :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  refine ⟨next,rfl,⟨fresh,typed.contents⟩,Or.inl ⟨?_,?_⟩⟩
  · exact decode_const s ambient f rest ty value after (by simpa only [FrameHeights] using frameTyped_heights frameTyped)
  · exact const_measure_decreases s ambient f rest ty value after

theorem pure_instruction_progress (s : _root_.store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr)
    (functions : FunctionsTyped s) (typed : FrameTyped s {f with code := op :: after} [])
    (covered : SliceInstr op) : astep ⟨s,ambient,{f with code := op :: after} :: rest,[]⟩ ≠ .stuck := by
  cases covered with
  | numeric descriptor => exact Numeric.numeric_progress s ambient f rest after descriptor typed
  | nop => simp [astep, advance]
  | unreachable => simp [astep]
  | drop => exact drop_progress s ambient f rest after typed
  | const ty value => exact const_progress s ambient f rest after ty value typed
  | add ty => exact add_progress s ambient f rest after ty typed
  | sub ty => exact sub_progress s ambient f rest after ty typed
  | eqz ty => exact eqz_progress s ambient f rest after ty typed
  | eq ty => exact relation_progress s ambient f rest after ty .EQ (Or.inl rfl) typed
  | lt_u ty => exact relation_progress s ambient f rest after ty (.LT .U) (Or.inr rfl) typed
  | local_get index => cases index with | mk_uN i => exact local_get_progress s ambient f rest after i typed
  | local_set index => cases index with | mk_uN i => exact local_set_progress s ambient f rest after i typed
  | local_tee index => cases index with | mk_uN i => exact local_tee_progress s ambient f rest after i typed
  | block bt body _ => exact block_progress s ambient f rest after bt body typed
  | loop bt body _ => exact loop_progress s ambient f rest after bt body typed
  | ifelse bt yes no _ _ => exact if_progress s ambient f rest after bt yes no typed
  | br depth => cases depth with | mk_uN i => exact br_progress s ambient f rest after i typed
  | br_if depth => cases depth with | mk_uN i => exact br_if_progress s ambient f rest after i typed
  | call index => cases index with | mk_uN i => exact call_progress s ambient f rest after i functions typed
  | ret => exact return_progress s ambient f rest after typed
end Exec.Abs.Core

