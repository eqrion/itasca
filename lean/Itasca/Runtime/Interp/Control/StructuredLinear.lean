import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels
import Itasca.Runtime.Interp.Relations.Defaults
import Itasca.Runtime.SourceMachine.BrTable
import Itasca.Runtime.Equations
import Itasca.Runtime.SourceMachine.Sim.Structured

/-!
Sections, each formerly its own module: StructuredPoint, PendingJump, LoopBasis, StructuredLinear.
-/

/-! ## StructuredPoint -/

section

namespace Itasca.Runtime.Interp
open Aeneas.Std

/-- Function identity and local layout survive ordinary instruction steps. -/
structure FrameMetadata (before after : SourceMachine.AFrame) : Prop where
  address : after.fa = before.fa
  module : after.module = before.module
  results : after.resultTypes = before.resultTypes
  locals : after.locals.map Compiler.valueType = before.locals.map Compiler.valueType

theorem value_type_eq_abs (value : val) : Compiler.valueType value = SourceMachine.valueType value := by
  cases value with
  | REF_NULL rt => cases rt <;> rfl
  | _ => rfl

/-- Each compiler label records the actual saved operand prefix and source
continuation of its abstract-machine counterpart. -/
structure LabelMatch (values : List val) (label : SourceMachine.Label) (target : Compiler.LabelTarget) : Prop where
  front : target.front = (values.take label.height).map Compiler.valueType
  height : target.front.length = label.height
  branchTypes : target.branchTypes = label.branchTypes
  resultTypes : target.resultTypes = label.resultTypes
  cont : target.cont = label.cont
  after : target.after = label.after

/-- Labels use the same innermost-first indexing on both sides. -/
structure LabelsMatch (values : List val) (labels : List SourceMachine.Label) (targets : List Compiler.LabelTarget) : Prop where
  length : labels.length = targets.length
  atIndex : ∀ (depth : Nat) (label : SourceMachine.Label), labels[depth]? = some label →
    ∃ target, targets[depth]? = some target ∧ LabelMatch values label target

theorem LabelsMatch.static_lookup {values labels targets}
    (h : LabelsMatch values labels targets) (depth : Nat) (target : Compiler.LabelTarget)
    (lookup : targets[depth]? = some target) :
    ∃ label, labels[depth]? = some label ∧ LabelMatch values label target := by
  have bound : depth < labels.length := by
    rw [h.length]
    exact List.getElem?_eq_some_iff.mp lookup |>.1
  have found : labels[depth]? = some labels[depth] := List.getElem?_eq_getElem bound
  obtain ⟨actual, actualAt, matching⟩ := h.atIndex depth labels[depth] found
  have same : actual = target := Option.some.inj (actualAt.symm.trans lookup)
  subst actual
  exact ⟨labels[depth], found, matching⟩

/-- Static branch stack decomposition determines concrete value intervals and
all transfer slots; no dynamic result correspondence is inserted as a premise. -/
theorem LabelsMatch.branch_layout {values labels targets} (locals : List val)
    (h : LabelsMatch values labels targets) (depth : Nat) (target : Compiler.LabelTarget)
    (lookup : targets[depth]? = some target) (dst src count : U32)
    (layout : Compiler.BranchLayout (locals.map Compiler.valueType) (values.map Compiler.valueType) target dst src count) :
    ∃ label front discarded results,
      labels[depth]? = some label ∧ LabelMatch values label target ∧
      values = front ++ discarded ++ results ∧ label.height = front.length ∧
      label.arity = results.length ∧ results.map SourceMachine.valueType = label.branchTypes ∧
      dst.val = Compiler.slots ((locals ++ front).map Compiler.valueType) ∧
      src.val = Compiler.slots ((locals ++ front ++ discarded).map Compiler.valueType) ∧
      count.val = Compiler.slots (results.map Compiler.valueType) := by
  obtain ⟨label, found, matching⟩ := h.static_lookup depth target lookup
  obtain ⟨discardedTypes, stackTypes, destination, source, size⟩ := layout
  obtain ⟨initial, results, valuesSplit, initialTypes, resultTypes⟩ := List.map_eq_append_iff.mp stackTypes
  obtain ⟨front, discarded, initialSplit, frontTypes, discardedType⟩ := List.map_eq_append_iff.mp initialTypes
  have frontLength : front.length = label.height := by
    have equal := congrArg List.length frontTypes
    simpa only [List.length_map, matching.height] using equal
  have resultLength : results.length = label.arity := by
    have equal := congrArg List.length resultTypes
    simpa only [List.length_map, matching.branchTypes, SourceMachine.Label.arity] using equal
  have types : results.map SourceMachine.valueType = label.branchTypes := by
    simpa only [show Compiler.valueType = SourceMachine.valueType from funext value_type_eq_abs, matching.branchTypes] using resultTypes
  refine ⟨label, front, discarded, results, found, matching, ?_, frontLength.symm, resultLength.symm, types, ?_, ?_, ?_⟩
  · simpa only [initialSplit] using valuesSplit
  · simpa only [List.map_append, Compiler.slots_append, frontTypes] using destination
  · simpa only [List.map_append, Compiler.slots_append, frontTypes, discardedType, Nat.add_assoc] using source
  · simpa only [resultTypes] using size

theorem LabelsMatch.drop {values labels targets} (h : LabelsMatch values labels targets) (count : Nat) :
    LabelsMatch values (labels.drop count) (targets.drop count) := by
  constructor
  · simp only [List.length_drop, h.length]
  · intro depth label lookup
    have original : labels[count + depth]? = some label := by simpa using lookup
    obtain ⟨target, found, matching⟩ := h.atIndex (count + depth) label original
    exact ⟨target, by simpa using found, matching⟩

theorem LabelMatch.reprefix {before after : List val} {label target}
    (h : LabelMatch before label target)
    (same : before.take label.height = after.take label.height) : LabelMatch after label target :=
  { h with front := h.front.trans (congrArg (List.map Compiler.valueType) same) }

theorem LabelsMatch.reprefix {before after : List val} {labels targets}
    (h : LabelsMatch before labels targets)
    (same : ∀ label ∈ labels, before.take label.height = after.take label.height) :
    LabelsMatch after labels targets := by
  refine ⟨h.length, ?_⟩
  intro depth label lookup
  obtain ⟨target, found, matching⟩ := h.atIndex depth label lookup
  exact ⟨target, found, matching.reprefix (same label (List.mem_of_getElem? lookup))⟩

theorem LabelsMatch.replace_suffix {front before after : List val} {labels targets}
    (h : LabelsMatch (front ++ before) labels targets)
    (heights : ∀ label ∈ labels, label.height ≤ front.length) :
    LabelsMatch (front ++ after) labels targets := by
  apply h.reprefix
  intro label member
  simp only [List.take_append_of_le_length (heights label member)]

/-- A branch only changes operand words at or above its target height. The
source typing invariant supplies the nesting bound for all surviving labels. -/
theorem LabelsMatch.branch {front discarded results : List val} {labels targets}
    (h : LabelsMatch (front ++ discarded ++ results) labels targets) (depth : Nat)
    (heights : ∀ label ∈ labels.drop (depth + 1), label.height ≤ front.length) :
    LabelsMatch (front ++ results) (labels.drop (depth + 1)) (targets.drop (depth + 1)) := by
  apply (h.drop (depth + 1)).reprefix
  intro label member
  have bound := heights label member
  simp only [List.append_assoc, List.take_append_of_le_length bound]

end Itasca.Runtime.Interp

end

/-! ## PendingJump -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Administrative potential covers source constants, forward skip jumps,
and the second half of a branch, including backward loop targets. The pending
phase weighs more than any possible remaining instruction distance. -/
def dispatchMeasure (pending : Bool) (codeLength pc : Nat) (state : SourceMachine.AState) : Nat :=
  SourceMachine.administrativeMeasure state * (2 * (codeLength + 1)) +
    (if pending then codeLength + 1 else 0) + (codeLength - pc)

theorem dispatch_measure_jump (state : SourceMachine.AState) (codeLength pc target : Nat) :
    dispatchMeasure false codeLength target state < dispatchMeasure true codeLength pc state := by
  simp only [dispatchMeasure, Bool.false_eq_true, ite_false, ite_true]
  omega

theorem dispatch_measure_forward (state : SourceMachine.AState) (codeLength pc target : Nat)
    (forward : pc < target) (bound : target ≤ codeLength) :
    dispatchMeasure false codeLength target state < dispatchMeasure false codeLength pc state := by
  simp only [dispatchMeasure, Bool.false_eq_true, ite_false]
  omega

theorem dispatch_jump_exact {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index inst function base : Usize) (raw : runtime.interp.Frame) (target : U32)
    (lookup : exec.frames.val[index.val]? = some raw) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index inst function base
      (.Jump target) ⦃ out => out.1 = .Ok () ∧
        out.2.1 = { exec with frames := exec.frames.set index { raw with pc := target } } ∧
        out.2.2.1 = store ∧ out.2.2.2 = platform ⦄ := by
  have bound : index.val < exec.frames.length := List.getElem?_eq_some_iff.mp lookup |>.1
  simp only [runtime.interp.dispatch]
  obtain ⟨out, result, success, found, foundAt, frames, unchanged⟩ := WP.spec_imp_exists
    (jump_effect exec index target bound)
  have same : found = raw := Option.some.inj (foundAt.symm.trans lookup)
  subst found
  have frameEq : out.2.frames = exec.frames.set index { raw with pc := target } :=
    alloc.vec.Vec.ext _ _ (by simpa only [alloc.vec.Vec.set_val_eq] using frames)
  have exactState := congrArg (fun e : runtime.interp.Execution => { e with frames := out.2.frames }) unchanged
  change out.2 = { exec with frames := out.2.frames } at exactState
  rw [frameEq] at exactState
  rw [result, bind_ok]
  rcases out with ⟨answer, nextExec⟩
  with_unfolding_all apply WP.spec.ret
  exact ⟨success, exactState, rfl, rfl⟩

theorem step_jump_exact {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (target : U32)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (fetched : compiled.code.val[raw.pc.val]? = some (.Jump target)) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧
      out.2.1 = { exec with frames := exec.frames.set index { raw with pc := target } } ∧
      out.2.2.1 = store ∧ out.2.2.2 = platform ⦄ := by
  apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
    (.Jump target) last hf hi hc fetched pcBound
  intro pc hpc
  have valid : index.val < exec.frames.val.length := List.getElem?_eq_some_iff.mp hf |>.1
  have lookup : (exec.frames.set index { raw with pc := pc }).val[index.val]? = some { raw with pc := pc } := by
    simp [alloc.vec.Vec.set_val_eq, valid]
  apply WP.spec_mono (dispatch_jump_exact memory hooks floats allocator
    { exec with frames := exec.frames.set index { raw with pc := pc } }
    store platform index raw.instance raw.function raw.base { raw with pc := pc } target lookup)
  intro out effect
  obtain ⟨success, exactState, sameStore, samePlatform⟩ := effect
  have frames : (exec.frames.set index { raw with pc := pc }).set index { raw with pc := target } =
      exec.frames.set index { raw with pc := target } := by
    apply alloc.vec.Vec.ext
    simp only [alloc.vec.Vec.set_val_eq, List.set_set]
  simp only [frames] at exactState
  exact ⟨success, exactState, sameStore, samePlatform⟩

end Itasca.Runtime.Interp

end

/-! ## LoopBasis -/

section

/-! Compositional loop facts for the extracted interpreter. These lemmas are
independent of the Wasm simulation; callers must discharge the body contract. -/
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

inductive NormalTrace {α β : Type} (body : α → Result (ControlFlow α β)) : Nat → α → β → Prop
  | done {state result} (step : body state = .ok (.done result)) : NormalTrace body 0 state result
  | next {count state next result} (step : body state = .ok (.cont next))
      (tail : NormalTrace body count next result) : NormalTrace body (count + 1) state result

/-- Every finite trace of normal body results is the actual extracted loop
result. No termination or semantic assumption is needed in this direction. -/
theorem NormalTrace.result {α β : Type} {body : α → Result (ControlFlow α β)}
    {count : Nat} {state : α} {result : β} (trace : NormalTrace body count state result) :
    loop body state = .ok result := by
  induction trace with
  | done step => rw [loop.eq_def]; simp [step]
  | next step tail ih => rw [loop.eq_def]; simpa [step] using ih

/-- An invariant-preserving body that never fails makes the loop safe, whether the loop or
one of its iterations diverges. Every returned value has an exact finite body trace. -/
theorem loop_trace_dspec {α β : Type} (body : α → Result (ControlFlow α β))
    (invariant : α → Prop) (post : β → Prop)
    (bodySafe : ∀ state, invariant state → body state ⦃ out =>
      match out with
      | .cont next => invariant next
      | .done result => post result ⦄div)
    (state : α) (initial : invariant state) :
    loop body state ⦃ result => ∃ count, NormalTrace body count state result ∧ post result ⦄div := by
  have adm : Lean.Order.admissible (fun run : α → Result β => ∀ state, invariant state →
      run state ⦃ result => ∃ count, NormalTrace body count state result ∧ post result ⦄div) := by
    apply Lean.Order.admissible_pi
    intro current
    apply Lean.Order.admissible_pi
    intro hcurrent
    exact WP.dspec_func_admissible current _
  apply loop.fixpoint_induct body _ adm ?_ state initial
  intro run ih state initial
  have safe := bodySafe state initial
  dsimp only
  generalize hbody : body state = answer at safe ⊢
  cases safe with
  | div => rw [bind_div]; exact .div _
  | @ret _ out hprop =>
    rw [bind_ok]
    cases out with
    | done result => exact WP.dspec.ret ⟨0, .done hbody, hprop⟩
    | cont next =>
      apply WP.dspec_mono (ih next hprop)
      rintro result ⟨count, trace, hpost⟩
      exact ⟨count + 1, .next hbody trace, hpost⟩

end Itasca.Runtime.Interp

end

/-! ## StructuredLinear -/

section

namespace Itasca.Runtime.Interp

def linearSource : instr → Bool
  | .NOP | .DROP | .CONST .. | .BINOP .. | .TESTOP .. | .RELOP ..
  | .UNOP .. | .CVTOP .. | .LOCAL_GET .. | .LOCAL_SET .. | .LOCAL_TEE .. => true
  | _ => false

def linearInputs : instr → Nat
  | .DROP | .TESTOP .. | .UNOP .. | .CVTOP .. | .LOCAL_SET .. | .LOCAL_TEE .. => 1
  | .BINOP .. | .RELOP .. => 2
  | _ => 0

theorem linear_source_inputs {C : context} {op : instr} {inputs outputs : List valtype}
    (linear : linearSource op = true)
    (typed : Instr_ok C op ⟨.mk_list inputs, .mk_list outputs⟩) : inputs.length = linearInputs op := by
  cases typed <;> simp_all [linearSource, linearInputs]

/-- Generated operand typing places every saved label prefix below the values
consumed by a linear instruction, even when its replacement changes a value. -/
theorem frame_linear_heights {s : store} {f : SourceMachine.AFrame} {op : instr} {code : List instr}
    (typed : SourceMachine.FrameTyped s { f with code := op :: code } [])
    (linear : linearSource op = true) (front : List val)
    (shape : f.vals.length = front.length + linearInputs op) :
    ∀ label ∈ f.labels, label.height ≤ front.length := by
  obtain ⟨C, first, operands, ins, outs, bindings, localTypes, operation, split, values, wf, heights⟩ :=
    SourceMachine.frame_typed_operands_bounds typed
  have count := linear_source_inputs linear operation
  have operandsLength := Spec.results_typed_length values
  have firstLength : first.length = front.length := by
    have splitLength := congrArg List.length split
    simp only [List.length_append] at splitLength
    omega
  simpa only [firstLength] using heights

end Itasca.Runtime.Interp

end
