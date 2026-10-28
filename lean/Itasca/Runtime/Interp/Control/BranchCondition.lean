import Itasca.Runtime.Interp.Relations.Conditional
import Itasca.Runtime.Interp.Control.BranchNoCopy
import Itasca.Runtime.Abs.Sim.Compose

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem branchIf_source_step (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr) (depth : Nat) (front : List val) (value : Nat) (bound : value < 2 ^ 32) :
    Abs.astep
      ⟨s, ambient, { f with code := .BR_IF (.mk_uN depth) :: after, vals := front ++ [Abs.integerVal .I32 value] } :: rest, []⟩ = .next
      ⟨s, ambient, { f with code := if value = 0 then after else .BR (.mk_uN depth) :: after, vals := front } :: rest, []⟩ := by
  have hb : value < 4294967296 := bound
  simp [Abs.astep, Abs.pop_append, Abs.integerVal, Abs.integer, numtype_Inn, hb, Abs.advance]

def branchIfFrame (f : Abs.AFrame) (after : List instr) (depth : Nat) (label : Abs.Label)
    (front discarded results : List val) (value : Nat) : Abs.AFrame :=
  if value = 0 then { f with code := after, vals := front ++ discarded ++ results }
  else { f with code := label.cont ++ label.after, labels := f.labels.drop (depth + 1), vals := front ++ results }

/-- A direct conditional branch may fuse the source BR_IF test and BR transfer.
Both reductions are derived from the generated source typing invariant. -/
theorem branchIf_source_refines (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr) (depth : Nat) (label : Abs.Label) (front discarded results : List val) (value : Nat)
    (bound : value < 2 ^ 32) (lookup : f.labels[depth]? = some label)
    (height : label.height = front.length) (arity : label.arity = results.length)
    (types : results.map Abs.valueType = label.branchTypes)
    (typed : Abs.ATyped ⟨s, ambient, { f with code := .BR_IF (.mk_uN depth) :: after, vals := front ++ discarded ++ results ++ [Abs.integerVal .I32 value] } :: rest, []⟩) :
    Abs.ATyped ⟨s, ambient, branchIfFrame f after depth label front discarded results value :: rest, []⟩ ∧
    Abs.NextSim
      ⟨s, ambient, { f with code := .BR_IF (.mk_uN depth) :: after, vals := front ++ discarded ++ results ++ [Abs.integerVal .I32 value] } :: rest, []⟩
      ⟨s, ambient, branchIfFrame f after depth label front discarded results value :: rest, []⟩ := by
  have step := branchIf_source_step s ambient f rest after depth (front ++ discarded ++ results) value bound
  have typedNext := Abs.instruction_preservation s ambient
    { f with vals := front ++ discarded ++ results ++ [Abs.integerVal .I32 value] } rest
    (.BR_IF (.mk_uN depth)) after _ (.br_if _) typed step
  have simulation := Abs.instruction_simulation s ambient
    { f with vals := front ++ discarded ++ results ++ [Abs.integerVal .I32 value] } rest
    (.BR_IF (.mk_uN depth)) after _ (.br_if _) typed step
  by_cases zero : value = 0
  · simpa only [branchIfFrame, if_pos zero] using And.intro typedNext simulation
  · simp only [if_neg zero] at typedNext simulation
    have branch := branch_source_step s ambient f rest after depth label front discarded results lookup height arity types
    have typedBranch := Abs.instruction_preservation s ambient { f with vals := front ++ discarded ++ results } rest
      (.BR (.mk_uN depth)) after _ (.br _) typedNext branch
    have branchSim := Abs.instruction_simulation s ambient { f with vals := front ++ discarded ++ results } rest
      (.BR (.mk_uN depth)) after _ (.br _) typedNext branch
    simpa only [branchIfFrame, if_neg zero] using And.intro typedBranch (simulation.trans branchSim)

/-- When the compiler omits the transfer, JumpIfNonZero implements the complete
conditional branch while retaining untouched dead operand words. -/
theorem dispatch_branchIfNoCopy_refines {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (cond target : U32) (value : Nat)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr) (depth : Nat) (label : Abs.Label) (front discarded results : List val)
    (frameLookup : exec.frames.val[index.val]? = some raw)
    (bound : value < 2 ^ 32) (lookup : f.labels[depth]? = some label)
    (height : label.height = front.length) (arity : label.arity = results.length)
    (types : results.map Abs.valueType = label.branchTypes)
    (noCopy : Code.slots (results.map Code.valueType) = 0 ∨ Code.slots (discarded.map Code.valueType) = 0)
    (position : cond.val = Code.slots ((f.locals ++ front ++ discarded ++ results).map Code.valueType))
    (typed : Abs.ATyped ⟨s, ambient, { f with code := .BR_IF (.mk_uN depth) :: after, vals := front ++ discarded ++ results ++ [Abs.integerVal .I32 value] } :: rest, []⟩)
    (slots : FrameSlots exec raw { f with vals := front ++ discarded ++ results ++ [Abs.integerVal .I32 value] }) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index
      raw.instance raw.function raw.base (.JumpIfNonZero cond target) ⦃ out => out.1 = .Ok () ∧
      out.2.1 = (if value = 0 then exec else { exec with frames := exec.frames.set index { raw with pc := target } }) ∧
      FrameSlots out.2.1 raw (branchIfFrame f after depth label front discarded results value) ∧
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      Abs.ATyped ⟨s, ambient, branchIfFrame f after depth label front discarded results value :: rest, []⟩ ∧
      Abs.NextSim
        ⟨s, ambient, { f with code := .BR_IF (.mk_uN depth) :: after, vals := front ++ discarded ++ results ++ [Abs.integerVal .I32 value] } :: rest, []⟩
        ⟨s, ambient, branchIfFrame f after depth label front discarded results value :: rest, []⟩ ⦄ := by
  have allValues : ValuesAt exec.slots.val raw.base.val ((f.locals ++ front ++ discarded ++ results) ++ [Abs.integerVal .I32 value]) := by
    simpa only [FrameSlots, List.append_assoc] using slots
  have input : WordsAt exec.slots.val (raw.base.val + cond.val) [value] := by
    simpa only [position, ValuesAt, Code.encodeValues, List.flatMap_cons, List.flatMap_nil,
      Abs.integerVal, Code.encodeValue, List.append_nil] using allValues.operands
  have reduced := allValues.locals.elide_transfer (front := f.locals ++ front) (discarded := discarded) (results := results) noCopy
  obtain ⟨typedNext, simulation⟩ := branchIf_source_refines s ambient f rest after depth label front discarded results value
    bound lookup height arity types typed
  apply WP.spec_mono (dispatch_jumpIfNonZero_exact memory hooks floats allocator exec store platform index raw cond target value
    frameLookup bound input)
  intro out effect
  obtain ⟨success, exactState, sameStore, samePlatform⟩ := effect
  refine ⟨success, exactState, ?_, sameStore, samePlatform, typedNext, simulation⟩
  rw [exactState]
  by_cases zero : value = 0
  · simp only [branchIfFrame, if_pos zero, FrameSlots]
    simpa only [List.append_assoc] using allValues.locals
  · simp only [branchIfFrame, if_neg zero, FrameSlots]
    simpa only [List.append_assoc] using reduced

end Itasca.Runtime.Interp
