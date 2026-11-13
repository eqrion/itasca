import Itasca.Runtime.Interp.Relations.ReferenceTransfers
import Itasca.Runtime.Interp.Relations.Normalization
import Itasca.Runtime.SourceMachine.Numeric.Decode
import Itasca.Runtime.Interp.Control.StructuredLinear
import Itasca.Runtime.Interp.Relations.ValueLookup
import Itasca.Runtime.Interp.Relations.SourceClosure
import Itasca.Runtime.Interp.Relations.Regions
import Itasca.Runtime.Compiler.Local.Control.Segments.Structured
import Itasca.Runtime.SourceMachine.Sim.Host
import Itasca.Runtime.Interp.Relations.Conditional
import Itasca.Runtime.Interp.Relations.ControlPoint
import Itasca.Runtime.Interp.Numeric.Integer.IntCounts
import Itasca.Runtime.Interp.Relations.Fetch

/-!
Sections, each formerly its own module: NormalizeClosure, BranchNoCopy, BranchCondition, BranchConditionStep, LoopHead, NormalizeCompose.
-/

/-! ## NormalizeClosure -/

section

namespace Itasca.Runtime.Interp

/-- A source position that requires bytecode execution or function return. -/
def ReadySource (f : SourceMachine.AFrame) : Prop :=
  match f.code with
  | [] => f.labels = []
  | .NOP :: _ | .DROP :: _ | .BLOCK _ _ :: _ => False
  | _ => True

theorem ErasedStep.metadata {before after} (step : ErasedStep before after) : FrameMetadata before after := by
  cases step <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem FrameMetadata.trans {before middle after}
    (first : FrameMetadata before middle) (second : FrameMetadata middle after) : FrameMetadata before after :=
  ⟨second.address.trans first.address, second.module.trans first.module,
    second.results.trans first.results, second.locals.trans first.locals⟩

theorem ErasedStep.closure {before after} (step : ErasedStep before after) : SourceClosure before after := by
  cases step with
  | nop f after => exact .tail _ _ _ _ _ (fun _ h => h)
  | drop f after front value => exact .tail { f with vals := front ++ [value] } .DROP after f.locals front (fun bound h => ⟨h.1, (SourceMachine.values_bound_append.mp h.2).1⟩)
  | block f bt body after front params results signature shape => exact .block _ _ _ _ _ _
  | label f label labels => exact .label _ _ _

theorem ErasedSteps.closure {count before after} (steps : ErasedSteps count before after) : SourceClosure before after := by
  induction steps with
  | nil => exact .refl _
  | cons step tail ih => exact step.closure.trans ih

end Itasca.Runtime.Interp

end

/-! ## BranchNoCopy -/

section

/-!
Branch execution with a transferred or already-positioned result region. The transfer effect and ValuesAt transport justify eliding a redundant copy before the common source branch step.
-/

/-! ## Branch Transfer -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- The compiler specializes short branch transfers to fixed-width copies. -/
abbrev transferInstruction := Compiler.transferInstruction

set_option maxHeartbeats 800000 in
theorem dispatch_transfer_effect {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index inst function base : Usize) (dst src count : U32)
    (source : base.val + src.val + count.val ≤ exec.slots.length)
    (destination : base.val + dst.val + count.val ≤ exec.slots.length) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index inst function base
      (transferInstruction dst src count) ⦃ out => out.1 = .Ok () ∧
        SlotsEffect exec out.2.1 (copyWords exec.slots.val (base.val + dst.val) (base.val + src.val) count.val) ∧
        out.2.2.1 = store ∧ out.2.2.2 = platform ⦄ := by
  by_cases one : count.val = 1
  · simp only [transferInstruction, Compiler.transferInstruction, if_pos one, runtime.interp.dispatch]
    obtain ⟨out, result, success, effect⟩ := WP.spec_imp_exists
      (copy_effect exec base dst src (by omega) (by omega))
    rw [result, bind_ok]
    rcases out with ⟨answer, next⟩
    with_unfolding_all apply WP.spec.ret
    exact ⟨success, by simpa only [one, copyWords] using effect, rfl, rfl⟩
  · by_cases two : count.val = 2
    · simp only [transferInstruction, Compiler.transferInstruction, if_neg one, if_pos two, runtime.interp.dispatch]
      obtain ⟨out, result, success, effect⟩ := WP.spec_imp_exists
        (copy2_effect exec base dst src (by omega) (by omega))
      rw [result, bind_ok]
      rcases out with ⟨answer, next⟩
      with_unfolding_all apply WP.spec.ret
      exact ⟨success, by simpa only [two] using effect, rfl, rfl⟩
    · simp only [transferInstruction, Compiler.transferInstruction, if_neg one, if_neg two, runtime.interp.dispatch]
      obtain ⟨out, result, success, effect⟩ := WP.spec_imp_exists
        (copy_n_effect exec base dst src count source destination
          (by scalar_tac) (by scalar_tac))
      rw [result, bind_ok]
      rcases out with ⟨answer, next⟩
      with_unfolding_all apply WP.spec.ret
      exact ⟨success, effect, rfl, rfl⟩

/-- Removing an operand interval copies the retained results downward. This
includes overlapping source/destination regions and zero result words. -/
theorem ValuesAt.transfer {words : List U64} {base : Nat}
    {front discarded results : List val}
    (live : ValuesAt words base (front ++ discarded ++ results))
    (capacity : base + Compiler.slots ((front ++ discarded ++ results).map Compiler.valueType) ≤ words.length) :
    ValuesAt (copyWords words
      (base + Compiler.slots (front.map Compiler.valueType))
      (base + Compiler.slots ((front ++ discarded).map Compiler.valueType))
      (Compiler.slots (results.map Compiler.valueType))) base (front ++ results) := by
  have saved : WordsAt words base (Compiler.encodeValues front) := by
    apply WordsAt.append_left (right := Compiler.encodeValues discarded ++ Compiler.encodeValues results)
    simpa only [ValuesAt, Compiler.encode_values_append, List.append_assoc] using live
  have input : WordsAt words (base + Compiler.slots ((front ++ discarded).map Compiler.valueType))
      (Compiler.encodeValues results) := by
    have suffix := live.operands
    simpa only [ValuesAt] using suffix
  have order : base + (Compiler.encodeValues front).length ≤
      base + Compiler.slots ((front ++ discarded).map Compiler.valueType) := by
    simp only [Compiler.encode_values_length, List.map_append, Compiler.slots_append]
    omega
  have source : base + Compiler.slots ((front ++ discarded).map Compiler.valueType) +
      (Compiler.encodeValues results).length ≤ words.length := by
    simpa only [Compiler.encode_values_length, List.map_append, Compiler.slots_append, Nat.add_assoc] using capacity
  have copied := WordsAt.copy_append saved input (Or.inl order) source (by omega)
  simpa only [ValuesAt, Compiler.encode_values_append, Compiler.encode_values_length] using copied

/-- The first instruction in a compiled branch pair performs the source
branch's operand transfer. A separate pending-jump phase retains its target. -/
theorem dispatch_branch_transfer_refines {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex : Usize) (raw : runtime.interp.Frame) (dst src count : U32)
    (s : _root_.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (depth : Nat) (target : SourceMachine.Label)
    (front discarded results : List val)
    (lookup : f.labels[depth]? = some target)
    (height : target.height = front.length)
    (arity : target.arity = results.length)
    (types : results.map SourceMachine.valueType = target.branchTypes)
    (typed : SourceMachine.ATyped ⟨s, ambient, { f with code := .BR (.mk_uN depth) :: after, vals := front ++ discarded ++ results } :: rest, []⟩)
    (slots : FrameSlots exec raw { f with vals := front ++ discarded ++ results })
    (destination : dst.val = Compiler.slots ((f.locals ++ front).map Compiler.valueType))
    (source : src.val = Compiler.slots ((f.locals ++ front ++ discarded).map Compiler.valueType))
    (size : count.val = Compiler.slots (results.map Compiler.valueType))
    (capacity : raw.base.val + Compiler.slots ((f.locals ++ front ++ discarded ++ results).map Compiler.valueType) ≤ exec.slots.length) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex
      raw.instance raw.function raw.base (transferInstruction dst src count) ⦃ out =>
      out.1 = .Ok () ∧
      FrameSlots out.2.1 raw { f with code := target.cont ++ target.after, labels := f.labels.drop (depth + 1), vals := front ++ results } ∧
      { out.2.1 with slots := exec.slots } = exec ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      SourceMachine.NextSim
        ⟨s, ambient, { f with code := .BR (.mk_uN depth) :: after, vals := front ++ discarded ++ results } :: rest, []⟩
        ⟨s, ambient, { f with code := target.cont ++ target.after, labels := f.labels.drop (depth + 1), vals := front ++ results } :: rest, []⟩ ⦄ := by
  have allValues : ValuesAt exec.slots.val raw.base.val ((f.locals ++ front) ++ discarded ++ results) := by
    simpa only [FrameSlots, List.append_assoc] using slots
  have copied := ValuesAt.transfer allValues capacity
  have hs : raw.base.val + src.val + count.val ≤ exec.slots.length := by
    simpa only [source, size, List.map_append, Compiler.slots_append, Nat.add_assoc] using capacity
  have hd : raw.base.val + dst.val + count.val ≤ exec.slots.length := by
    simp only [destination, source, size, List.map_append, Compiler.slots_append] at hs ⊢
    omega
  have step : SourceMachine.astep
      ⟨s, ambient, { f with code := .BR (.mk_uN depth) :: after, vals := front ++ discarded ++ results } :: rest, []⟩ = .next
      ⟨s, ambient, { f with code := target.cont ++ target.after, labels := f.labels.drop (depth + 1), vals := front ++ results } :: rest, []⟩ := by
    have drop : (front ++ discarded ++ results).drop ((front ++ discarded ++ results).length - target.arity) = results := by
      rw [arity, List.length_append, Nat.add_sub_cancel]
      exact List.drop_left
    have take : (front ++ discarded ++ results).take target.height = front := by
      simp [height, List.append_assoc]
    have bound : target.height + target.arity ≤ (front ++ discarded ++ results).length := by
      simp only [height, arity, List.length_append]
      omega
    simp only [SourceMachine.astep, SourceMachine.branch, lookup, bound, drop, types, and_self, ↓reduceIte, take, SourceMachine.advance]
  have simulation := SourceMachine.instruction_simulation s ambient { f with vals := front ++ discarded ++ results } rest
    (.BR (.mk_uN depth)) after _ (.br _) typed step
  apply WP.spec_mono (dispatch_transfer_effect memory hooks floats allocator exec store platform
    frameIndex raw.instance raw.function raw.base dst src count hs hd)
  intro out effect
  obtain ⟨success, ⟨written, unchanged⟩, sameStore, samePlatform⟩ := effect
  refine ⟨success, ?_, unchanged, sameStore, samePlatform, simulation⟩
  simp only [FrameSlots, written]
  simpa only [destination, source, size, List.append_assoc] using copied

end Itasca.Runtime.Interp

end

/-! ## Branch No Copy -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem branch_no_transfer {locals front discarded results : List val} {dst src count : U32}
    (destination : dst.val = Compiler.slots ((locals ++ front).map Compiler.valueType))
    (source : src.val = Compiler.slots ((locals ++ front ++ discarded).map Compiler.valueType))
    (size : count.val = Compiler.slots (results.map Compiler.valueType))
    (elided : count = 0#u32 ∨ src = dst) :
    Compiler.slots (results.map Compiler.valueType) = 0 ∨ Compiler.slots (discarded.map Compiler.valueType) = 0 := by
  rcases elided with zero | same
  · left
    rw [zero] at size
    exact size.symm
  · right
    have equal := congrArg UScalar.val same
    simp only [source, destination, List.map_append, Compiler.slots_append] at equal
    omega

theorem ValuesAt.elide_transfer {words : List U64} {base : Nat} {front discarded results : List val}
    (live : ValuesAt words base (front ++ discarded ++ results))
    (noCopy : Compiler.slots (results.map Compiler.valueType) = 0 ∨ Compiler.slots (discarded.map Compiler.valueType) = 0) :
    ValuesAt words base (front ++ results) := by
  rcases noCopy with empty | same
  · have length := Compiler.length_le_slots (results.map Compiler.valueType)
    have nil : results = [] := by apply List.eq_nil_of_length_eq_zero; simp only [List.length_map] at length; omega
    subst results
    have h : ValuesAt words base (front ++ discarded) := by simpa only [List.append_nil] using live
    simpa only [List.append_nil] using h.locals
  · have length := Compiler.length_le_slots (discarded.map Compiler.valueType)
    have nil : discarded = [] := by apply List.eq_nil_of_length_eq_zero; simp only [List.length_map] at length; omega
    subst discarded
    simpa only [List.append_nil] using live

theorem branch_source_step (s : _root_.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (depth : Nat) (target : SourceMachine.Label) (front discarded results : List val)
    (lookup : f.labels[depth]? = some target) (height : target.height = front.length)
    (arity : target.arity = results.length) (types : results.map SourceMachine.valueType = target.branchTypes) :
    SourceMachine.astep
      ⟨s, ambient, { f with code := .BR (.mk_uN depth) :: after, vals := front ++ discarded ++ results } :: rest, []⟩ = .next
      ⟨s, ambient, { f with code := target.cont ++ target.after, labels := f.labels.drop (depth + 1), vals := front ++ results } :: rest, []⟩ := by
  have drop : (front ++ discarded ++ results).drop ((front ++ discarded ++ results).length - target.arity) = results := by
    rw [arity, List.length_append, Nat.add_sub_cancel]
    exact List.drop_left
  have take : (front ++ discarded ++ results).take target.height = front := by
    simp [height, List.append_assoc]
  have bound : target.height + target.arity ≤ (front ++ discarded ++ results).length := by
    simp only [height, arity, List.length_append]
    omega
  simp only [SourceMachine.astep, SourceMachine.branch, lookup, bound, drop, types, and_self, ↓reduceIte, take, SourceMachine.advance]

theorem step_branch_no_copy_refines {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex : Usize) (raw : runtime.interp.Frame) (targetPC : U32)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (s : _root_.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (depth : Nat) (target : SourceMachine.Label) (front discarded results : List val)
    (last : frameIndex.val + 1 = exec.frames.length)
    (frameLookup : exec.frames.val[frameIndex.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (fetched : compiled.code.val[raw.pc.val]? = some (.Jump targetPC))
    (lookup : f.labels[depth]? = some target) (height : target.height = front.length)
    (arity : target.arity = results.length) (types : results.map SourceMachine.valueType = target.branchTypes)
    (noCopy : Compiler.slots (results.map Compiler.valueType) = 0 ∨ Compiler.slots (discarded.map Compiler.valueType) = 0)
    (typed : SourceMachine.ATyped ⟨s, ambient, { f with code := .BR (.mk_uN depth) :: after, vals := front ++ discarded ++ results } :: rest, []⟩)
    (slots : FrameSlots exec raw { f with vals := front ++ discarded ++ results }) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out => out.1 = .Ok () ∧
      out.2.1 = { exec with frames := exec.frames.set frameIndex { raw with pc := targetPC } } ∧
      FrameSlots out.2.1 { raw with pc := targetPC }
        { f with code := target.cont ++ target.after, labels := f.labels.drop (depth + 1), vals := front ++ results } ∧
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      SourceMachine.NextSim
        ⟨s, ambient, { f with code := .BR (.mk_uN depth) :: after, vals := front ++ discarded ++ results } :: rest, []⟩
        ⟨s, ambient, { f with code := target.cont ++ target.after, labels := f.labels.drop (depth + 1), vals := front ++ results } :: rest, []⟩ ⦄ := by
  have allValues : ValuesAt exec.slots.val raw.base.val ((f.locals ++ front) ++ discarded ++ results) := by
    simpa only [FrameSlots, List.append_assoc] using slots
  have represented := allValues.elide_transfer noCopy
  have step := branch_source_step s ambient f rest after depth target front discarded results lookup height arity types
  have simulation := SourceMachine.instruction_simulation s ambient { f with vals := front ++ discarded ++ results } rest
    (.BR (.mk_uN depth)) after _ (.br _) typed step
  apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform
    frameIndex raw inst compiled targetPC last frameLookup hi hc pcBound fetched)
  intro out effect
  obtain ⟨success, exactState, sameStore, samePlatform⟩ := effect
  refine ⟨success, exactState, ?_, sameStore, samePlatform, simulation⟩
  rw [exactState]
  simpa only [FrameSlots, List.append_assoc] using represented

end Itasca.Runtime.Interp

end

end

/-! ## BranchCondition -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem branch_if_source_step (s : _root_.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (depth : Nat) (front : List val) (value : Nat) (bound : value < 2 ^ 32) :
    SourceMachine.astep
      ⟨s, ambient, { f with code := .BR_IF (.mk_uN depth) :: after, vals := front ++ [SourceMachine.integerVal .I32 value] } :: rest, []⟩ = .next
      ⟨s, ambient, { f with code := if value = 0 then after else .BR (.mk_uN depth) :: after, vals := front } :: rest, []⟩ := by
  have hb : value < 4294967296 := bound
  simp [SourceMachine.astep, SourceMachine.pop_append, SourceMachine.integerVal, SourceMachine.integer, numtype_Inn, hb, SourceMachine.advance]

def branchIfFrame (f : SourceMachine.AFrame) (after : List instr) (depth : Nat) (label : SourceMachine.Label)
    (front discarded results : List val) (value : Nat) : SourceMachine.AFrame :=
  if value = 0 then { f with code := after, vals := front ++ discarded ++ results }
  else { f with code := label.cont ++ label.after, labels := f.labels.drop (depth + 1), vals := front ++ results }

/-- A direct conditional branch may fuse the source BR_IF test and BR transfer.
Both reductions are derived from the generated source typing invariant. -/
theorem branch_if_source_refines (s : _root_.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (depth : Nat) (label : SourceMachine.Label) (front discarded results : List val) (value : Nat)
    (bound : value < 2 ^ 32) (lookup : f.labels[depth]? = some label)
    (height : label.height = front.length) (arity : label.arity = results.length)
    (types : results.map SourceMachine.valueType = label.branchTypes)
    (typed : SourceMachine.ATyped ⟨s, ambient, { f with code := .BR_IF (.mk_uN depth) :: after, vals := front ++ discarded ++ results ++ [SourceMachine.integerVal .I32 value] } :: rest, []⟩) :
    SourceMachine.ATyped ⟨s, ambient, branchIfFrame f after depth label front discarded results value :: rest, []⟩ ∧
    SourceMachine.NextSim
      ⟨s, ambient, { f with code := .BR_IF (.mk_uN depth) :: after, vals := front ++ discarded ++ results ++ [SourceMachine.integerVal .I32 value] } :: rest, []⟩
      ⟨s, ambient, branchIfFrame f after depth label front discarded results value :: rest, []⟩ := by
  have step := branch_if_source_step s ambient f rest after depth (front ++ discarded ++ results) value bound
  have typedNext := SourceMachine.instruction_preservation s ambient
    { f with vals := front ++ discarded ++ results ++ [SourceMachine.integerVal .I32 value] } rest
    (.BR_IF (.mk_uN depth)) after _ (.br_if _) typed step
  have simulation := SourceMachine.instruction_simulation s ambient
    { f with vals := front ++ discarded ++ results ++ [SourceMachine.integerVal .I32 value] } rest
    (.BR_IF (.mk_uN depth)) after _ (.br_if _) typed step
  by_cases zero : value = 0
  · simpa only [branchIfFrame, if_pos zero] using And.intro typedNext simulation
  · simp only [if_neg zero] at typedNext simulation
    have branch := branch_source_step s ambient f rest after depth label front discarded results lookup height arity types
    have typedBranch := SourceMachine.instruction_preservation s ambient { f with vals := front ++ discarded ++ results } rest
      (.BR (.mk_uN depth)) after _ (.br _) typedNext branch
    have branchSim := SourceMachine.instruction_simulation s ambient { f with vals := front ++ discarded ++ results } rest
      (.BR (.mk_uN depth)) after _ (.br _) typedNext branch
    simpa only [branchIfFrame, if_neg zero] using And.intro typedBranch (simulation.trans branchSim)

/-- When the compiler omits the transfer, JumpIfNonZero implements the complete
conditional branch while retaining untouched dead operand words. -/
theorem dispatch_branch_if_no_copy_refines {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (cond target : U32) (value : Nat)
    (s : _root_.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (depth : Nat) (label : SourceMachine.Label) (front discarded results : List val)
    (frameLookup : exec.frames.val[index.val]? = some raw)
    (bound : value < 2 ^ 32) (lookup : f.labels[depth]? = some label)
    (height : label.height = front.length) (arity : label.arity = results.length)
    (types : results.map SourceMachine.valueType = label.branchTypes)
    (noCopy : Compiler.slots (results.map Compiler.valueType) = 0 ∨ Compiler.slots (discarded.map Compiler.valueType) = 0)
    (position : cond.val = Compiler.slots ((f.locals ++ front ++ discarded ++ results).map Compiler.valueType))
    (typed : SourceMachine.ATyped ⟨s, ambient, { f with code := .BR_IF (.mk_uN depth) :: after, vals := front ++ discarded ++ results ++ [SourceMachine.integerVal .I32 value] } :: rest, []⟩)
    (slots : FrameSlots exec raw { f with vals := front ++ discarded ++ results ++ [SourceMachine.integerVal .I32 value] }) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index
      raw.instance raw.function raw.base (.JumpIfNonZero cond target) ⦃ out => out.1 = .Ok () ∧
      out.2.1 = (if value = 0 then exec else { exec with frames := exec.frames.set index { raw with pc := target } }) ∧
      FrameSlots out.2.1 raw (branchIfFrame f after depth label front discarded results value) ∧
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      SourceMachine.ATyped ⟨s, ambient, branchIfFrame f after depth label front discarded results value :: rest, []⟩ ∧
      SourceMachine.NextSim
        ⟨s, ambient, { f with code := .BR_IF (.mk_uN depth) :: after, vals := front ++ discarded ++ results ++ [SourceMachine.integerVal .I32 value] } :: rest, []⟩
        ⟨s, ambient, branchIfFrame f after depth label front discarded results value :: rest, []⟩ ⦄ := by
  have allValues : ValuesAt exec.slots.val raw.base.val ((f.locals ++ front ++ discarded ++ results) ++ [SourceMachine.integerVal .I32 value]) := by
    simpa only [FrameSlots, List.append_assoc] using slots
  have input : WordsAt exec.slots.val (raw.base.val + cond.val) [value] := by
    simpa only [position, ValuesAt, Compiler.encodeValues, List.flatMap_cons, List.flatMap_nil,
      SourceMachine.integerVal, Compiler.encodeValue, List.append_nil] using allValues.operands
  have reduced := allValues.locals.elide_transfer (front := f.locals ++ front) (discarded := discarded) (results := results) noCopy
  obtain ⟨typedNext, simulation⟩ := branch_if_source_refines s ambient f rest after depth label front discarded results value
    bound lookup height arity types typed
  apply WP.spec_mono (dispatch_jump_if_non_zero_exact memory hooks floats allocator exec store platform index raw cond target value
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

end

/-! ## BranchConditionStep -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem frame_set_twice (frames : alloc.vec.Vec runtime.interp.Frame) (index : Usize)
    (raw : runtime.interp.Frame) (first second : U32) :
    (frames.set index { raw with pc := first }).set index { raw with pc := second } =
      frames.set index { raw with pc := second } := by
  apply alloc.vec.Vec.ext
  simp only [alloc.vec.Vec.set_val_eq, List.set_set]

theorem step_branch_guard_refines {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (cond target : U32) (value : Nat)
    (s : _root_.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (depth : Nat) (front : List val)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (fetched : compiled.code.val[raw.pc.val]? = some (.JumpIfZero cond target))
    (bound : value < 2 ^ 32)
    (position : cond.val = Compiler.slots ((f.locals ++ front).map Compiler.valueType))
    (typed : SourceMachine.ATyped ⟨s, ambient, { f with code := .BR_IF (.mk_uN depth) :: after, vals := front ++ [SourceMachine.integerVal .I32 value] } :: rest, []⟩)
    (slots : FrameSlots exec raw { f with vals := front ++ [SourceMachine.integerVal .I32 value] }) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      FrameSlots out.2.1 raw { f with code := if value = 0 then after else .BR (.mk_uN depth) :: after, vals := front } ∧
      (∃ pc : U32, pc.val = raw.pc.val + 1 ∧
        out.2.1 = { exec with frames := exec.frames.set index { raw with pc := if value = 0 then target else pc } }) ∧
      SourceMachine.NextSim
        ⟨s, ambient, { f with code := .BR_IF (.mk_uN depth) :: after, vals := front ++ [SourceMachine.integerVal .I32 value] } :: rest, []⟩
        ⟨s, ambient, { f with code := if value = 0 then after else .BR (.mk_uN depth) :: after, vals := front } :: rest, []⟩ ⦄ := by
  apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
    (.JumpIfZero cond target) last hf hi hc fetched pcBound
  intro pc hpc
  have valid : index.val < exec.frames.val.length := List.getElem?_eq_some_iff.mp hf |>.1
  have lookup : (exec.frames.set index { raw with pc := pc }).val[index.val]? = some { raw with pc := pc } := by
    simp [alloc.vec.Vec.set_val_eq, valid]
  apply WP.spec_mono (dispatch_branch_guard_refines memory hooks floats allocator
    { exec with frames := exec.frames.set index { raw with pc := pc } } store platform index
    { raw with pc := pc } cond target value s ambient f rest after depth front lookup bound position typed slots)
  intro out effect
  obtain ⟨success, exactState, represented, sameStore, samePlatform, simulation⟩ := effect
  refine ⟨success, sameStore, samePlatform, represented, ⟨pc, hpc, ?_⟩, simulation⟩
  by_cases zero : value = 0
  · simpa only [if_pos zero, frame_set_twice] using exactState
  · simpa only [if_neg zero] using exactState

theorem step_branch_if_no_copy_refines {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (cond target : U32) (value : Nat)
    (s : _root_.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (depth : Nat) (label : SourceMachine.Label) (front discarded results : List val)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (fetched : compiled.code.val[raw.pc.val]? = some (.JumpIfNonZero cond target))
    (bound : value < 2 ^ 32) (lookup : f.labels[depth]? = some label)
    (height : label.height = front.length) (arity : label.arity = results.length)
    (types : results.map SourceMachine.valueType = label.branchTypes)
    (noCopy : Compiler.slots (results.map Compiler.valueType) = 0 ∨ Compiler.slots (discarded.map Compiler.valueType) = 0)
    (position : cond.val = Compiler.slots ((f.locals ++ front ++ discarded ++ results).map Compiler.valueType))
    (typed : SourceMachine.ATyped ⟨s, ambient, { f with code := .BR_IF (.mk_uN depth) :: after, vals := front ++ discarded ++ results ++ [SourceMachine.integerVal .I32 value] } :: rest, []⟩)
    (slots : FrameSlots exec raw { f with vals := front ++ discarded ++ results ++ [SourceMachine.integerVal .I32 value] }) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      FrameSlots out.2.1 raw (branchIfFrame f after depth label front discarded results value) ∧
      (∃ pc : U32, pc.val = raw.pc.val + 1 ∧
        out.2.1 = { exec with frames := exec.frames.set index { raw with pc := if value = 0 then pc else target } }) ∧
      SourceMachine.ATyped ⟨s, ambient, branchIfFrame f after depth label front discarded results value :: rest, []⟩ ∧
      SourceMachine.NextSim
        ⟨s, ambient, { f with code := .BR_IF (.mk_uN depth) :: after, vals := front ++ discarded ++ results ++ [SourceMachine.integerVal .I32 value] } :: rest, []⟩
        ⟨s, ambient, branchIfFrame f after depth label front discarded results value :: rest, []⟩ ⦄ := by
  apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
    (.JumpIfNonZero cond target) last hf hi hc fetched pcBound
  intro pc hpc
  have valid : index.val < exec.frames.val.length := List.getElem?_eq_some_iff.mp hf |>.1
  have lookupFrame : (exec.frames.set index { raw with pc := pc }).val[index.val]? = some { raw with pc := pc } := by
    simp [alloc.vec.Vec.set_val_eq, valid]
  apply WP.spec_mono (dispatch_branch_if_no_copy_refines memory hooks floats allocator
    { exec with frames := exec.frames.set index { raw with pc := pc } } store platform index
    { raw with pc := pc } cond target value s ambient f rest after depth label front discarded results
    lookupFrame bound lookup height arity types noCopy position typed slots)
  intro out effect
  obtain ⟨success, exactState, represented, sameStore, samePlatform, typedNext, simulation⟩ := effect
  refine ⟨success, sameStore, samePlatform, represented, ⟨pc, hpc, ?_⟩, typedNext, simulation⟩
  by_cases zero : value = 0
  · simpa only [if_pos zero] using exactState
  · simpa only [if_neg zero, frame_set_twice] using exactState

end Itasca.Runtime.Interp

end

/-! ## LoopHead -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem dispatch_loop_head_eq {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform after : P)
    (index : Usize) (raw : runtime.interp.Frame) (decision : runtime.platform.InterruptAction)
    (hook : hooks.interrupt platform = .ok (decision, after)) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index
      raw.instance raw.function raw.base .LoopHead = .ok (interruptResult decision, exec, store, after) := by
  simp only [runtime.interp.dispatch, runtime.interp.execute_loop_head,
    interrupt_eq memory hooks platform after decision hook, bind_ok]
  cases decision <;> simp [interruptResult, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame]

/-- LoopHead is exactly the interrupt boundary. It cannot mutate the store or
slot/frame state, and termination has an actual terminating hook witness. -/
theorem dispatch_loop_head_effect {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index
      raw.instance raw.function raw.base .LoopHead ⦃ out =>
      out.2.1 = exec ∧ out.2.2.1 = store ∧ ∃ decision,
      hooks.interrupt platform = .ok (decision, out.2.2.2) ∧ out.1 = interruptResult decision ⦄ := by
  obtain ⟨⟨decision, after⟩, hook, _⟩ := WP.spec_imp_exists (law platform)
  rw [dispatch_loop_head_eq memory hooks floats allocator exec store platform after index raw decision hook]
  exact ⟨rfl, rfl, decision, hook, rfl⟩

end Itasca.Runtime.Interp

end

/-! ## NormalizeCompose -/

section

namespace Itasca.Runtime.Interp

theorem ConcreteSim.trans {codeLength firstPC middlePC lastPC firstPending middlePending lastPending before middle after}
    (first : ConcreteSim codeLength firstPC middlePC firstPending middlePending before middle)
    (second : ConcreteSim codeLength middlePC lastPC middlePending lastPending middle after) :
    ConcreteSim codeLength firstPC lastPC firstPending lastPending before after := by
  rcases first with ⟨firstEq, firstDecrease⟩ | ⟨n, hn, firstSteps⟩
  · rcases second with ⟨secondEq, secondDecrease⟩ | ⟨m, hm, secondSteps⟩
    · exact Or.inl ⟨firstEq.trans secondEq, Nat.lt_trans secondDecrease firstDecrease⟩
    · exact Or.inr ⟨m, hm, by simpa only [firstEq] using secondSteps⟩
  · rcases second with ⟨secondEq, secondDecrease⟩ | ⟨m, hm, secondSteps⟩
    · exact Or.inr ⟨n, hn, by simpa only [secondEq] using firstSteps⟩
    · exact Or.inr ⟨n + m, by omega, by simpa using firstSteps.trans secondSteps⟩

/-- Source-only normalization can precede the real dispatch without losing
its measured stutter or positive counted reduction guarantee. -/
theorem ConcreteSim.prepend_normalization {count before middle} (chain : ErasedSteps count before middle)
    (s : store) (ambient : frame) (rest : List SourceMachine.AFrame)
    (typed : SourceMachine.ATyped ⟨s, ambient, before :: rest, []⟩)
    {codeLength pc target pending after}
    (simulation : ConcreteSim codeLength pc target false pending
      ⟨s, ambient, middle :: rest, []⟩ after) :
    ConcreteSim codeLength pc target false pending ⟨s, ambient, before :: rest, []⟩ after := by
  rcases (chain.sound s ambient rest typed).2 with ⟨_, same⟩ | prefixSimulation
  · simpa only [same] using simulation
  · exact (ConcreteSim.of_source codeLength pc pc false false prefixSimulation).trans simulation

end Itasca.Runtime.Interp

end
