import Itasca.Runtime.Interp.Control.BranchCondition
import Itasca.Runtime.Interp.Relations.ControlPoint

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
