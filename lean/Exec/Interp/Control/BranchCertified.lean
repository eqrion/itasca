import Exec.Interp.Control.BranchTransfer
import Exec.Interp.Control.PendingJump

namespace Exec.Interp
open Aeneas Aeneas.Std

/-- Exact branch-pair evidence. This is a data relation for emitted code and
slot addresses; compiler correctness must construct it from lowering. -/
structure BranchLinearPoint (raw : runtime.interp.Frame) (f : Abs.AFrame)
    (compiled : runtime.bytecode.CompiledFunction) (depth : Nat) (target : Abs.Label)
    (front discarded results : List val) (dst src count targetPC : U32)
    (next : Nat) (output : List valtype) : Prop where
  destination : dst.val = Code.slots ((f.locals ++ front).map Code.valueType)
  source : src.val = Code.slots ((f.locals ++ front ++ discarded).map Code.valueType)
  size : count.val = Code.slots (results.map Code.valueType)
  transfer : compiled.code.val[raw.pc.val]? = some (transferInstruction dst src count)
  jump : compiled.code.val[raw.pc.val + 1]? = some (.Jump targetPC)
  continuation : LinearPoint { raw with pc := targetPC }
    { f with code := target.cont ++ target.after, labels := f.labels.drop (depth + 1), vals := front ++ results }
    compiled next output

/-- First half of a concrete branch: fetch, copy results and enter the pending
jump phase after the positive source branch reduction. -/
theorem step_branchTransfer_certified {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
    (dst src count targetPC : U32) (next : Nat) (output : List valtype)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr) (depth : Nat) (target : Abs.Label)
    (front discarded results : List val)
    (last : frameIndex.val + 1 = exec.frames.length)
    (hf : exec.frames.val[frameIndex.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (lookup : f.labels[depth]? = some target)
    (height : target.height = front.length)
    (arity : target.arity = results.length)
    (types : results.map Abs.valueType = target.branchTypes)
    (typed : Abs.ATyped ⟨s, ambient, { f with code := .BR (.mk_uN depth) :: after, vals := front ++ discarded ++ results } :: rest, []⟩)
    (slots : FrameSlots exec raw { f with vals := front ++ discarded ++ results })
    (capacity : raw.base.val + Code.slots ((f.locals ++ front ++ discarded ++ results).map Code.valueType) ≤ exec.slots.length)
    (point : BranchLinearPoint raw f compiled depth target front discarded results dst src count targetPC next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧
      FrameSlots out.2.1 raw { f with code := target.cont ++ target.after, labels := f.labels.drop (depth + 1), vals := front ++ results } ∧
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      (∃ pc : U32, pc.val = raw.pc.val + 1 ∧
        { out.2.1 with slots := exec.slots } =
          { exec with frames := exec.frames.set frameIndex { raw with pc := pc } } ∧
        PendingLinearJump { raw with pc := pc }
          { f with code := target.cont ++ target.after, labels := f.labels.drop (depth + 1), vals := front ++ results }
          compiled targetPC next output) ∧
      Abs.NextSim
        ⟨s, ambient, { f with code := .BR (.mk_uN depth) :: after, vals := front ++ discarded ++ results } :: rest, []⟩
        ⟨s, ambient, { f with code := target.cont ++ target.after, labels := f.labels.drop (depth + 1), vals := front ++ results } :: rest, []⟩ ⦄ := by
  apply step_fetch memory hooks floats allocator exec store platform frameIndex raw inst compiled
    (transferInstruction dst src count) last hf hi hc point.transfer pcBound
  intro pc hpc
  apply WP.spec_mono (dispatch_branchTransfer_refines memory hooks floats allocator
    { exec with frames := exec.frames.set frameIndex { raw with pc := pc } }
    store platform frameIndex raw dst src count s ambient f rest after depth target front discarded results
    lookup height arity types typed slots point.destination point.source point.size capacity)
  intro out effect
  obtain ⟨success, represented, unchanged, sameStore, samePlatform, simulation⟩ := effect
  refine ⟨success, represented, sameStore, samePlatform, ⟨pc, hpc, unchanged, ?_⟩, simulation⟩
  exact ⟨by simpa only [hpc] using point.jump, point.continuation⟩

end Exec.Interp
