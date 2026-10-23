import Exec.Interp.Relations.ConstCodePoint
import Exec.Interp.Relations.Fetch

namespace Exec.Interp
open Aeneas Aeneas.Std
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem step_const32_certified
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (next : Nat) (output : List valtype) (s : _root_.store) (ambient : frame) (f : Abs.AFrame)
    (rest : List Abs.AFrame) (after : List instr) (value : U32)
    (last : frameIndex.val + 1 = exec.frames.length)
    (hf : exec.frames.val[frameIndex.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some code)
    (pcBound : raw.pc.val < U32.max)
    (typed : Abs.ATyped ⟨s, ambient, { f with code := .CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) :: after } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (capacity : raw.base.val + Code.slots ((f.locals ++ f.vals).map Code.valueType) < exec.slots.length)
    (point : LinearPoint raw { f with code := .CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) :: after } code next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧
      FrameSlots out.2.1 raw { f with code := after, vals := f.vals ++ [Abs.integerVal .I32 value.val] } ∧
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      (∃ pc : U32, pc.val = raw.pc.val + 1 ∧
        { out.2.1 with slots := exec.slots } =
          { exec with frames := exec.frames.set frameIndex { raw with pc := pc } } ∧
        LinearPoint { raw with pc := pc } { f with code := after, vals := f.vals ++ [Abs.integerVal .I32 value.val] } code next output) ∧
      Abs.NextSim
        ⟨s, ambient, { f with code := .CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) :: after } :: rest, []⟩
        ⟨s, ambient, { f with code := after, vals := f.vals ++ [Abs.integerVal .I32 value.val] } :: rest, []⟩ ⦄ := by
  obtain ⟨dst, destination, fetched, continuation⟩ := linearPoint_const32 value after point
  apply step_fetch memory hooks floats allocator exec store platform frameIndex raw inst code
    (.Const32 dst value) last hf hi hc fetched pcBound
  intro pc hpc
  apply WP.spec_mono (dispatch_const32_refines memory hooks floats allocator
    { exec with frames := exec.frames.set frameIndex { raw with pc := pc } }
    store platform frameIndex raw dst value s ambient f rest after
    typed slots destination (by simpa only [destination] using capacity))
  intro out effect
  obtain ⟨success, represented, unchanged, sameStore, samePlatform, simulation⟩ := effect
  refine ⟨success, represented, sameStore, samePlatform, ⟨pc, hpc, unchanged, ?_⟩, simulation⟩
  simpa only [LinearPoint, hpc] using continuation

theorem step_const64_certified
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (next : Nat) (output : List valtype) (s : _root_.store) (ambient : frame) (f : Abs.AFrame)
    (rest : List Abs.AFrame) (after : List instr) (value : U64)
    (last : frameIndex.val + 1 = exec.frames.length)
    (hf : exec.frames.val[frameIndex.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some code)
    (pcBound : raw.pc.val < U32.max)
    (typed : Abs.ATyped ⟨s, ambient, { f with code := .CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) :: after } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (capacity : raw.base.val + Code.slots ((f.locals ++ f.vals).map Code.valueType) < exec.slots.length)
    (point : LinearPoint raw { f with code := .CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) :: after } code next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧
      FrameSlots out.2.1 raw { f with code := after, vals := f.vals ++ [Abs.integerVal .I64 value.val] } ∧
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      (∃ pc : U32, pc.val = raw.pc.val + 1 ∧
        { out.2.1 with slots := exec.slots } =
          { exec with frames := exec.frames.set frameIndex { raw with pc := pc } } ∧
        LinearPoint { raw with pc := pc } { f with code := after, vals := f.vals ++ [Abs.integerVal .I64 value.val] } code next output) ∧
      Abs.NextSim
        ⟨s, ambient, { f with code := .CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) :: after } :: rest, []⟩
        ⟨s, ambient, { f with code := after, vals := f.vals ++ [Abs.integerVal .I64 value.val] } :: rest, []⟩ ⦄ := by
  obtain ⟨dst, destination, fetched, continuation⟩ := linearPoint_const64 value after point
  apply step_fetch memory hooks floats allocator exec store platform frameIndex raw inst code
    (.Const64 dst value) last hf hi hc fetched pcBound
  intro pc hpc
  apply WP.spec_mono (dispatch_const64_refines memory hooks floats allocator
    { exec with frames := exec.frames.set frameIndex { raw with pc := pc } }
    store platform frameIndex raw dst value s ambient f rest after
    typed slots destination (by simpa only [destination] using capacity))
  intro out effect
  obtain ⟨success, represented, unchanged, sameStore, samePlatform, simulation⟩ := effect
  refine ⟨success, represented, sameStore, samePlatform, ⟨pc, hpc, unchanged, ?_⟩, simulation⟩
  simpa only [LinearPoint, hpc] using continuation

end Exec.Interp
