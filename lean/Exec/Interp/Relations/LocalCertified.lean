import Exec.Interp.Relations.LocalCodePoint
import Exec.Interp.Relations.Fetch

/-! Complete extracted local-variable iterations. The retained source/code
certificate supplies the fetched instruction and exact word offsets. -/
namespace Exec.Interp
open Aeneas Aeneas.Std
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem step_localGet_certified
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.Instance) (code : runtime.bytecode.CompiledFunction)
    (next : Nat) (output : List valtype) (s : _root_.store) (ambient : frame) (f : Abs.AFrame)
    (rest : List Abs.AFrame) (after : List instr) (index : U32) (value : val)
    (last : frameIndex.val + 1 = exec.frames.length)
    (hf : exec.frames.val[frameIndex.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some code)
    (pcBound : raw.pc.val < U32.max)
    (lookup : f.locals[index.val]? = some value)
    (typed : Abs.ATyped ⟨s, ambient, { f with code := .LOCAL_GET (.mk_uN index.val) :: after } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (capacity : raw.base.val + Code.slots ((f.locals ++ f.vals).map Code.valueType) +
      Code.width (Code.valueType value) ≤ exec.slots.length)
    (point : LinearPoint raw { f with code := .LOCAL_GET (.mk_uN index.val) :: after } code next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧
      FrameSlots out.2.1 raw { f with code := after, vals := f.vals ++ [value] } ∧
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      (∃ pc : U32, pc.val = raw.pc.val + 1 ∧
        { out.2.1 with slots := exec.slots } =
          { exec with frames := exec.frames.set frameIndex { raw with pc := pc } } ∧
        LinearPoint { raw with pc := pc } { f with code := after, vals := f.vals ++ [value] } code next output) ∧
      Abs.NextSim
        ⟨s, ambient, { f with code := .LOCAL_GET (.mk_uN index.val) :: after } :: rest, []⟩
        ⟨s, ambient, { f with code := after, vals := f.vals ++ [value] } :: rest, []⟩ ⦄ := by
  obtain ⟨src, dst, source, destination, fetched, continuation⟩ := linearPoint_localGet index.val value after lookup point
  apply step_fetch memory hooks floats allocator exec store platform frameIndex raw inst code
    (Code.move (Code.valueType value) dst src) last hf hi hc fetched pcBound
  intro pc hpc
  apply WP.spec_mono (dispatch_localGet_refines memory hooks floats allocator
    { exec with frames := exec.frames.set frameIndex { raw with pc := pc } }
    store platform frameIndex raw index src dst s ambient f rest after f.vals value lookup
    typed slots source destination (by simpa only [destination] using capacity))
  intro out effect
  obtain ⟨success, represented, unchanged, sameStore, samePlatform, simulation⟩ := effect
  refine ⟨success, represented, sameStore, samePlatform, ⟨pc, hpc, unchanged, ?_⟩, simulation⟩
  simpa only [LinearPoint, hpc] using continuation

theorem step_localWrite_certified
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.Instance) (code : runtime.bytecode.CompiledFunction)
    (next : Nat) (output : List valtype) (s : _root_.store) (ambient : frame) (f : Abs.AFrame)
    (rest : List Abs.AFrame) (after : List instr) (index : U32) (keep : Bool)
    (front : List val) (value old : val)
    (last : frameIndex.val + 1 = exec.frames.length)
    (hf : exec.frames.val[frameIndex.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some code)
    (pcBound : raw.pc.val < U32.max)
    (lookup : f.locals[index.val]? = some old)
    (typed : Abs.ATyped ⟨s, ambient, { f with
      code := (if keep then .LOCAL_TEE (.mk_uN index.val) else .LOCAL_SET (.mk_uN index.val)) :: after, vals := front ++ [value] } :: rest, []⟩)
    (slots : FrameSlots exec raw { f with vals := front ++ [value] })
    (point : LinearPoint raw { f with
      code := (if keep then .LOCAL_TEE (.mk_uN index.val) else .LOCAL_SET (.mk_uN index.val)) :: after, vals := front ++ [value] } code next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧
      FrameSlots out.2.1 raw { f with code := after, locals := f.locals.set index.val value, vals := if keep then front ++ [value] else front } ∧
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      (∃ pc : U32, pc.val = raw.pc.val + 1 ∧
        { out.2.1 with slots := exec.slots } =
          { exec with frames := exec.frames.set frameIndex { raw with pc := pc } } ∧
        LinearPoint { raw with pc := pc } { f with code := after, locals := f.locals.set index.val value, vals := if keep then front ++ [value] else front } code next output) ∧
      Abs.NextSim
        ⟨s, ambient, { f with code := (if keep then .LOCAL_TEE (.mk_uN index.val) else .LOCAL_SET (.mk_uN index.val)) :: after, vals := front ++ [value] } :: rest, []⟩
        ⟨s, ambient, { f with code := after, locals := f.locals.set index.val value, vals := if keep then front ++ [value] else front } :: rest, []⟩ ⦄ := by
  obtain ⟨src, dst, compatible, source, destination, fetched, continuation⟩ :=
    linearPoint_localWrite index.val keep front value old after lookup point
  apply step_fetch memory hooks floats allocator exec store platform frameIndex raw inst code
    (Code.move (Code.valueType value) dst src) last hf hi hc fetched pcBound
  intro pc hpc
  apply WP.spec_mono (dispatch_localWrite_refines memory hooks floats allocator
    { exec with frames := exec.frames.set frameIndex { raw with pc := pc } }
    store platform frameIndex raw index src dst keep s ambient f rest after front value old lookup
    compatible typed slots source destination)
  intro out effect
  obtain ⟨success, represented, unchanged, sameStore, samePlatform, simulation⟩ := effect
  refine ⟨success, represented, sameStore, samePlatform, ⟨pc, hpc, unchanged, ?_⟩, simulation⟩
  simpa only [LinearPoint, hpc] using continuation

end Exec.Interp
