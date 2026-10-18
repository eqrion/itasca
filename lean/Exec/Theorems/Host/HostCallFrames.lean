import Exec.Theorems.Host.HostCallSource
import Exec.Interp.Host.HostReturnFrames

namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Successful actual host calls supply the concrete slot/frame transport used
when resuming a caller; no callback behavior is hidden in that transport. -/
theorem HostCallSourceOutcome.return_effect {M P : Type}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {before : runtime.store.Store M}
    {ambient : frame} {address : runtime.FuncAddr} {args : List val} {base : Usize}
    {exec : runtime.interp.Execution}
    {out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P}
    (observed : HostCallSourceOutcome view code before ambient address args base exec out)
    (success : out.1 = .Ok ()) :
    HostReturnEffect exec out.2.1 base.val (out.2.1.host_results.val.map sourceValue) := by
  obtain ⟨arguments,frames,identity,capacity,outcome⟩ := observed
  rcases outcome with returned | failed
  · obtain ⟨_,values,source,preserved⟩ := returned
    exact ⟨identity,frames,capacity,values,fun j bound below => preserved j bound (Or.inl below)⟩
  · rcases failed.1 with status | status <;> rw [success] at status <;> cases status

/-- The callback's checked result resumes all concrete callers provided their
raw metadata survived. The latter is an explicit transport premise and is not
derived from decoded store extension. -/
theorem HostCallSourceOutcome.resume_frames {M P : Type}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {before : runtime.store.Store M}
    {ambient : frame} {address : runtime.FuncAddr} {args : List val} {base : Usize}
    {exec : runtime.interp.Execution}
    {out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P}
    (observed : HostCallSourceOutcome view code before ambient address args base exec out)
    (success : out.1 = .Ok ())
    (retained : FrameStorePrefix before out.2.2.1) (bounds : FrameTypeBounds before)
    {raw : runtime.interp.Frame} {raws : List runtime.interp.Frame}
    {caller : Abs.AFrame} {rest : List Abs.AFrame} {waiting : List valtype}
    (frames : exec.frames.val = raws.reverse ++ [raw])
    (saved : SavedFrame before exec raw caller waiting base.val)
    (older : SavedFrames before exec raws rest caller.resultTypes raw.base.val)
    (types : (out.2.1.host_results.val.map sourceValue).map Code.valueType = waiting)
    (heights : Abs.FrameHeights caller) :
    FrameStackRel out.2.2.1 out.2.1
      ({caller with vals := caller.vals ++ out.2.1.host_results.val.map sourceValue} :: rest) ∧
      ReadyTop out.2.2.1 out.2.1 {caller with vals := caller.vals ++ out.2.1.host_results.val.map sourceValue} :=
  host_return_stack_extended retained bounds frames saved older (observed.return_effect success) types heights
end Exec.Theorems
