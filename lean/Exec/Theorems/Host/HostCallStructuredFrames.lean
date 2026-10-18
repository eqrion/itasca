import Exec.Theorems.Host.HostCallFrames
import Exec.Interp.StructuredMachine.HostReturnFrames

namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

theorem HostCallSourceOutcome.resume_structured_frames {emission : StructuredMachine.FunctionEmission} {M P : Type}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {before : runtime.store.Store M}
    {ambient : frame} {address : runtime.FuncAddr} {args : List val} {base : Usize}
    {exec : runtime.interp.Execution}
    {out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P}
    (observed : HostCallSourceOutcome view code before ambient address args base exec out)
    (success : out.1 = .Ok ())
    (retained : FrameStorePrefix before out.2.2.1) (bounds : FrameTypeBounds before)
    (extension : Extend_store (Store.decodeStore view code before) (Store.decodeStore view code out.2.2.1))
    {raw : runtime.interp.Frame} {raws : List runtime.interp.Frame}
    {caller : Abs.AFrame} {rest : List Abs.AFrame} {waiting : List valtype}
    (frames : exec.frames.val = raws.reverse ++ [raw])
    (saved : StructuredMachine.SavedFrame emission before (Store.decodeStore view code before) exec raw caller waiting base.val)
    (older : StructuredMachine.SavedFrames emission before (Store.decodeStore view code before) exec raws rest caller.resultTypes raw.base.val)
    (types : (out.2.1.host_results.val.map sourceValue).map Code.valueType = waiting)
    (heights : Abs.FrameHeights caller) :
    StructuredMachine.FrameStackRel emission out.2.2.1 (Store.decodeStore view code out.2.2.1) out.2.1
      ({caller with vals := caller.vals ++ out.2.1.host_results.val.map sourceValue} :: rest) ∧
      StructuredMachine.ReadyTop emission out.2.2.1 (Store.decodeStore view code out.2.2.1) out.2.1 {caller with vals := caller.vals ++ out.2.1.host_results.val.map sourceValue} :=
  StructuredMachine.host_return_stack_extended retained bounds extension frames saved older (observed.return_effect success) types heights

end Exec.Theorems
