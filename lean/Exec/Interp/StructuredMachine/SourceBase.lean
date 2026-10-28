import Exec.Interp.StructuredMachine.StructuredCall
namespace Itasca.Runtime.Interp.StructuredMachine
open Aeneas Aeneas.Std

theorem FrameStackRel.source_base {M : Type}
    {store : runtime.store.Store M} {sourceStore : _root_.store} {exec : runtime.interp.Execution}
    {f : Abs.AFrame} {rest : List Abs.AFrame} (stack : FrameStackRel store sourceStore exec (f::rest))
    {raw : runtime.interp.Frame} {index : Usize}
    (last : index.val+1=exec.frames.length) (found : exec.frames.val[index.val]?=some raw) :
    raw.base.val=suspendedSourceWords rest := by
  cases stack with
  | @active actual _ raws _ frames active saved =>
    have same : actual=raw := by
      have top : exec.frames.val.getLast?=some raw := by
        rw [List.getLast?_eq_getElem?]
        have size : exec.frames.val.length-1=index.val := by change index.val+1=exec.frames.val.length at last;omega
        simpa only [size] using found
      simpa only [frames,List.getLast?_concat,Option.some.injEq] using top
    subst actual
    exact saved_source_base saved
end Itasca.Runtime.Interp.StructuredMachine
