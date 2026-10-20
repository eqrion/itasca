import Exec.Spec.Choices.ReadDeterminism
import Exec.Spec.Choices.ValuePrefixSyntax
namespace Exec.Spec
open SpecExt

private def lastOperationTag (body : List admininstr) : Option Nat :=
  body.getLast? |>.map admininstr.ctorIdx

theorem host_not_wasm {s : store} {f : frame} {address : funcaddr} {identity : Nat}
    {params results inputs outputs : List valtype} {object : moduleinst} {function : func}
    (host : HostFunction s address identity params results)
    (actual : (fun_funcinst ⟨s,f⟩)[address]! =
      ({TYPE := .mk_functype (.mk_list inputs) (.mk_list outputs),MODULE := object,CODE := funccode_func function} : funcinst)) : False := by
  obtain ⟨moduleObject,found⟩ := host
  have code := congrArg funcinst.CODE actual
  simp only [fun_funcinst,List.getElem!_eq_getElem?_getD,found,Option.getD_some] at code
  cases code

set_option maxHeartbeats 2000000 in
theorem read_not_host_call {s : store} {f : frame} {before after : List admininstr}
    {address : funcaddr} {identity : Nat} {params results : List valtype} {args : List val}
    (source : Step_read ⟨⟨s,f⟩,before⟩ after) (host : HostFunction s address identity params results)
    (same : before=vals args++[.CALL_ADDR address]) : False := by
  have last := congrArg lastOperationTag same
  cases source
  all_goals simp [lastOperationTag,admininstr.ctorIdx] at last
  have operands := value_prefix_unique (by rfl) (by rfl) same
  obtain ⟨_,addressEq,_⟩ := operands
  cases addressEq
  exact host_not_wasm host (by assumption)
end Exec.Spec
