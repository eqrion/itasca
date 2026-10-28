import Exec.Abs.Indirect.Definition
import Exec.Abs.Indirect.Operands
namespace Itasca.Runtime.Abs.Indirect
open SpecExt Itasca.Runtime.Spec

theorem type_selected {s : store} {f : AFrame} {C : context} {type : Nat} {signature : functype}
    (bindings : ModuleBindings s f.module C) (selected : C.TYPES[type]?=some signature) :
    fun_type ⟨s,f.toFrame⟩ (.mk_uN type)=signature := by
  simp only [fun_type,AFrame.toFrame,proj_uN_0,←bindings.types,List.getElem!_eq_getElem?_getD,selected,Option.getD_some]

end Itasca.Runtime.Abs.Indirect
