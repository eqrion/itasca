import Exec.Abs.Indirect.Definition
import Exec.Abs.Indirect.Operands
namespace Exec.Abs.Indirect
open SpecExt Exec.Spec

theorem invoke_progress (s : AState) (f : AFrame) (rest : List AFrame) (address : Nat) (after : List instr)
    (fn : funcinst) (params results : List valtype) (front args : List val)
    (lookup : s.store.FUNCS[address]?=some fn) (signature : fn.TYPE=⟨.mk_list params,.mk_list results⟩)
    (values : f.vals=front++args) (arguments : ResultsTyped s.store params args)
    (functions : FunctionsTyped s.store) : invoke s f rest address after ≠ .stuck := by
  have types := results_type_of_typed arguments
  have lengthEq := resultsTyped_length arguments
  cases body : fn.CODE with
  | HOST host => simp [invoke,lookup,signature,values,←lengthEq,types,body]
  | FUNC index locals source =>
    obtain ⟨defaults,initial⟩ := function_defaults functions (List.mem_of_getElem? lookup) body
    simp [invoke,lookup,signature,values,←lengthEq,types,body,initial]

theorem type_selected {s : store} {f : AFrame} {C : context} {type : Nat} {signature : functype}
    (bindings : ModuleBindings s f.module C) (selected : C.TYPES[type]?=some signature) :
    fun_type ⟨s,f.toFrame⟩ (.mk_uN type)=signature := by
  simp only [fun_type,AFrame.toFrame,proj_uN_0,←bindings.types,List.getElem!_eq_getElem?_getD,selected,Option.getD_some]

theorem progress (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (table type : Nat) (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩) :
    step ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩ f rest table type after ≠ .stuck := by
  have frameTyped : FrameTyped s {f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,args,params,results,position,bindings,tableSelected,typeSelected,values,bounded,arguments,frontWf,heights,caller,tableBound,typeBound⟩ := operands frameTyped
  have decoded : integer numtype.I32 (integerVal .I32 position)=some position := integer_accepts .I32 position bounded
  cases resolved : resolve s f table type position with
  | none =>
    simp only [step,values,pop_append,decoded,resolved]
    intro impossible;cases impossible
  | some address =>
    obtain ⟨reference,fn,lookup,signature⟩ := (resolve_iff s f table type position address).mp resolved
    have actualType : fn.TYPE=⟨.mk_list params,.mk_list results⟩ := signature.symm.trans (type_selected bindings typeSelected)
    have safe := invoke_progress ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩
      {f with vals:=front++args} rest address after fn params results front args lookup actualType rfl arguments typed.typed.functions
    simpa only [step,values,pop_append,decoded,resolved] using safe
end Exec.Abs.Indirect
