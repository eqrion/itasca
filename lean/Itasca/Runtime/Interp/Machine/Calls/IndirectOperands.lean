import Itasca.Runtime.Interp.Machine.Coverage.Heads
import Itasca.Runtime.Interp.Machine.Calls.IndirectPoint
import Itasca.Runtime.Interp.Machine.Execution
import Itasca.Runtime.SourceMachine.Cumulative.Step
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulEmission
import Itasca.Runtime.SourceMachine.Indirect.Operands

/-!
Source operand values at an indirect-call instruction.

Main declarations: `indirect_values_head`. A direct consumer is `Integration.Execution.Dispatch.IndirectExecution`.
-/

namespace Itasca.Runtime.Interp.StructuredMachine
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Spec

theorem indirect_values_head {s : _root_.store} {raw : runtime.interp.Frame} {f : Abs.AFrame} {compiled : runtime.bytecode.CompiledFunction} {C targets next output}
    [IndirectProjection (emission compiled) compiled.indirect.val]
    (table type : Nat) (after : List instr)
    (point : FramePoint s raw {f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after} compiled C targets next output)
    (typed : Abs.FrameTyped s {f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after} []) :
    (∃ target : U32, raw.pc.val<target.val ∧ compiled.code.val[raw.pc.val]?=some (.Jump target) ∧
      FramePoint s {raw with pc:=target} {f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after} compiled C targets next output) ∨
    (∃ (front args : List val) (params results : List valtype) (position : Nat)
        (typeIndex tableIndex entry index base : U32) (bounds : limits),
      typeIndex.val=type ∧ tableIndex.val=table ∧
      f.vals=(front++args)++[Abs.integerVal .I32 position] ∧ position<2^32 ∧
      ResultsTyped s params args ∧ args.map Code.valueType=params ∧
      (∀ label∈f.labels,label.height≤front.length) ∧ Abs.FrameTyped s {f with code:=after,vals:=front} results ∧
      C.TYPES[type]?=some ⟨.mk_list params,.mk_list results⟩ ∧
      C.TABLES[table]?=some (.mk_tabletype bounds .FUNCREF) ∧
      compiled.indirect.val[entry.val]?=some (tableIndex,typeIndex) ∧
      base.val=Code.slots ((f.locals++front).map Code.valueType) ∧ index.val=base.val+Code.slots params ∧
      compiled.code.val[raw.pc.val]?=some (.CallIndirect entry index base) ∧
      Code.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS compiled.code.val compiled.jump_tables.val targets
        (front.map Code.valueType++results) after (raw.pc.val+1) next output) := by
  rcases indirect_point_head table type after (fun _ _ _ head => IndirectProjection.project (pairs:=compiled.indirect.val) head) point.code with jump | actual
  · obtain ⟨target,forward,fetched,tail⟩ := jump
    exact Or.inl ⟨target,forward,fetched,⟨point.bindings,point.locals,point.labels,tail⟩⟩
  · obtain ⟨stack,params,results,typeIndex,tableIndex,entry,index,base,bounds,typeEq,tableEq,input,signature,tableType,pair,basePosition,indexPosition,fetch,tail⟩ := actual
    obtain ⟨actualContext,front,args,actualParams,actualResults,position,bindings,actualTable,actualSignature,values,bounded,arguments,frontWf,heights,caller,tableBound,typeBound⟩ := Abs.Indirect.operands typed
    have contexts : actualContext.TYPES=C.TYPES := bindings.types.trans point.bindings.types.symm
    rw [contexts,signature] at actualSignature
    have equal := Option.some.inj actualSignature
    obtain ⟨paramsEq,resultsEq⟩ := functype.mk_functype.inj equal
    have paramsEq := list.mk_list.inj paramsEq
    have resultsEq := list.mk_list.inj resultsEq
    subst actualParams
    subst actualResults
    have argumentTypes : args.map Code.valueType=params := by
      simpa only [show Code.valueType = Abs.valueType from funext valueType_eq_abs] using Abs.results_type_of_typed arguments
    have valueType : Code.valueType (Abs.integerVal .I32 position)=.I32 := rfl
    simp only [values,List.map_append,List.map_cons,List.map_nil,argumentTypes,valueType] at input
    have frontTypes : front.map Code.valueType=stack := List.append_cancel_right (List.append_cancel_right input)
    refine Or.inr ⟨front,args,params,results,position,typeIndex,tableIndex,entry,index,base,bounds,typeEq,tableEq,
      values,bounded,arguments,argumentTypes,heights,caller,signature,tableType,pair,?_,indexPosition,fetch,?_⟩
    · simpa only [List.map_append,Code.slots_append,frontTypes,point.locals] using basePosition
    · simpa only [frontTypes] using tail
end Itasca.Runtime.Interp.StructuredMachine
