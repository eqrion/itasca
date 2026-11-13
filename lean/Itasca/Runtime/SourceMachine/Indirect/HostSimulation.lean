import Itasca.Runtime.Spec.ModuleMembership
import Itasca.Runtime.SourceMachine.Sim.Structured
import Itasca.Runtime.SourceMachine.Stateful.TableRead
import Itasca.Runtime.SourceMachine.Core.Trap
import Itasca.Runtime.SourceMachine.Ownership.Extension
import Itasca.Runtime.SourceMachine.Bound
import Itasca.Runtime.SourceMachine.Measure
import Itasca.Runtime.SourceMachine.Float.Results
import Itasca.Runtime.SourceMachine.Stateful.Signature
import Itasca.Runtime.SourceMachine.Stateful.TableSet
import Itasca.Runtime.SourceMachine.BrTable
import Itasca.Runtime.SourceMachine.Sim.Control

/-!
Sections, each formerly its own module: Definition, Operands, Correct, Transport, Results, HostSimulation.
-/

/-! ## Definition -/

section

namespace Itasca.Runtime.SourceMachine.Indirect
open SpecExt Itasca.Runtime.Spec

def resolve (s : store) (f : AFrame) (table type position : Nat) : Option Nat :=
  match (fun_table ⟨s,f.toFrame⟩ (.mk_uN table)).REFS[position]? with
  | some (.REF_FUNC_ADDR address) =>
    match s.FUNCS[address]? with
    | some function => if fun_type ⟨s,f.toFrame⟩ (.mk_uN type)=function.TYPE then some address else none
    | none => none
  | _ => none

theorem resolve_iff (s : store) (f : AFrame) (table type position address : Nat) :
    resolve s f table type position=some address ↔ IndirectTarget s f.toFrame table type position address := by
  unfold resolve IndirectTarget
  split
  · rename_i actual reference
    split
    · rename_i function lookup
      split
      · rename_i signature
        constructor
        · intro equal;cases equal;exact ⟨reference,function,lookup,signature⟩
        · rintro ⟨other,fn,found,same⟩
          have addressEq := Option.some.inj (reference.symm.trans other)
          cases addressEq
          rfl
      · rename_i signature
        constructor
        · intro impossible;cases impossible
        · rintro ⟨other,fn,found,same⟩
          have addressEq := Option.some.inj (reference.symm.trans other)
          cases addressEq
          have fnEq := Option.some.inj (lookup.symm.trans found)
          cases fnEq
          exact (signature same).elim
    · rename_i missing
      constructor
      · intro impossible;cases impossible
      · rintro ⟨other,fn,found,same⟩
        have addressEq := Option.some.inj (reference.symm.trans other)
        cases addressEq
        rw [missing] at found
        cases found
  · rename_i reference missing
    constructor
    · intro impossible;cases impossible
    · rintro ⟨found,_⟩
      exact (missing address found).elim

/-- Direct and indirect calls share the exact resolved-address installation. -/
def invoke (s : AState) (f : AFrame) (rest : List AFrame) (address : Nat) (after : List instr) : AResult :=
  match s.store.FUNCS[address]? with
  | none => .stuck
  | some function =>
    let ⟨.mk_list params, .mk_list results⟩ := function.TYPE
    if params.length ≤ f.vals.length then
      let args := f.vals.drop (f.vals.length - params.length)
      if args.map valueType = params then
        let caller := { f with vals := f.vals.take (f.vals.length - params.length), code := after }
        match function.CODE with
        | .HOST _ => .host address args results { s with frames := caller :: rest }
        | .FUNC _ locals body =>
          match defaultLocals locals with
          | none => .stuck
          | some defaults =>
            let label : Label := {
              branchTypes := results
              resultTypes := results
              cont := []
              height := 0
              after := [] }
            let callee : AFrame := {
              fa := address
              resultTypes := results
              locals := args ++ defaults
              module := function.MODULE
              labels := [label]
              code := body
              vals := [] }
            .next { s with frames := callee :: caller :: rest }
      else .stuck
    else .stuck

def step (s : AState) (f : AFrame) (rest : List AFrame) (table type : Nat) (after : List instr) : AResult :=
  match pop f.vals with
  | none => .stuck
  | some (front,value) => match integer .I32 value with
    | none => .stuck
    | some position => match resolve s.store f table type position with
      | none => .trap
      | some address => invoke s {f with vals:=front} rest address after

end Itasca.Runtime.SourceMachine.Indirect

end

/-! ## Operands -/

section

namespace Itasca.Runtime.SourceMachine.Indirect
open SpecExt Itasca.Runtime.Spec

theorem operands {s : store} {f : AFrame} {table type : Nat} {after : List instr}
    (typed : FrameTyped s {f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after} []) :
    ∃ C front args params results position,
      ModuleBindings s f.module C ∧
      (∃limits,C.TABLES[table]?=some (.mk_tabletype limits .FUNCREF)) ∧
      C.TYPES[type]?=some ⟨.mk_list params,.mk_list results⟩ ∧
      f.vals=front++args++[integerVal .I32 position] ∧ position<2^32 ∧
      ResultsTyped s params args ∧ Forall wf_val front ∧
      (∀label∈f.labels,label.height≤front.length) ∧
      FrameTyped s {f with code:=after,vals:=front} results ∧ table<2^32 ∧ type<2^32 := by
  cases typed with
  | mk C bindings localTypes locals values returns hc hw =>
    simp only [List.append_nil] at hc
    obtain ⟨prefixTypes,inputs,outputs,operation,stack,continuation,heights⟩ := code_stack_after_bounds (value_types_concrete f.vals) hc
    cases operation with
    | call_indirect _ _ _ params results limits tableBound tableType typeBound signature contextWf instructionWf _ =>
      simp only [labelContext,proj_uN_0] at tableBound tableType typeBound signature
      have all : ResultsTyped s (prefixTypes++(params++[valtype.I32])) f.vals := by rw [←stack];exact values
      obtain ⟨front,operands,split,frontTyped,operandTyped⟩ := results_typed_split all
      obtain ⟨args,index,operandSplit,argsTyped,indexTyped⟩ := results_typed_split operandTyped
      cases indexTyped with
      | cons selected nil =>
        cases nil
        obtain ⟨position,rfl,bounded⟩ := integer_val_inv (ty:=.I32) selected
        have selectedTable : C.TABLES[table]?=some (.mk_tabletype limits .FUNCREF) := by
          rw [List.getElem?_eq_getElem tableBound]
          exact congrArg some (by simpa only [getElem!_pos C.TABLES table tableBound] using tableType)
        have selectedType : C.TYPES[type]?=some ⟨.mk_list params,.mk_list outputs⟩ := by
          rw [List.getElem?_eq_getElem typeBound]
          exact congrArg some (by simpa only [getElem!_pos C.TYPES type typeBound] using signature)
        refine ⟨C,front,args,params,outputs,position,bindings,⟨limits,selectedTable⟩,selectedType,?_,bounded,argsTyped,
          results_typed_wf frontTyped,?_,?_,?_,?_⟩
        · simpa only [operandSplit,List.append_assoc] using split
        · intro label member
          rw [results_typed_length frontTyped]
          exact heights label member
        · have frontTypes := results_type_of_typed frontTyped
          apply FrameTyped.mk (f:={f with code:=after,vals:=front}) C bindings localTypes locals (by simpa only [frontTypes] using frontTyped) returns ?_ hw
          simpa only [frontTypes] using continuation
        · cases instructionWf;rename_i ht hy;cases ht;norm_num at *;omega
        · cases instructionWf;rename_i ht hy;cases hy;norm_num at *;omega
end Itasca.Runtime.SourceMachine.Indirect

end

/-! ## Correct -/

section

/-!
Indirect-call source progress, preservation and simulation, used by selected-call machine execution. Lookup contracts and host-call simulation remain separate.
-/

/-! ## Progress -/

section

namespace Itasca.Runtime.SourceMachine.Indirect
open SpecExt Itasca.Runtime.Spec

theorem type_selected {s : store} {f : AFrame} {C : context} {type : Nat} {signature : functype}
    (bindings : ModuleBindings s f.module C) (selected : C.TYPES[type]?=some signature) :
    fun_type ⟨s,f.toFrame⟩ (.mk_uN type)=signature := by
  simp only [fun_type,AFrame.toFrame,proj_uN_0,←bindings.types,List.getElem!_eq_getElem?_getD,selected,Option.getD_some]

end Itasca.Runtime.SourceMachine.Indirect

end

/-! ## Preservation -/

section

namespace Itasca.Runtime.SourceMachine.Indirect
open SpecExt Itasca.Runtime.Spec

theorem invoke_preservation (s : store) (ambient : frame) (originalCode : List instr) (f : AFrame) (rest : List AFrame)
    (address : Nat) (after : List instr) (fn : funcinst) (params results : List valtype) (front args : List val)
    (typed : CoreTyped ⟨s,ambient,{f with code:=originalCode}::rest,[]⟩)
    (lookup : s.FUNCS[address]?=some fn) (signature : fn.TYPE=⟨.mk_list params,.mk_list results⟩)
    (arguments : ResultsTyped s params args) (caller : FrameTyped s {f with code:=after,vals:=front} results)
    (heights : ∀label∈f.labels,label.height≤front.length)
    (next : AState)
    (stepped : invoke ⟨s,ambient,{f with code:=originalCode}::rest,[]⟩ {f with vals:=front++args} rest address after=.next next) :
    CoreTyped next := by
  have types := results_type_of_typed arguments
  have lengthEq := results_typed_length arguments
  cases body : fn.CODE with
  | HOST host => simp [invoke,lookup,signature,←lengthEq,types,body] at stepped
  | FUNC index locals source =>
    obtain ⟨defaults,initial⟩ := function_defaults typed.typed.functions (List.mem_of_getElem? lookup) body
    have functionTyped := typed.typed.functions fn (List.mem_of_getElem? lookup)
    simp only [body] at functionTyped
    obtain ⟨C,bindings,emptyLocals,emptyLabels,returns,functionTyped⟩ := functionTyped
    rw [signature] at functionTyped
    obtain ⟨actualDefaults,actualInitial,callee⟩ := callee_frame_typed typed.typed.store
      (function_module_wf typed.typed.store (List.mem_of_getElem? lookup)) bindings emptyLocals emptyLabels functionTyped arguments address
    have same := Option.some.inj (initial.symm.trans actualInitial)
    subst actualDefaults
    have nextEq : next=⟨s,ambient,
        ⟨address,results,args++defaults,fn.MODULE,[⟨results,results,[],0,[]⟩],source,[]⟩::
        {f with vals:=front,code:=after}::rest,[]⟩ := by
      simpa [invoke,lookup,signature,←lengthEq,types,body,initial] using stepped.symm
    rw [nextEq]
    refine ⟨?_,typed.contents⟩
    have tail : FramesTyped s rest f.resultTypes := by
      cases typed.typed.frames with | cons _ tail => exact tail
    refine ⟨typed.typed.store,typed.typed.functions,typed.typed.ambient,.cons callee (.cons caller tail),by simp [Forall],by simp,?_⟩
    intro frame member
    simp only [List.mem_cons] at member
    rcases member with rfl | rfl | member
    · exact frame_typed_heights callee
    · exact heights
    · exact typed.typed.heights frame (by simp [member])

theorem preservation (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (table type : Nat) (after : List instr) (next : AState)
    (typed : CoreTyped ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩)
    (stepped : step ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩ f rest table type after=.next next) :
    CoreTyped next := by
  have frameTyped : FrameTyped s {f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,args,params,results,position,bindings,tableSelected,typeSelected,values,bounded,arguments,frontWf,heights,caller,tableBound,typeBound⟩ := operands frameTyped
  have decoded : integer numtype.I32 (integerVal .I32 position)=some position := integer_accepts .I32 position bounded
  cases resolved : resolve s f table type position with
  | none =>
    simp only [step,values,pop_append,decoded,resolved] at stepped
    cases stepped
  | some address =>
    obtain ⟨reference,fn,lookup,signature⟩ := (resolve_iff s f table type position address).mp resolved
    have actualType : fn.TYPE=⟨.mk_list params,.mk_list results⟩ := signature.symm.trans (type_selected bindings typeSelected)
    apply invoke_preservation s ambient _ f rest address after fn params results front args typed lookup actualType arguments caller heights next
    simpa only [step,values,pop_append,decoded,resolved] using stepped
end Itasca.Runtime.SourceMachine.Indirect

end

/-! ## Simulation -/

section

namespace Itasca.Runtime.SourceMachine.Indirect
open SpecExt Itasca.Runtime.Spec
theorem indirect_call_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (table type position address : Nat) (typeIndex : idx)
    (moduleInst : moduleinst) (params results types : List valtype) (body : List instr)
    (baseValues args defaults : List val)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length)
    (resolve : IndirectTarget s f.toFrame table type position address)
    (tableBound : table<2^32) (typeBound : type<2^32) (positionBound : position<2^32)
    (lookup : s.FUNCS[address]? = some ⟨⟨.mk_list params, .mk_list results⟩, moduleInst,
      .FUNC typeIndex (types.map local.LOCAL) body⟩)
    (nonbot : Forall (fun ty => ty ≠ valtype.BOT) types)
    (hdefaults : defaultLocals (types.map local.LOCAL) = some defaults)
    (hargs : Forall wf_val args) (hlen : args.length = params.length) :
    StepsHN 2
      (decode ⟨s, ambient, { f with code := .CALL_INDIRECT (.mk_uN table) (.mk_uN type) :: after, vals := baseValues ++ args ++ [integerVal .I32 position] } :: rest, []⟩) []
      (decode ⟨s, ambient,
        ⟨address, results, args ++ defaults, moduleInst,
          [⟨results, results, [], 0, []⟩], body, []⟩ ::
        { f with code := after, vals := baseValues } :: rest, []⟩) := by
  have h₁ := step_h_instrs (call_indirect_resolve s f.toFrame table type position address hs hf tableBound typeBound positionBound resolve)
    args (after.map admininstr_instr) hargs (wf_instrs hc)
  have h₂ := step_h_instrs (call_invoke s f.toFrame address typeIndex moduleInst
    params results types body args defaults hs hf lookup nonbot hdefaults hargs hlen)
    [] (after.map admininstr_instr) (forall_nil _) (wf_instrs hc)
  have h₃ := step_h_active ambient rest f.arity
    (step_h_decode_labels h₁ f.labels baseValues hl hv) ha hr
  have h₄ := step_h_active ambient rest f.arity
    (step_h_decode_labels h₂ f.labels baseValues hl hv) ha hr
  simp only [vals, List.map_nil, List.nil_append, List.append_assoc] at h₃ h₄
  have both := StepsHN.cons h₃ (StepsHN.cons h₄ (StepsHN.refl (step_h_wf h₄).2))
  simp only [decode, decodeFrames, vals, List.map_nil, List.nil_append, List.map_cons,
    AFrame.toFrame, AFrame.arity, decodeLabels, Label.arity, List.take_zero,
    List.drop_zero, List.append_nil]
  rw [List.append_assoc]
  rw [decode_labels_move_values _ _ _ _ heights]
  simpa [instrContext, vals, List.append_assoc, AFrame.arity, AFrame.toFrame, admininstr_instr, integerVal, Segment.i32, numtype_Inn, admininstr_val] using both

end Itasca.Runtime.SourceMachine.Indirect

end

/-! ## Correct -/

section

namespace Itasca.Runtime.SourceMachine.Indirect
open SpecExt Itasca.Runtime.Spec

theorem next_simulation (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (table type : Nat) (after : List instr) (next : AState)
    (typed : CoreTyped ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩)
    (stepped : step ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩ f rest table type after=.next next) :
    StepsHN 2 (decode ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩) [] (decode next) := by
  have frameTyped : FrameTyped s {f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,args,params,results,position,bindings,tableSelected,typeSelected,values,bounded,arguments,frontWf,heights,caller,tableBound,typeBound⟩ := operands frameTyped
  obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frame_typed_wf frameTyped
  have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
  have restWf : Forall FrameWf rest := by cases typed.typed.frames with | cons _ tail => exact frames_typed_wf tail
  have decoded : integer numtype.I32 (integerVal .I32 position)=some position := integer_accepts .I32 position bounded
  cases resolved : resolve s f table type position with
  | none => simp only [step,values,pop_append,decoded,resolved] at stepped;cases stepped
  | some address =>
    have target := (resolve_iff s f table type position address).mp resolved
    obtain ⟨reference,fn,lookup,signature⟩ := target
    have actualType : fn.TYPE=⟨.mk_list params,.mk_list results⟩ := signature.symm.trans (type_selected bindings typeSelected)
    have argTypes := results_type_of_typed arguments
    have argLength := results_typed_length arguments
    cases body : fn.CODE with
    | HOST host => simp [step,values,←List.append_assoc,pop_append,decoded,resolved,invoke,lookup,actualType,←argLength,argTypes,body] at stepped
    | FUNC index locals source =>
      have functionTyped := typed.typed.functions fn (List.mem_of_getElem? lookup)
      simp only [body] at functionTyped
      obtain ⟨Cfn,fnBindings,noLocals,noLabels,noReturns,functionTyped⟩ := functionTyped
      rw [actualType] at functionTyped
      obtain ⟨types,localEq,nonbot⟩ := function_local_types functionTyped
      subst locals
      obtain ⟨defaults,initial,defaultsTyped⟩ := default_locals_typed typed.typed.store types nonbot
      have record : fn=⟨⟨.mk_list params,.mk_list results⟩,fn.MODULE,.FUNC index (types.map local.LOCAL) source⟩ := by
        cases fn
        simp_all
      have installed : next=⟨s,ambient,
        ⟨address,results,args++defaults,fn.MODULE,[⟨results,results,[],0,[]⟩],source,[]⟩::
        {f with vals:=front,code:=after}::rest,[]⟩ := by
        simp only [step,values,pop_append,decoded,resolved] at stepped
        simpa [invoke,lookup,actualType,←argLength,argTypes,body,initial] using stepped.symm
      have simulation := indirect_call_simulation s ambient f rest after table type position address index fn.MODULE params results types source front args defaults
        typed.typed.store typed.typed.ambient frameWf labelsWf frontWf tailWf restWf heights ⟨reference,fn,lookup,signature⟩ tableBound typeBound bounded
        (record ▸ lookup) nonbot initial (results_typed_wf arguments) argLength
      simpa only [installed,values] using simulation

theorem invoke_not_trap (s : AState) (f : AFrame) (rest : List AFrame) (address : Nat) (after : List instr) :
    invoke s f rest address after ≠ .trap := by
  unfold invoke
  repeat' first | split | (dsimp only) | (intro impossible;cases impossible)

theorem trap_simulation (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (table type : Nat) (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩)
    (stepped : step ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩ f rest table type after=.trap) :
    ∃count,0<count ∧ StepsHN count (decode ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩) [] ⟨⟨s,ambient⟩,[.TRAP]⟩ := by
  have frameTyped : FrameTyped s {f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,args,params,results,position,bindings,tableSelected,typeSelected,values,bounded,arguments,frontWf,heights,caller,tableBound,typeBound⟩ := operands frameTyped
  obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frame_typed_wf frameTyped
  have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
  have restWf : Forall FrameWf rest := by cases typed.typed.frames with | cons _ tail => exact frames_typed_wf tail
  have decoded : integer numtype.I32 (integerVal .I32 position)=some position := integer_accepts .I32 position bounded
  cases resolved : resolve s f table type position with
  | some address =>
    simp only [step,values,pop_append,decoded,resolved] at stepped
    exact (invoke_not_trap _ _ _ _ _ stepped).elim
  | none =>
    have missing : ¬∃address,IndirectTarget s f.toFrame table type position address := by
      rintro ⟨address,target⟩
      have same := (resolve_iff s f table type position address).mpr target
      rw [resolved] at same
      cases same
    have source := call_indirect_trap s f.toFrame table type position typed.typed.store frameWf tableBound typeBound bounded missing
    have allFront : Forall wf_val (front++args) := forall_append frontWf (results_typed_wf arguments)
    have allHeights : ∀label∈f.labels,label.height≤(front++args).length := by
      intro label member
      have bound := heights label member
      simp only [List.length_append]
      omega
    have full := operand_trap_simulation s ambient f rest (.CALL_INDIRECT (.mk_uN table) (.mk_uN type)) after
      (front++args) [integerVal .I32 position] typed.typed.store typed.typed.ambient frameWf labelsWf allFront tailWf restWf allHeights
      (by simpa only [vals,List.map_cons,List.map_nil,admininstr_val,integerVal,numtype_Inn,admininstr_instr,Segment.i32,List.singleton_append] using source)
    simpa only [values] using full
end Itasca.Runtime.SourceMachine.Indirect

end

end

/-! ## Transport -/

section

/-!
Indirect-call ownership and transport through store/code bounds, used by supported and cumulative execution.
-/

/-! ## Ownership -/

section

namespace Itasca.Runtime.SourceMachine.Indirect
open SpecExt Itasca.Runtime.Spec Itasca.Runtime.SourceMachine.Ownership

theorem invoke_owned {bound s f rest next address after}
    (frame : FrameOwned bound f) (frames : ∀item∈rest,FrameOwned bound item)
    (results : ValuesOwned bound s.results)
    (stepped : invoke s f rest address after=.next next) : StateOwned bound next := by
  simp only [invoke] at stepped
  repeat' first | split at stepped | contradiction
  cases stepped
  refine ⟨results,?_⟩
  simp only [List.mem_cons,forall_eq_or_imp]
  refine ⟨⟨values_owned_append.mpr ⟨frame.2.drop _,?_⟩,values_owned_nil _⟩,⟨frame.1,frame.2.take _⟩,frames⟩
  apply default_locals_ownership
  assumption

theorem step_owned {bound s f rest next table type after}
    (frame : FrameOwned bound f) (frames : ∀item∈rest,FrameOwned bound item)
    (results : ValuesOwned bound s.results)
    (stepped : step s f rest table type after=.next next) : StateOwned bound next := by
  unfold step at stepped
  split at stepped
  · cases stepped
  · rename_i front value popped
    split at stepped
    · cases stepped
    · split at stepped
      · cases stepped
      · apply invoke_owned (f:={f with vals:=front}) ⟨frame.1,?_⟩ frames results stepped
        exact (frame.2.pop popped).1
end Itasca.Runtime.SourceMachine.Indirect

end

/-! ## Transport -/

section

namespace Itasca.Runtime.SourceMachine.Indirect
open SpecExt Itasca.Runtime.Spec Itasca.Runtime.SourceMachine.Ownership

theorem invoke_metadata {s f rest address after next}
    (stepped : invoke s f rest address after=.next next) :
    next.store=s.store ∧ next.ambient=s.ambient := by
  simp only [invoke] at stepped
  repeat' first | split at stepped | contradiction
  cases stepped
  exact ⟨rfl,rfl⟩

theorem step_metadata {s f rest table type after next}
    (stepped : step s f rest table type after=.next next) :
    next.store=s.store ∧ next.ambient=s.ambient := by
  unfold step at stepped
  repeat' first | split at stepped | contradiction
  exact invoke_metadata stepped

theorem invoke_bound {bound : Nat} {s : AState} {f : AFrame} {rest : List AFrame}
    {address : Nat} {after : List instr} {next : AState}
    (bounded : CodeBound bound s) (tail : sizeOf after≤bound)
    (labels : ∀label∈f.labels,sizeOf (label.cont++label.after)≤bound)
    (frames : Forall (FrameCodeBound bound) rest)
    (stepped : invoke s f rest address after=.next next) : CodeBound bound next := by
  cases lookup : s.store.FUNCS[address]? with
  | none => simp [invoke,lookup] at stepped
  | some fn =>
    have function := bounded.functions fn (List.mem_of_getElem? lookup)
    cases signature : fn.TYPE with
    | mk_functype params results =>
      cases params with
      | mk_list params =>
        cases results with
        | mk_list results =>
          cases body : fn.CODE with
          | HOST host =>
            simp only [invoke,lookup,signature,body] at stepped
            repeat' first | split at stepped | contradiction
          | FUNC index locals source =>
            simp only [body] at function
            simp only [invoke,lookup,signature,body] at stepped
            repeat' first | split at stepped | contradiction
            cases stepped
            refine ⟨bounded.positive,?_,bounded.functions⟩
            intro frame member
            rcases List.mem_cons.mp member with rfl | member
            · exact ⟨function,by simpa [Forall] using bounded.positive⟩
            · rcases List.mem_cons.mp member with rfl | member
              · exact ⟨tail,labels⟩
              · exact frames frame member

theorem step_bound {bound s ambient f rest table type after next}
    (bounded : CodeBound bound ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩)
    (stepped : step ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩ f rest table type after=.next next) : CodeBound bound next := by
  have frame := bounded.frames {f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after} (List.mem_cons_self ..)
  unfold step at stepped
  repeat' first | split at stepped | contradiction
  apply invoke_bound (f:={f with vals:=_}) bounded ?_ frame.2 ?_ stepped
  · have size := frame.1
    change sizeOf (.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after)≤bound at size
    simp at size
    omega
  · exact fun item member => bounded.frames item (List.mem_cons_of_mem _ member)

theorem step_stateful_owned {bounds s ambient f rest table type after next}
    (owned : StatefulOwned bounds ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩)
    (stepped : step ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩ f rest table type after=.next next) : StatefulOwned bounds next := by
  have frame := owned.values.2 {f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after} (List.mem_cons_self ..)
  refine ⟨step_owned frame (fun item member => owned.values.2 item (List.mem_cons_of_mem _ member)) owned.values.1 stepped,?_⟩
  rw [(step_metadata stepped).1]
  exact owned.heap

end Itasca.Runtime.SourceMachine.Indirect

end

end

/-! ## Results -/

section

namespace Itasca.Runtime.SourceMachine.Indirect

theorem invoke_result {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
    {original : List instr} {values : List val} {address : Nat} {after : List instr} {next : AState} {expected : List valtype}
    (result : InvocationResult expected ⟨s,ambient,{f with code:=original}::rest,[]⟩)
    (stepped : invoke ⟨s,ambient,{f with code:=original}::rest,[]⟩ {f with vals:=values} rest address after=.next next) :
    InvocationResult expected next := by
  simp only [invoke] at stepped
  repeat' first | split at stepped | contradiction
  cases stepped
  exact FramesReturn.under (FramesReturn.replace result rfl)

theorem step_result {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
    {table type : Nat} {after : List instr} {next : AState} {expected : List valtype}
    (result : InvocationResult expected ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩)
    (stepped : step ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩ f rest table type after=.next next) :
    InvocationResult expected next := by
  unfold step at stepped
  repeat' first | split at stepped | contradiction
  exact invoke_result result stepped
end Itasca.Runtime.SourceMachine.Indirect

end

/-! ## HostSimulation -/

section

namespace Itasca.Runtime.SourceMachine.Indirect
open SpecExt Itasca.Runtime.Spec

/-- An indirect host call resolves its checked table target and then returns atomically.
The host event and changed store survive all labels and suspended callers. -/
theorem host_return_simulation (s s' : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (table type position address : Nat)
    (baseValues args results : List val) (events : List HostEvent)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length)
    (resolve : IndirectTarget s f.toFrame table type position address)
    (tableBound : table < 2^32) (typeBound : type < 2^32) (positionBound : position < 2^32)
    (hargs : Forall wf_val args)
    (host : StepH ⟨⟨s,f.toFrame⟩,vals args ++ [.CALL_ADDR address]⟩ events
      ⟨⟨s',f.toFrame⟩,vals results⟩) :
    StepsHN 2
      (decode ⟨s,ambient,{f with code := .CALL_INDIRECT (.mk_uN table) (.mk_uN type) :: after,vals := baseValues ++ args ++ [integerVal .I32 position]} :: rest,[]⟩)
      events
      (decode ⟨s',ambient,{f with code := after,vals := baseValues ++ results} :: rest,[]⟩) := by
  have first := step_h_active ambient rest f.arity
    (step_h_decode_labels
      (step_h_instrs (call_indirect_resolve s f.toFrame table type position address hs hf tableBound typeBound positionBound resolve)
        args (after.map admininstr_instr) hargs (wf_instrs hc)) f.labels baseValues hl hv) ha hr
  have second := step_h_active ambient rest f.arity
    (step_h_decode_labels (step_h_instrs host [] (after.map admininstr_instr)
      (forall_nil _) (wf_instrs hc)) f.labels baseValues hl hv) ha hr
  simp only [vals,List.map_nil,List.nil_append,List.append_assoc] at first second
  have both := StepsHN.cons first (StepsHN.cons second (StepsHN.refl (step_h_wf second).2))
  simp only [decode,decodeFrames,vals,List.map_nil,List.nil_append,List.map_cons,AFrame.toFrame,AFrame.arity]
  rw [List.append_assoc]
  rw [decode_labels_move_values _ _ _ _ heights,decode_labels_move_values _ _ _ _ heights]
  simpa [instrContext,vals,List.append_assoc,AFrame.arity,AFrame.toFrame,admininstr_instr,integerVal,Segment.i32,numtype_Inn,admininstr_val] using both

/-- Host traps retain callback store effects while the source semantics unwinds
all remaining labels and callers. Unwinding emits no additional host events. -/
theorem host_trap_simulation (s s' : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (table type position address : Nat)
    (baseValues args : List val) (events : List HostEvent)
    (hs : wf_store s) (hs' : wf_store s') (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length)
    (resolve : IndirectTarget s f.toFrame table type position address)
    (tableBound : table < 2^32) (typeBound : type < 2^32) (positionBound : position < 2^32)
    (hargs : Forall wf_val args)
    (host : StepH ⟨⟨s,f.toFrame⟩,vals args ++ [.CALL_ADDR address]⟩ events
      ⟨⟨s',f.toFrame⟩,[.TRAP]⟩) :
    ∃ n, 2 ≤ n ∧ StepsHN n
      (decode ⟨s,ambient,{f with code := .CALL_INDIRECT (.mk_uN table) (.mk_uN type) :: after,vals := baseValues ++ args ++ [integerVal .I32 position]} :: rest,[]⟩)
      events ⟨⟨s',ambient⟩,[.TRAP]⟩ := by
  have first := step_h_active ambient rest f.arity
    (step_h_decode_labels
      (step_h_instrs (call_indirect_resolve s f.toFrame table type position address hs hf tableBound typeBound positionBound resolve)
        args (after.map admininstr_instr) hargs (wf_instrs hc)) f.labels baseValues hl hv) ha hr
  have second := step_h_active ambient rest f.arity
    (step_h_decode_labels (step_h_instrs host [] (after.map admininstr_instr)
      (forall_nil _) (wf_instrs hc)) f.labels baseValues hl hv) ha hr
  have frames : Forall FrameWf ({f with vals := baseValues,code := after} :: rest) := by
    intro frame member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨hf,hl,hv,hc⟩
    · exact hr frame member
  obtain ⟨n,tail⟩ := trap_frames s' ambient ({f with vals := baseValues,code := after} :: rest) hs' ha frames
  have tail' : StepsHN n _ [] ⟨⟨s',ambient⟩,[.TRAP]⟩ := tail
  simp only [vals,List.map_nil,List.nil_append,List.append_assoc] at first second
  have both := StepsHN.cons first (StepsHN.cons second tail')
  refine ⟨n+2,by omega,?_⟩
  simp only [decode,decodeFrames,vals,List.map_nil,List.nil_append,List.map_cons,AFrame.toFrame,AFrame.arity]
  rw [List.append_assoc]
  rw [decode_labels_move_values _ _ _ _ heights]
  simpa [decodeFrames,instrContext,vals,List.append_assoc,AFrame.arity,AFrame.toFrame,admininstr_instr,Nat.add_assoc,integerVal,Segment.i32,numtype_Inn,admininstr_val] using both
end Itasca.Runtime.SourceMachine.Indirect

end
