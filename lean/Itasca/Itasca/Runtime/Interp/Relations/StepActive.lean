import Itasca.Runtime.Interp.Relations.StackPreservation
import Itasca.Runtime.Interp.Recording
import Itasca.Runtime.Interp.Relations.SourceCallCause
import Itasca.Runtime.SourceMachine.Indirect.HostSimulation
import Itasca.Runtime.Interp.Relations.ReadbackAndBindings
import Itasca.Runtime.SourceMachine.TransitionAndHostPreparation
import Itasca.Runtime.SourceMachine.Core.OperationsAndMemoryTyping
import Itasca.Runtime.Interp.Machine.Select.Operands
import Itasca.Runtime.Interp.Control.NormalizeCompose
import Itasca.Runtime.Interp.HostCalls
import Itasca.Runtime.Interp.Relations.TypedOperands
import Itasca.Support.Translation

open WebAssembly

open Itasca.Representation

/-! ## SourceIndirectCallCause -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std

/-- A rejected indirect call retains both the actual selected callee and the
source argument region. The table selector is consumed before callee entry. -/
def SourceIndirectCallCause {A M P : Type} (allocator : runtime.platform.Alloc A)
    (hooks : runtime.platform.Platform P M) (code : Representation.CodeInterpretation) (before : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (frameIndex : Usize)
    (raw : runtime.interp.Frame) (callerCode : runtime.bytecode.CompiledFunction)
    (source : SourceMachine.AState) (error : runtime.ExecError) : Prop :=
  ∃ (entry selector offset table type pc : U32) (address base : Usize)
    (function : runtime.store.FuncInst) (instanceIndex functionIndex : Usize)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction),
    callerCode.code.val[raw.pc.val]?=some (.CallIndirect entry selector offset) ∧
    callerCode.indirect.val[entry.val]?=some (table,type) ∧
    store.funcs.val[address.val]?=some function ∧ function.code=.Wasm instanceIndex functionIndex ∧
    store.instances.val[instanceIndex.val]?=some inst ∧ inst.module.functions.val[functionIndex.val]?=some compiled ∧
    base.val=raw.base.val+offset.val ∧ pc.val=raw.pc.val+1 ∧
    CallCause allocator hooks {before with frames:=before.frames.set frameIndex {raw with pc:=pc}}
      store platform base compiled error ∧
    ∃ (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr) (front args : List val)
      (position : Nat) (params results : List valtype) (count : Nat),
      Spec.StepsHN count (SourceMachine.decode source) [] (SourceMachine.decode ⟨source.store,source.ambient,
        {f with code:=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)::after}::rest,[]⟩) ∧
      f.vals=(front++args)++[SourceMachine.integerVal .I32 position] ∧ position<2^32 ∧
      SourceMachine.Indirect.resolve source.store f table.val type.val position=some address.val ∧
      (Representation.decodeFunction code store function).TYPE=⟨.mk_list params,.mk_list results⟩ ∧
      args.map Representation.valueType=params ∧
      offset.val=Representation.slots ((f.locals++front).map Representation.valueType) ∧
      raw.base.val=suspendedSourceWords rest
theorem SourceIndirectCallCause.prepend {A M P : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {code : Representation.CodeInterpretation} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {frameIndex : Usize} {raw : runtime.interp.Frame}
    {compiled : runtime.bytecode.CompiledFunction} {before after : SourceMachine.AState} {error : runtime.ExecError} {count}
    (steps : Spec.StepsHN count (SourceMachine.decode before) [] (SourceMachine.decode after))
    (sameStore : after.store=before.store) (sameAmbient : after.ambient=before.ambient)
    (cause : SourceIndirectCallCause allocator hooks code exec store platform frameIndex raw compiled after error) :
    SourceIndirectCallCause allocator hooks code exec store platform frameIndex raw compiled before error := by
  obtain ⟨entry,selector,offset,table,type,pc,address,base,function,instanceIndex,functionIndex,inst,callee,
    fetch,pair,functionAt,defined,instanceAt,calleeAt,baseEq,pcEq,rejected,
    f,rest,source,front,args,position,params,results,tailCount,tail,values,bounded,resolved,signature,arguments,coordinates,sourceBase⟩ := cause
  refine ⟨entry,selector,offset,table,type,pc,address,base,function,instanceIndex,functionIndex,inst,callee,
    fetch,pair,functionAt,defined,instanceAt,calleeAt,baseEq,pcEq,rejected,
    f,rest,source,front,args,position,params,results,count+tailCount,?_,values,bounded,?_,signature,arguments,coordinates,sourceBase⟩
  · simpa only [sameStore,sameAmbient,List.nil_append] using steps.trans tail
  · simpa only [sameStore] using resolved
end Itasca.Interp

end

/-! ## EventfulControl -/

section

namespace Itasca.Interp

theorem ConcreteSim.eventful {codeLength beforePC afterPC beforePending afterPending before after}
    (simulation : ConcreteSim codeLength beforePC afterPC beforePending afterPending before after) :
    EventfulConcreteSim codeLength beforePC afterPC beforePending afterPending before after [] := by
  rcases simulation with ⟨same,decrease⟩ | reductions
  · exact Or.inl ⟨same,rfl,decrease⟩
  · exact Or.inr reductions

theorem EventfulConcreteSim.of_steps {codeLength beforePC afterPC beforePending afterPending before after events n}
    (positive : 0 < n) (steps : Spec.StepsHN n (SourceMachine.decode before) events (SourceMachine.decode after)) :
    EventfulConcreteSim codeLength beforePC afterPC beforePending afterPending before after events :=
  Or.inr ⟨n,positive,steps⟩

theorem EventfulConcreteSim.source {codeLength beforePC afterPC beforePending afterPending before after events}
    (wellFormed : wf_config (SourceMachine.decode before))
    (simulation : EventfulConcreteSim codeLength beforePC afterPC beforePending afterPending before after events) :
    ∃ n, Spec.StepsHN n (SourceMachine.decode before) events (SourceMachine.decode after) := by
  rcases simulation with ⟨same,rfl,decrease⟩ | ⟨n,positive,steps⟩
  · exact ⟨0,same ▸ Spec.StepsHN.refl wellFormed⟩
  · exact ⟨n,steps⟩
end Itasca.Interp

end

/-! ## TypedSelectOperands -/

section

namespace Itasca.Interp.TypedSelect
open Aeneas Aeneas.Std

theorem select_typed_operands {annotation : Option (List valtype)} {s : WebAssembly.store} {f : SourceMachine.AFrame} {after : List instr}
    (typed : SourceMachine.FrameTyped s {f with code := .SELECT annotation::after} []) :
    ∃ front left right bits ty,
      f.vals = front ++ [left,right,SourceMachine.integerVal .I32 bits] ∧ bits < 2^32 ∧
      Representation.valueType left = ty ∧ Representation.valueType right = ty ∧
      (∀ label ∈ f.labels, label.height ≤ front.length) := by
  obtain ⟨C,front,operands,ins,outs,_,_,operation,split,operandTypes,frontWf,heights⟩ :=
    SourceMachine.frame_typed_operands_bounds typed
  obtain ⟨ty,rfl,rfl⟩ := SourceMachine.TypedSelect.signature operation
  cases operandTypes with
  | cons leftTyped tail =>
    cases tail with
    | cons rightTyped tail =>
      cases tail with
      | cons conditionTyped tail =>
        cases tail
        rename_i left right condition
        obtain ⟨bits,rfl,bitsBound⟩ := SourceMachine.integer_val_inv (ty := .I32) conditionTyped
        exact ⟨front,left,right,bits,_,split,bitsBound,
          (value_type_eq_abs left).trans (SourceMachine.value_type_of_typed leftTyped),
          (value_type_eq_abs right).trans (SourceMachine.value_type_of_typed rightTyped),heights⟩

theorem select_source_next {annotation : Option (List valtype)} {s : WebAssembly.store} {ambient : frame} {f : SourceMachine.AFrame} {rest : List SourceMachine.AFrame}
    {after : List instr} {front : List val} {left right : val} {bits : Nat}
    (values : f.vals = front ++ [left,right,SourceMachine.integerVal .I32 bits])
    (matching : Representation.valueType left = Representation.valueType right) (bounded : bits < 2^32) :
    SourceMachine.Core.select ⟨s,ambient,{f with code := .SELECT annotation::after}::rest,[]⟩ f rest after =
      .next ⟨s,ambient,{f with code := after,vals := front ++ [if bits = 0 then right else left]}::rest,[]⟩ := by
  have shape : f.vals = ((front ++ [left]) ++ [right]) ++ [SourceMachine.integerVal .I32 bits] := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using values
  have decoded : SourceMachine.integer .I32 (SourceMachine.integerVal .I32 bits) = some bits := by
    simpa only [numtype_Inn] using SourceMachine.integer_accepts .I32 bits bounded
  have types : SourceMachine.valueType left = SourceMachine.valueType right := by simpa only [value_type_eq_abs] using matching
  simp only [SourceMachine.Core.select,shape,SourceMachine.pop_append,decoded,types,
    ite_true,SourceMachine.advance]
end Itasca.Interp.TypedSelect

end

/-! ## EventfulNormalize -/

section

namespace Itasca.Interp

theorem EventfulConcreteSim.trans
    {codeLength firstPC middlePC lastPC firstPending middlePending lastPending before middle after events rest}
    (first : EventfulConcreteSim codeLength firstPC middlePC firstPending middlePending before middle events)
    (second : EventfulConcreteSim codeLength middlePC lastPC middlePending lastPending middle after rest) :
    EventfulConcreteSim codeLength firstPC lastPC firstPending lastPending before after (events ++ rest) := by
  rcases first with ⟨firstEq,rfl,firstDecrease⟩ | ⟨n,hn,firstSteps⟩
  · rcases second with ⟨secondEq,rfl,secondDecrease⟩ | ⟨m,hm,secondSteps⟩
    · exact Or.inl ⟨firstEq.trans secondEq,rfl,Nat.lt_trans secondDecrease firstDecrease⟩
    · exact Or.inr ⟨m,hm,by simpa only [List.nil_append,firstEq] using secondSteps⟩
  · rcases second with ⟨secondEq,rfl,secondDecrease⟩ | ⟨m,hm,secondSteps⟩
    · exact Or.inr ⟨n,hn,by simpa only [List.append_nil,secondEq] using firstSteps⟩
    · exact Or.inr ⟨n+m,by omega,firstSteps.trans secondSteps⟩

/-- Normalize erased source control before a dispatch while retaining exactly
that dispatch's events, including a host call reached through nested blocks. -/
theorem EventfulConcreteSim.prepend_normalization {count before middle}
    (chain : ErasedSteps count before middle) (s : store) (ambient : frame) (rest : List SourceMachine.AFrame)
    (typed : SourceMachine.ATyped ⟨s,ambient,before::rest,[]⟩)
    {codeLength pc target pending after events}
    (simulation : EventfulConcreteSim codeLength pc target false pending
      ⟨s,ambient,middle::rest,[]⟩ after events) :
    EventfulConcreteSim codeLength pc target false pending ⟨s,ambient,before::rest,[]⟩ after events := by
  rcases (chain.sound s ambient rest typed).2 with ⟨_,same⟩ | prefixSimulation
  · simpa only [same] using simulation
  · simpa only [List.nil_append] using
      (ConcreteSim.of_source codeLength pc pc false false prefixSimulation).eventful.trans simulation
end Itasca.Interp

end

/-! ## DecodeOwnership -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std

theorem decode_value_owned_of_ok (ty : Itasca.wasm_types.ValueType) (lo hi : U64) (store : Usize)
    (value : runtime.Value) (actual : runtime.value.decode ty lo hi store = .ok value) : OwnedBy store value := by
  cases ty <;> simp only [runtime.value.decode,lift,bind_ok] at actual
  all_goals try { simp only [Result.ok.injEq] at actual; subst value; trivial }
  case V128 =>
    obtain ⟨shifted,shift,actual⟩ := Itasca.Computation.bind_ok_inv _ _ _ actual
    simp only [lift,bind_ok,Result.ok.injEq] at actual
    subst value
    trivial
  all_goals
    split at actual
    · simp only [Result.ok.injEq] at actual; subst value; trivial
    · obtain ⟨index,subtracted,actual⟩ := Itasca.Computation.bind_ok_inv _ _ _ actual
      simp only [Result.ok.injEq] at actual
      subst value
      rfl

theorem decode_slot_owned_of_ok (slots : Slice U64) (position : Usize)
    (ty : Itasca.wasm_types.ValueType) (store : Usize) (value : runtime.Value)
    (actual : runtime.interp.decode_slot slots position ty store = .ok value) : OwnedBy store value := by
  simp only [runtime.interp.decode_slot] at actual
  obtain ⟨width,widthEq,actual⟩ := Itasca.Computation.bind_ok_inv _ _ _ actual
  obtain ⟨hi,hiEq,actual⟩ := Itasca.Computation.bind_ok_inv _ _ _ actual
  obtain ⟨lo,loEq,actual⟩ := Itasca.Computation.bind_ok_inv _ _ _ actual
  exact decode_value_owned_of_ok ty lo hi store value actual

end Itasca.Interp

end

/-! ## StepActive -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std

theorem step_returned_active {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {exec : runtime.interp.Execution} {store : runtime.store.Store M} {platform : P} {out}
    (returned : runtime.interp.step memory hooks floats allocator exec store platform=.ok out) :
    0<exec.frames.length := by
  by_contra inactive
  have length : exec.frames.len=0#usize := by scalar_tac
  unfold runtime.interp.step at returned
  change (do let index ← exec.frames.len-1#usize; _) = .ok out at returned
  rw [length] at returned
  have failed : (0#usize-1#usize : Result Usize)=.fail .integerOverflow := by
    change UScalar.sub _ _=_
    simp [UScalar.sub]
  rw [failed] at returned
  simp at returned
theorem execution_body_stopped {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (state : ExecutionState M P) (stopped : ¬ActiveExecution state) :
    executionBody memory hooks floats allocator state=.ok (.done (finishExecution state)) := by
  rcases state with ⟨exec,store,platform,status⟩
  unfold executionBody runtime.interp.invoke_with_loop1.body
  dsimp only
  split
  · have positive : 0<exec.frames.length := by scalar_tac
    cases status with
    | Ok value => cases value;exact (stopped ⟨positive,rfl⟩).elim
    | Err error => simp [core.result.Result.is_ok,finishExecution]
  · rfl
end Itasca.Interp

end

/-! Callback observation preserves the extracted computation under erasure. -/

namespace Itasca.Interp
open Aeneas Aeneas.Std Itasca.Platform

theorem observing_invoke_loop_erase {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (status : core.result.Result Unit runtime.ExecError) (prior : List (HostObservation M)) :
    (do let out ← runtime.interp.invoke_with_loop1 memory (observing hooks) floats allocator
          exec store (platform, prior) status
        Result.ok (eraseLoopAnswer out)) =
      runtime.interp.invoke_with_loop1 memory hooks floats allocator exec store platform status := by
  apply loop_project _ _ eraseLoopState eraseLoopAnswer
  rintro ⟨exec, store, ⟨platform, prior⟩, status⟩
  dsimp only [eraseLoopState]
  unfold runtime.interp.invoke_with_loop1.body
  dsimp only
  split
  · simp only [Std.bind_assoc]
    apply congrArg (Std.bind _)
    funext continuing
    split
    · simp only [Std.bind_assoc]
      apply bind_project (fun out => (out.1, out.2.1, out.2.2.1, out.2.2.2.1)) _ _ _ _
        (observing_step_erase memory hooks floats allocator exec store platform prior)
      rintro ⟨result, nextExec, after, next, trace⟩
      simp only [Std.uncurry, bind_ok, eraseFlow, eraseLoopState]
    · simp only [bind_ok, eraseFlow, eraseLoopAnswer]
  · simp only [bind_ok, eraseFlow, eraseLoopAnswer]


end Itasca.Interp
