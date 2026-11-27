import Itasca.Runtime.SourceMachine.Stateful.TransitionInvariants
import Itasca.Runtime.SourceMachine.Core.OperationsAndMemoryTyping
import Itasca.Runtime.SourceMachine.Indirect.HostSimulation
import Itasca.Runtime.SourceMachine.Supported.PureCoverage
import Itasca.Runtime.SourceMachine.Core.ProgressAndBounds
import Itasca.Runtime.SourceMachine.OwnershipExtension
import Itasca.Runtime.SourceMachine.Float.Transition
import Itasca.Runtime.SourceMachine.StructureAndTyping
import Itasca.Runtime.SourceMachine.Float.Descriptors
import Itasca.Runtime.SourceMachine.Numeric.Transition
import Itasca.Runtime.SourceMachine.Bound
import Itasca.Runtime.SourceMachine.EntryAndBranchTables
import Itasca.Runtime.SourceMachine.Preservation
import Itasca.Runtime.SourceMachine.Sim.Structured
import Itasca.Runtime.SourceMachine.Sim.Host
import Itasca.Runtime.Spec.PrimitiveOperations
import Itasca.Runtime.SourceMachine.Simulation

open WebAssembly

/-!
Proofs for Runtime / SourceMachine.

This module collects CumulativeStep, TransitionAndHostPreparation, TypedSelect.
Each section documents its contracts and consumers.
-/

/-! ## CumulativeStep -/

section

/-! ## Heap -/

section

namespace Itasca.SourceMachine.Cumulative
open Itasca.SourceMachine.Ownership

theorem core_heap_metadata {s next : AState} (equation : Core.step s = .next next) :
    next.store.TABLES = s.store.TABLES ∧ next.store.ELEMS = s.store.ELEMS ∧ next.store.FUNCS = s.store.FUNCS := by
  simp only [Core.step,Core.instruction,astep] at equation
  repeat' first | split at equation | contradiction
  all_goals
    simp only [advance,returnFrame,enterLabel,branch,call,Itasca.SourceMachine.Numeric.transition,Itasca.SourceMachine.Numeric.finish,
      Core.select,Core.globalGet,Core.globalSet,Core.load,Core.store] at equation
    repeat' first | split at equation | contradiction
    all_goals
      simp only [advance,AResult.next.injEq] at equation
      cases equation
      exact ⟨rfl,rfl,rfl⟩

theorem core_heap_owned {bounds s next} (heap : StatefulHeapOwned bounds s.store)
    (globals : GlobalsOwned bounds next.store) (equation : Core.step s = .next next) :
    StatefulHeapOwned bounds next.store := by
  obtain ⟨tables,elements,functions⟩ := core_heap_metadata equation
  exact ⟨globals,by simpa only [tables] using heap.tables,by simpa only [elements] using heap.elements,
    by simpa only [functions] using heap.functions⟩
end Itasca.SourceMachine.Cumulative

end

/-! ## Step -/

section

namespace Itasca.SourceMachine.Cumulative
open WebAssembly Itasca.Spec Itasca.SourceMachine.Ownership

/-- Executable source transitions combine the deterministic mutable core with
the complete float result relation, preserving every permitted NaN result. -/
inductive Step : AState → AResult → Prop where
  | core {before result} (equation : Core.step before = result) (executable : result ≠ .stuck) : Step before result
  | scalar {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
      {after : List instr} {op : Float.Instruction} {result : AResult}
      (transition : Float.Transition ⟨s,ambient,{f with code := op.source :: after}::rest,[]⟩
        {f with code := op.source :: after} rest after op result) :
      Step ⟨s,ambient,{f with code := op.source :: after}::rest,[]⟩ result

  | stateful {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
      {after : List instr} {op : Stateful.Instruction} {result : AResult}
      (transition : Stateful.Transition ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩
        {f with code := op.source::after} rest after op result)
      (executable : result ≠ .stuck) :
      Step ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩ result

  | indirect {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
      {after : List instr} {table type : Nat} {result : AResult}
      (equation : Indirect.step ⟨s,ambient,{f with code := .CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩
        f rest table type after = result) (executable : result ≠ .stuck) :
      Step ⟨s,ambient,{f with code := .CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩ result

end Itasca.SourceMachine.Cumulative

end

end

/-! ## TransitionAndHostPreparation -/

section

/-!
# Transition And Host Preparation

Branch-table transitions and host-call preparation retain the source state invariants.
-/

/-! ## BrTableTransition -/

section

/-!
Branch-table transitions with ownership and code-bound preservation. Basic branch-table source semantics remain below the stateful invariant imports.
-/

/-! ## Br Table Invariants -/

section

namespace Itasca.SourceMachine.BrTable
open Ownership

/-- Selecting a label only removes the integer selector; all owned references
and every source heap component are retained. -/
theorem owned {bounds : Bounds} {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
    {after : List instr} {labels : List labelidx} {fallback : labelidx} {front : List val} {bits : Nat}
    (before : StatefulOwned bounds ⟨s,ambient,{f with code := .BR_TABLE labels fallback::after,vals := front ++ [integerVal .I32 bits]}::rest,[]⟩) :
    StatefulOwned bounds ⟨s,ambient,{f with code := .BR (select labels fallback bits)::after,vals := front}::rest,[]⟩ := by
  have frame := before.values.2 _ (List.mem_cons_self ..)
  apply stateful_owned_advance (step := rfl) before.heap (values_owned_nil _) ?_ ?_
  · exact ⟨frame.1,(values_owned_append.mp frame.2).1⟩
  · exact fun item member => before.values.2 item (List.mem_cons_of_mem _ member)

theorem bounded {bound : Nat} {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
    {after : List instr} {labels : List labelidx} {fallback : labelidx} {front : List val} {bits : Nat}
    (before : CodeBound bound ⟨s,ambient,{f with code := .BR_TABLE labels fallback::after,vals := front ++ [integerVal .I32 bits]}::rest,[]⟩) :
    CodeBound bound ⟨s,ambient,{f with code := .BR (select labels fallback bits)::after,vals := front}::rest,[]⟩ := by
  apply bound_replace_frame before
  have frame := before.frames _ (List.mem_cons_self ..)
  refine ⟨?_,frame.2⟩
  have size := frame.1
  have selected := select_size labels fallback bits
  simp at size ⊢
  omega

theorem covered
    {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
    {after : List instr} {labels : List labelidx} {fallback : labelidx} {front : List val} {bits : Nat}
    (before : SupportedState ⟨s,ambient,{f with code := .BR_TABLE labels fallback::after,vals := front ++ [integerVal .I32 bits]}::rest,[]⟩) :
    SupportedState ⟨s,ambient,{f with code := .BR (select labels fallback bits)::after,vals := front}::rest,[]⟩ := by
  have frame := before.active _ (List.mem_cons_self ..)
  refine ⟨?_,before.functions⟩
  intro item member
  rcases List.mem_cons.mp member with rfl | member
  · refine ⟨?_,frame.2⟩
    intro instruction member
    rcases List.mem_cons.mp member with rfl | member
    · exact SourceMachine.BinaryInstr.br _
    · exact frame.1 instruction (List.mem_cons_of_mem _ member)
  · exact before.active item (List.mem_cons_of_mem _ member)
end Itasca.SourceMachine.BrTable

end

/-! ## Br Table Transition -/

section

namespace Itasca.SourceMachine.BrTable
open WebAssembly Itasca.Spec Ownership

inductive Transition : AState → AState → Prop where
  | next {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
      {after : List instr} {labels : List labelidx} {fallback : labelidx} {front : List val} {bits : Nat}
      (values : f.vals = front ++ [integerVal .I32 bits]) (bound : bits < 2^32) :
      Transition ⟨s,ambient,{f with code := .BR_TABLE labels fallback::after}::rest,[]⟩
        ⟨s,ambient,{f with code := .BR (select labels fallback bits)::after,vals := front}::rest,[]⟩

private theorem normalized {f : AFrame} {source : List instr} {values : List val}
    (same : f.vals = values) : {f with code := source,vals := values} = {f with code := source} := by
  cases f
  simp_all

theorem Transition.correct {before next} (transition : Transition before next) (typed : CoreTyped before) :
    CoreTyped next ∧ NextSim before next := by
  cases transition with
  | @next s ambient f rest after labels fallback front bits values bound =>
    have result := Itasca.SourceMachine.BrTable.correct s ambient f rest after front bits labels fallback bound
      (by simpa only [normalized values] using typed.typed)
    exact ⟨⟨result.1,typed.contents⟩,by simpa only [normalized values] using result.2⟩

theorem Transition.next_supported {before next}
    (transition : Transition before next) (supported : SupportedState before) : SupportedState next := by
  cases transition with
  | next values bound =>
    exact covered (by simpa only [normalized values] using supported)

theorem Transition.next_owned {bounds before next} (transition : Transition before next)
    (initial : StatefulOwned bounds before) : StatefulOwned bounds next := by
  cases transition with
  | next values bound => exact owned (by simpa only [normalized values] using initial)

theorem Transition.next_bound {bound before next} (transition : Transition before next)
    (initial : CodeBound bound before) : CodeBound bound next := by
  cases transition with
  | next values bound => exact bounded (by simpa only [normalized values] using initial)

end Itasca.SourceMachine.BrTable

end

end

/-! ## HostTyping -/

section

namespace Itasca.SourceMachine
open WebAssembly Itasca.Spec

/-- A host callback suspends a nonempty source stack with its pending result
signature. The store is the pre-call store until the atomic callback completes. -/
structure HostPending (state : AState) (results : List valtype) : Prop where
  store : wf_store state.store
  functions : FunctionsTyped state.store
  ambient : wf_frame state.ambient
  frames : FramesTyped state.store state.frames results
  nonempty : state.frames ≠ []
  values : state.results = []
  heights : Forall FrameHeights state.frames

/-- Store extension transports every suspended frame; typed callback results
resume the active one. New functions obtain their typing from the post-store
invariant instead of assuming the host cannot add functions. -/
theorem HostPending.resume {state : AState} {types : List valtype}
    (pending : HostPending state types) {after : WebAssembly.store}
    (extension : Extend_store state.store after) (functions : FunctionsTyped after)
    {values : List val} (typed : ResultsTyped after types values) :
    ∃ f rest, state.frames = f :: rest ∧
      ATyped ⟨after,state.ambient,{f with vals := f.vals ++ values} :: rest,[]⟩ := by
  cases frames : state.frames with
  | nil => exact False.elim (pending.nonempty frames)
  | cons f rest =>
    have frameTypes := pending.frames.extend extension
    rw [frames] at frameTypes
    cases frameTypes with
    | cons head tail =>
      have resumed := resume_frame_preservation head typed
      refine ⟨f,rest,rfl,(extend_store_wf extension).2,functions,pending.ambient,
        .cons resumed tail,by simp [Forall],by simp,?_⟩
      intro frame member
      rcases List.mem_cons.mp member with rfl | member
      · exact frame_typed_heights resumed
      · exact pending.heights frame (by rw [frames]; simp [member])

/-- Source typing discharges argument extraction and the host's suspended
continuation directly from the abstract call result. -/
theorem host_call_preparation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (index address : Nat)
    (args : List val) (results : List valtype) (resume : AState)
    (typed : ATyped ⟨s,ambient,{f with code := .CALL (.mk_uN index) :: after} :: rest,[]⟩)
    (step : astep ⟨s,ambient,{f with code := .CALL (.mk_uN index) :: after} :: rest,[]⟩ =
      .host address args results resume) :
    HostPending resume results ∧ ∃ identity params,
      HostFunction s address identity params results ∧ ResultsTyped s params args := by
  have frames := typed.frames
  cases frames with
  | cons hf hr =>
    cases hf with
    | mk C bindings localTypes locals values returns hc hw =>
      simp only [List.append_nil] at hc
      obtain ⟨front, ins, outs, hop, hstack, hafter, heights⟩ :=
        code_stack_after_bounds (value_types_concrete f.vals) hc
      cases hop with
      | call _ _ inputs outputs hi ht _ _ =>
        simp only [labelContext, proj_uN_0] at hi ht
        have hi' : index < f.module.FUNCS.length := by
          rw [bindings.funcs.length_eq]
          exact hi
        obtain ⟨fn, hfn, htype⟩ := bindings.funcs.get hi' hi
        simp only [List.get_eq_getElem] at hfn htype
        have htype' : fn.TYPE = ⟨.mk_list ins, .mk_list outs⟩ := by
          rw [htype]
          simpa only [getElem!_pos C.FUNCS index hi] using ht
        have hresolve := List.getElem?_eq_getElem hi'
        have hlen := congrArg List.length hstack
        simp only [List.length_map, List.length_append] at hlen
        have hheight : f.vals.length - ins.length = front.length := by omega
        have hbound : ins.length ≤ f.vals.length := by omega
        have hargs : ResultsTyped s ins (f.vals.drop front.length) := by
          apply results_typed_drop (before := front)
          simpa only [hstack] using values
        have hargtypes := results_type_of_typed hargs
        have hfront : (f.vals.take front.length).map valueType = front := by
          rw [List.map_take, hstack, List.take_left]
        have hcaller : FrameTyped s { f with vals := f.vals.take front.length, code := after } outs := by
          apply FrameTyped.mk (f := { f with vals := f.vals.take front.length, code := after }) C
            bindings localTypes locals (results_typed_take front.length values) returns ?_ hw
          simpa only [hfront] using hafter
        have hcallerHeights : FrameHeights { f with vals := f.vals.take front.length, code := after } := by
          intro label hm
          have hh := heights label hm
          simp only [List.length_take]
          omega
        cases hcode : fn.CODE with
        | HOST identity =>
          have observed := step
          simp [astep,call,hresolve,hfn,htype',hbound,hheight,hargtypes,hcode] at observed
          obtain ⟨rfl,rfl,rfl,rfl⟩ := observed
          refine ⟨⟨typed.store,typed.functions,typed.ambient,.cons hcaller hr,
            by simp,rfl,?_⟩,identity,ins,?_ ,hargs⟩
          · intro frame member
            rcases List.mem_cons.mp member with rfl | member
            · exact hcallerHeights
            · exact typed.heights frame (by simp [member])
          · refine ⟨fn.MODULE,?_⟩
            have record : fn = ⟨⟨.mk_list ins,.mk_list outs⟩,fn.MODULE,.HOST identity⟩ := by
              cases fn with
              | MKfuncinst ft mm cd =>
                simp only [funcinst.TYPE] at htype'
                simp only [funcinst.CODE] at hcode
                subst ft
                subst cd
                rfl
            rw [← record]
            exact hfn
        | FUNC fi fl body =>
          cases defaults : defaultLocals fl <;>
            simp [astep,call,hresolve,hfn,htype',hbound,hheight,hargtypes,hcode,defaults] at step
end Itasca.SourceMachine

end

/-! ## HostCallSite -/

section

namespace Itasca.SourceMachine
open WebAssembly Itasca.Spec

/-- The source context around an abstract host boundary is recovered from
instruction typing and actual address/argument extraction. -/
theorem host_call_site (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (index address : Nat)
    (args : List val) (results : List valtype) (resume : AState)
    (typed : ATyped ⟨s,ambient,{f with code := .CALL (.mk_uN index) :: after} :: rest,[]⟩)
    (step : astep ⟨s,ambient,{f with code := .CALL (.mk_uN index) :: after} :: rest,[]⟩ =
      .host address args results resume) :
    ∃ front, f.vals = front ++ args ∧
      resume = ⟨s,ambient,{f with vals := front,code := after} :: rest,[]⟩ ∧
      f.module.FUNCS[index]? = some address ∧ index < 2^32 ∧
      wf_frame f.toFrame ∧ LabelsWf f.labels ∧ Forall wf_val front ∧
      Forall wf_instr after ∧ Forall FrameWf rest ∧
      (∀ label ∈ f.labels, label.height ≤ front.length) := by
  have frames := typed.frames
  cases frames with
  | cons hf hr =>
    cases hf with
    | mk C bindings localTypes locals values returns hc hw =>
      simp only [List.append_nil] at hc
      obtain ⟨front, ins, outs, hop, hstack, hafter, heights⟩ :=
        code_stack_after_bounds (value_types_concrete f.vals) hc
      cases hop with
      | call _ _ inputs outputs hi ht _ wfInstruction =>
        simp only [labelContext, proj_uN_0] at hi ht
        have hi' : index < f.module.FUNCS.length := by
          rw [bindings.funcs.length_eq]
          exact hi
        obtain ⟨fn, hfn, htype⟩ := bindings.funcs.get hi' hi
        simp only [List.get_eq_getElem] at hfn htype
        have htype' : fn.TYPE = ⟨.mk_list ins, .mk_list outs⟩ := by
          rw [htype]
          simpa only [getElem!_pos C.FUNCS index hi] using ht
        have hresolve := List.getElem?_eq_getElem hi'
        have hlen := congrArg List.length hstack
        simp only [List.length_map, List.length_append] at hlen
        have hheight : f.vals.length - ins.length = front.length := by omega
        have hbound : ins.length ≤ f.vals.length := by omega
        have hargs : ResultsTyped s ins (f.vals.drop front.length) := by
          apply results_typed_drop (before := front)
          simpa only [hstack] using values
        have hargtypes := results_type_of_typed hargs
        have hfront : (f.vals.take front.length).map valueType = front := by
          rw [List.map_take, hstack, List.take_left]
        have hcaller : FrameTyped s { f with vals := f.vals.take front.length, code := after } outs := by
          apply FrameTyped.mk (f := { f with vals := f.vals.take front.length, code := after }) C
            bindings localTypes locals (results_typed_take front.length values) returns ?_ hw
          simpa only [hfront] using hafter
        have hcallerHeights : FrameHeights { f with vals := f.vals.take front.length, code := after } := by
          intro label hm
          have hh := heights label hm
          simp only [List.length_take]
          omega
        cases hcode : fn.CODE with
        | HOST identity =>
          have observed := step
          simp [astep,call,hresolve,hfn,htype',hbound,hheight,hargtypes,hcode] at observed
          obtain ⟨rfl,rfl,rfl,rfl⟩ := observed
          refine ⟨f.vals.take front.length,(List.take_append_drop _ _).symm,rfl,hresolve,?_,hw,
            code_stack_labels_wf hc,?_,?_,frames_typed_wf hr,hcallerHeights⟩
          · cases wfInstruction with
            | instr_case_10 _ bounded => cases bounded with
              | uN_case_0 _ bounds => norm_num at bounds ⊢; omega
          · exact fun value member => results_typed_wf values value (List.mem_of_mem_take member)
          · exact fun instruction member => code_stack_wf hc instruction (by simp [member])
        | FUNC fi fl body =>
          cases defaults : defaultLocals fl <;>
            simp [astep,call,hresolve,hfn,htype',hbound,hheight,hargtypes,hcode,defaults] at step
/-- Resume the exact source continuation stored by the host boundary. -/
def finishHost (pending : AState) (after : store) (values : List val) : AState :=
  {pending with store := after, frames := match pending.frames with
    | [] => []
    | f :: rest => {f with vals := f.vals ++ values} :: rest}

theorem HostPending.finish_typed {state : AState} {types : List valtype}
    (pending : HostPending state types) {after : WebAssembly.store}
    (extension : Extend_store state.store after) (functions : FunctionsTyped after)
    {values : List val} (typed : ResultsTyped after types values) :
    ATyped (finishHost state after values) := by
  obtain ⟨f,rest,frames,valid⟩ := pending.resume extension functions typed
  simpa only [finishHost,frames,pending.values] using valid

end Itasca.SourceMachine

end

/-! ## DecodeDepth -/

section

namespace Itasca.SourceMachine

@[simp] theorem instr_depth_value (value : val) : Spec.instrDepth (admininstr_val value) = 0 := by
  cases value <;> rfl

@[simp] theorem instr_depth_source (instruction : instr) :
    Spec.instrDepth (admininstr_instr instruction) = 0 := by
  cases instruction <;> rfl

@[simp] theorem instrs_depth_values (values : List val) : Spec.instrsDepth (WebAssembly.vals values) = 0 := by
  induction values with
  | nil => rfl
  | cons value rest ih => simpa only [WebAssembly.vals, List.map_cons, Spec.instrsDepth, instr_depth_value, Nat.zero_max] using ih

@[simp] theorem instrs_depth_source (instructions : List instr) :
    Spec.instrsDepth (instructions.map admininstr_instr) = 0 := by
  induction instructions with
  | nil => rfl
  | cons instruction rest ih => simp [Spec.instrsDepth, ih]

/-- Label contexts do not introduce administrative function frames. -/
@[simp] theorem decode_labels_depth (labels : List Label) (values : List val) (code : List admininstr) :
    Spec.instrsDepth (decodeLabels labels values code) = Spec.instrsDepth code := by
  induction labels generalizing values code with
  | nil => simp [decodeLabels]
  | cons label rest ih => simp only [decodeLabels, ih, List.singleton_append, Spec.instrsDepth, Spec.instrDepth,
      Spec.instrs_depth_append, instrs_depth_values, instrs_depth_source, Nat.zero_max, Nat.max_zero]

/-- Each retained abstract function contributes exactly one FRAME_ node. -/
@[simp] theorem decode_frames_depth (frames : List AFrame) (inner : List admininstr) :
    Spec.instrsDepth (decodeFrames frames inner) = Spec.instrsDepth inner + frames.length := by
  induction frames generalizing inner with
  | nil => simp
  | cons f rest ih => simp [decodeFrames, ih, Spec.instrDepth, Nat.add_assoc, Nat.add_comm]

@[simp] theorem decode_depth (source : AState) :
    Spec.frameDepth (decode source) = source.frames.length := by
  simp [decode, Spec.frameDepth]

end Itasca.SourceMachine

end

end

/-! ## TypedSelect -/

section

/-! ## Correct -/

section

namespace Itasca.SourceMachine.TypedSelect
open WebAssembly Itasca.Spec

open Itasca.SourceMachine.Core

theorem signature {C : context} {annotation : Option (List valtype)} {inputs outputs : List valtype}
    (typed : Instr_ok C (.SELECT annotation) ⟨.mk_list inputs,.mk_list outputs⟩) :
    ∃ ty, inputs = [ty,ty,.I32] ∧ outputs = [ty] := by
  cases typed <;> exact ⟨_,rfl,rfl⟩

theorem frame_preservation {s : store} {f : AFrame} {after : List instr} {annotation : Option (List valtype)}
    {front : List val} {left right : val} {bits : Nat}
    (typed : FrameTyped s {f with code := .SELECT annotation :: after, vals := front ++ [left,right,integerVal .I32 bits]} []) :
    FrameTyped s {f with code := after, vals := front ++ [if bits = 0 then right else left]} [] := by
  cases typed with
  | mk C bindings localTypes locals values returns hc hw =>
    simp only [List.append_nil] at hc
    obtain ⟨base,ins,outs,operation,stack,continuation⟩ :=
      code_stack_after (value_types_concrete (front ++ [left,right,integerVal .I32 bits])) hc
    obtain ⟨ty,rfl,rfl⟩ := signature operation
    simp only [List.map_append,List.map_cons,List.map_nil] at stack
    have length : (front.map valueType).length = base.length := by
      have lengths := congrArg List.length stack
      simp only [List.length_append,List.length_cons,List.length_nil] at lengths
      omega
    obtain ⟨baseEq,types⟩ := List.append_inj stack length
    simp only [List.cons.injEq] at types
    have leftType : valueType left = ty := types.1
    have rightType : valueType right = ty := types.2.1
    have selectedTyped : Val_ok s (if bits = 0 then right else left) ty := by
      split
      · simpa only [rightType] using results_typed_self_mem (value := right) values (by simp)
      · simpa only [leftType] using results_typed_self_mem (value := left) values (by simp)
    have selectedType := value_type_of_typed selectedTyped
    have prefixTyped : ResultsTyped s (front.map valueType) front := by
      simpa using results_typed_take front.length values
    apply FrameTyped.mk (f := {f with code := after, vals := front ++ [if bits = 0 then right else left]}) C
      bindings localTypes locals ?_ returns ?_ hw
    · simpa only [ResultsTyped,List.map_append,List.map_cons,List.map_nil,selectedType] using
        List.rel_append prefixTyped (List.Forall₂.cons selectedTyped List.Forall₂.nil)
    · simpa only [List.map_append,List.map_cons,List.map_nil,List.append_nil,selectedType,baseEq] using continuation

theorem simulation (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (annotation : Option (List valtype)) (after : List instr) (front : List val) (left right : val) (bits : Nat)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val front)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ front.length)
    (leftWf : wf_val left) (rightWf : wf_val right) (bitsBound : bits < 2^32) :
    StepH (decode ⟨s,ambient,
      {f with code := .SELECT annotation :: after, vals := front ++ [left,right,integerVal .I32 bits]} :: rest,[]⟩) []
      (decode ⟨s,ambient,{f with code := after, vals := front ++ [if bits = 0 then right else left]} :: rest,[]⟩) := by
  have conditionWf := integer_val_wf .I32 bits bitsBound
  have selectWf : wf_instr (.SELECT annotation) := .instr_case_3 _
  apply pure_stack_simulation s ambient f rest (.SELECT annotation) after front
    [left,right,integerVal .I32 bits] [if bits = 0 then right else left]
    hs ha hf hl hv hc hr heights
  · simpa [Forall] using And.intro leftWf (And.intro rightWf conditionWf)
  · by_cases zero : bits = 0 <;> simp [zero,Forall,leftWf,rightWf]
  · exact selectWf
  · by_cases zero : bits = 0
    · simpa [vals,integerVal,admininstr_val,admininstr_instr,numtype_Inn,zero] using
        Step_pure.select_false left right (.mk_num__0 .I32 (.mk_uN bits)) annotation
          (by simp [proj_num__0]) (by simpa [proj_num__0,proj_uN_0]) leftWf rightWf
          (.admininstr_case_13 _ _ (integer_num_wf .I32 bits bitsBound)) (wf_admininstr_instr selectWf)
    · simpa [vals,integerVal,admininstr_val,admininstr_instr,numtype_Inn,zero] using
        Step_pure.select_true left right (.mk_num__0 .I32 (.mk_uN bits)) annotation
          (by simp [proj_num__0]) (by simpa [proj_num__0,proj_uN_0]) leftWf rightWf
          (.admininstr_case_13 _ _ (integer_num_wf .I32 bits bitsBound)) (wf_admininstr_instr selectWf)

/-- The generated select rule supplies two equally typed alternatives and an
i32 condition, so the executable branch is total on every typed frame. -/
theorem progress (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (annotation : Option (List valtype)) (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .SELECT annotation :: after} :: rest,[]⟩) :
    ∃ next, select ⟨s,ambient,{f with code := .SELECT annotation :: after} :: rest,[]⟩
      f rest after = .next next ∧ CoreTyped next ∧
      StepH (decode ⟨s,ambient,{f with code := .SELECT annotation :: after} :: rest,[]⟩) [] (decode next) := by
  have frameTyped : FrameTyped s {f with code := .SELECT annotation :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,ins,outs,_,_,operation,split,operandTypes,frontWf,heights⟩ :=
    frame_typed_operands_bounds frameTyped
  obtain ⟨ty,rfl,rfl⟩ := signature operation
  cases operandTypes with
  | cons leftTyped tail =>
    cases tail with
    | cons rightTyped tail =>
      cases tail with
      | cons conditionTyped tail =>
        cases tail
        rename_i left right condition
        obtain ⟨bits,rfl,bitsBound⟩ := integer_val_inv (ty := .I32) conditionTyped
        have matching : valueType left = valueType right :=
          (value_type_of_typed leftTyped).trans (value_type_of_typed rightTyped).symm
        have continuation := frame_preservation (bits := bits) (by simpa only [split] using frameTyped)
        have fresh := active_frame_preservation typed.typed continuation rfl
        let next : AState := ⟨s,ambient,
          {f with code := after, vals := front ++ [if bits = 0 then right else left]} :: rest,[]⟩
        refine ⟨next,?_,⟨fresh,typed.contents⟩,?_⟩
        · have shape : f.vals = ((front ++ [left]) ++ [right]) ++ [integerVal .I32 bits] := by
            simpa only [List.append_assoc,List.cons_append,List.nil_append] using split
          have decoded : integer .I32 (integerVal .I32 bits) = some bits := by
            simpa only [numtype_Inn] using integer_accepts .I32 bits bitsBound
          simp only [select,shape,pop_append,decoded,matching,
            ite_true,advance,next]
        · obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frame_typed_wf frameTyped
          have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
          have restWf : Forall FrameWf rest := by
            cases typed.typed.frames with | cons _ tail => exact frames_typed_wf tail
          have source := simulation s ambient f rest annotation after front left right bits
            typed.typed.store typed.typed.ambient frameWf labelsWf frontWf tailWf restWf heights
            (val_ok_wf leftTyped) (val_ok_wf rightTyped) bitsBound
          simpa only [split,next] using source

end Itasca.SourceMachine.TypedSelect

end

/-! ## Step -/

section

namespace Itasca.SourceMachine.TypedSelect
open WebAssembly Itasca.Spec Itasca.SourceMachine.Ownership

/-- Explicit select uses the deterministic value choice, with the type
annotation retained in its source configuration. -/
inductive Step : AState → AState → Prop where
  | next {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
      {declared : valtype} {after : List instr} {next : AState}
      (equation : Core.select ⟨s,ambient,{f with code := .SELECT (some [declared])::after}::rest,[]⟩
        f rest after = .next next) :
      Step ⟨s,ambient,{f with code := .SELECT (some [declared])::after}::rest,[]⟩ next

theorem Step.next_supported {before next}
    (step : Step before next) (covered : SupportedState before) : SupportedState next := by
  cases step with
  | next equation =>
    have frame := covered.active _ (List.mem_cons_self ..)
    simp only [Core.select] at equation
    repeat' first | split at equation | contradiction
    all_goals
      apply Supported.advance_covered covered equation
      exact ⟨fun i member => frame.1 i (List.mem_cons_of_mem _ member),frame.2⟩

theorem Step.next_bound {bound before next} (step : Step before next)
    (bounded : CodeBound bound before) : CodeBound bound next := by
  cases step with
  | next equation =>
    have frame := bounded.frames _ (List.mem_cons_self ..)
    simp only [Core.select] at equation
    repeat' first | split at equation | contradiction
    all_goals
      apply advance_bound bounded equation
      refine ⟨?_,frame.2⟩
      have size := frame.1
      simp at size ⊢
      omega

theorem Step.next_owned {bounds before next} (step : Step before next)
    (owned : StatefulOwned bounds before) : StatefulOwned bounds next := by
  cases step with
  | @next s ambient f rest declared after next equation =>
    have frame := owned.values.2 _ (List.mem_cons_self ..)
    have remaining : ∀ g ∈ rest, FrameOwned bounds g :=
      fun g member => owned.values.2 g (List.mem_cons_of_mem _ member)
    simp only [Core.select] at equation
    repeat' first | split at equation | contradiction
    all_goals
      apply stateful_owned_advance (step := equation) owned.heap (values_owned_nil _) ?_ remaining
      refine ⟨frame.1,?_⟩
      have values := frame.2
      aesop (add safe forward ValuesOwned.pop)

end Itasca.SourceMachine.TypedSelect

end

end
