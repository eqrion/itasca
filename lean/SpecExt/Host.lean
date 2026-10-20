import «wasm2.0»
import Batteries.Data.List.Basic

/-!
Host extension of the generated Wasm 2.0 reduction relation. Host calls are
atomic: an event records the directly invoked host function, its arguments,
and its return or trap. Reentrant Wasm calls are subsumed by that transition;
a separate invocation has its own trace.

The host representation follows the pinned SpecTec 3.0 funccode backport.
The host behavior follows the Wasm execution prose: typed inputs and outputs,
unchanged function instances, and store extension. Every completed callback must leave a source-typed store, including a callback
that traps after committing effects.
-/

namespace SpecExt

/-- Administrative instructions representing a sequence of values. -/
def vals (vs : List val) : List admininstr := vs.map admininstr_val

/-- Values have exactly the given types and arity in the current store. -/
def ResultsTyped (s : store) (ts : List valtype) (vs : List val) : Prop :=
  List.Forall₂ (Val_ok s) vs ts

/-- A direct host call; `none` records a trap. -/
inductive HostEvent where
  | call (fa : funcaddr) (args : List val) (out : Option (List val))
  deriving DecidableEq

/-- The function address denotes host code with the indicated signature. -/
def HostFunction (s : store) (fa : funcaddr) (id : Nat)
    (params results : List valtype) : Prop :=
  ∃ mm, s.FUNCS[fa]? = some {
    TYPE := functype.mk_functype (.mk_list params) (.mk_list results)
    MODULE := mm
    CODE := funccode.HOST id }

/-- Generated reduction plus host calls and the same evaluation contexts. -/
inductive StepH : config → List HostEvent → config → Prop where
  | step {c c' : config} : Step c c' → StepH c [] c'
  | host_return {s s' : store} {f : frame} {fa : funcaddr} {id : Nat}
      {params results : List valtype} {args res : List val} :
      HostFunction s fa id params results →
      ResultsTyped s params args →
      Extend_store s s' →
      Store_ok s' →
      ResultsTyped s' results res →
      wf_config (.mk_config (.mk_state s f) (vals args ++ [.CALL_ADDR fa])) →
      wf_config (.mk_config (.mk_state s' f) (vals res)) →
      StepH (.mk_config (.mk_state s f) (vals args ++ [.CALL_ADDR fa]))
        [.call fa args (some res)] (.mk_config (.mk_state s' f) (vals res))
  | host_trap {s s' : store} {f : frame} {fa : funcaddr} {id : Nat}
      {params results : List valtype} {args : List val} :
      HostFunction s fa id params results →
      ResultsTyped s params args →
      Extend_store s s' →
      Store_ok s' →
      wf_config (.mk_config (.mk_state s f) (vals args ++ [.CALL_ADDR fa])) →
      wf_config (.mk_config (.mk_state s' f) [.TRAP]) →
      StepH (.mk_config (.mk_state s f) (vals args ++ [.CALL_ADDR fa]))
        [.call fa args none] (.mk_config (.mk_state s' f) [.TRAP])
  | ctxt_label {z z' : state} {arity : Nat} {cont : List instr}
      {body body' : List admininstr} {events : List HostEvent} :
      StepH (.mk_config z body) events (.mk_config z' body') →
      wf_config (.mk_config z [.LABEL_ arity cont body]) →
      wf_config (.mk_config z' [.LABEL_ arity cont body']) →
      wf_config (.mk_config z body) →
      wf_config (.mk_config z' body') →
      StepH (.mk_config z [.LABEL_ arity cont body]) events
        (.mk_config z' [.LABEL_ arity cont body'])
  | ctxt_frame {s s' : store} {f inner inner' : frame} {arity : Nat}
      {body body' : List admininstr} {events : List HostEvent} :
      StepH (.mk_config (.mk_state s inner) body) events
        (.mk_config (.mk_state s' inner') body') →
      wf_config (.mk_config (.mk_state s f) [.FRAME_ arity inner body]) →
      wf_config (.mk_config (.mk_state s' f) [.FRAME_ arity inner' body']) →
      wf_config (.mk_config (.mk_state s inner) body) →
      wf_config (.mk_config (.mk_state s' inner') body') →
      StepH (.mk_config (.mk_state s f) [.FRAME_ arity inner body]) events
        (.mk_config (.mk_state s' f) [.FRAME_ arity inner' body'])
  | ctxt_instrs {z z' : state} {vs : List val}
      {body body' after : List admininstr} {events : List HostEvent} :
      StepH (.mk_config z body) events (.mk_config z' body') →
      (vs ≠ [] ∨ after ≠ []) →
      wf_config (.mk_config z (vals vs ++ (body ++ after))) →
      wf_config (.mk_config z' (vals vs ++ (body' ++ after))) →
      wf_config (.mk_config z body) →
      wf_config (.mk_config z' body') →
      StepH (.mk_config z (vals vs ++ (body ++ after))) events
        (.mk_config z' (vals vs ++ (body' ++ after)))

/-- Reflexive-transitive reduction, concatenating direct host events in order. -/
inductive StepsH : config → List HostEvent → config → Prop where
  | refl {c : config} : wf_config c → StepsH c [] c
  | cons {c c' c'' : config} {events rest : List HostEvent} :
      StepH c events c' → StepsH c' rest c'' → StepsH c (events ++ rest) c''

end SpecExt
