import Itasca.Runtime.SourceMachine.Definitions
import WebAssembly.Host

open WebAssembly

/-!
Proofs for Runtime / SourceMachine.

This module collects Simulation, Decode.
Each section documents its contracts and consumers.
-/

/-! ## Simulation -/

section

/-!
# Internal source-machine invariants

Flat-frame typing, ownership and administrative progress are construction
invariants for the simulation. Public contracts use specification reductions,
source call sites and resource bounds without requiring these proof witnesses.
-/

namespace Itasca.SourceMachine
open WebAssembly

/-- Pending instructions in the active frame. Suspended callers do not affect
the bound on consecutive administrative constant moves; real steps may reset it. -/
def administrativeMeasure (s : AState) : Nat :=
  match s.frames with
  | [] => 0
  | f :: _ => f.code.length

end Itasca.SourceMachine


/-! ## SourceMachine / Ownership -/

section SourceMachineOwnership

/-!
### Source reference ownership

Distinct function and external address bounds apply to values, frames and mutable heap objects. Stateful ownership combines the value and heap obligations.
-/

section

/-!
## Source value and frame ownership

Bounds and value/frame/state ownership relate source references and globals to the store
in which they are interpreted.
-/

namespace Itasca.SourceMachine.Ownership

/-- Source function and external references use distinct issued address spaces. -/
structure Bounds where
  functions : Nat
  externs : Nat

/-- Only non-null references carry an ownership obligation. -/
def ValueOwned (bound : Bounds) : val → Prop
  | .REF_FUNC_ADDR address => address < bound.functions
  | .REF_HOST_ADDR address => address < bound.externs
  | _ => True

def ValuesOwned (bound : Bounds) (values : List val) : Prop := ∀ value ∈ values, ValueOwned bound value

def FrameOwned (bound : Bounds) (f : AFrame) : Prop :=
  ValuesOwned bound f.locals ∧ ValuesOwned bound f.vals

def StateOwned (bound : Bounds) (s : AState) : Prop :=
  ValuesOwned bound s.results ∧ ∀ f ∈ s.frames, FrameOwned bound f

end Itasca.SourceMachine.Ownership

namespace Itasca.SourceMachine.Ownership

open WebAssembly

def GlobalsOwned (bounds : Bounds) (s : WebAssembly.store) : Prop :=
  ∀ object ∈ s.GLOBALS, ValueOwned bounds object.VALUE

end Itasca.SourceMachine.Ownership

end

section

/-!
## Stateful source ownership

Reference and heap ownership predicates retain the source-store membership needed by
stateful instruction effects.
-/

namespace Itasca.SourceMachine.Ownership

open WebAssembly

def ReferencesOwned (bounds : Bounds) (values : List ref) : Prop :=
  ∀ value ∈ values, ValueOwned bounds (val_ref value)

structure StatefulHeapOwned (bounds : Bounds) (s : store) : Prop where
  globals : GlobalsOwned bounds s
  tables : ∀ object ∈ s.TABLES, ReferencesOwned bounds object.REFS
  elements : ∀ object ∈ s.ELEMS, ReferencesOwned bounds object.REFS
  functions : s.FUNCS.length ≤ bounds.functions

structure StatefulOwned (bounds : Bounds) (s : AState) : Prop where
  values : StateOwned bounds s
  heap : StatefulHeapOwned bounds s.store

end Itasca.SourceMachine.Ownership

end

end SourceMachineOwnership


namespace Itasca.SourceMachine
open WebAssembly

/-- The outermost active function retains the invocation's declared results;
inner callees may have independent signatures. -/
inductive FramesReturn (expected : List valtype) : List AFrame → Prop where
  | last {f : AFrame} : f.resultTypes = expected → FramesReturn expected [f]
  | under {f : AFrame} {rest : List AFrame} : FramesReturn expected rest → FramesReturn expected (f :: rest)

/-- Attach an invocation signature until all frames finish, then require its
actual returned values to have that exact signature. -/
def InvocationResult (expected : List valtype) (s : AState) : Prop :=
  match s.frames with
  | [] => ResultsTyped s.store expected s.results
  | frames => FramesReturn expected frames

end Itasca.SourceMachine


namespace Itasca.SourceMachine
open WebAssembly

/-- Source support is independent of values and concrete bytecode emission. -/
def FrameSupported (f : AFrame) : Prop :=
  Forall BinaryInstr f.code ∧ Forall (fun label => Forall BinaryInstr label.cont ∧ Forall BinaryInstr label.after) f.labels

end Itasca.SourceMachine


namespace Itasca.SourceMachine
open WebAssembly

structure SupportedState (s : AState) : Prop where
  active : Forall (FrameSupported) s.frames
  functions : FunctionsSupported s.store

end Itasca.SourceMachine


namespace Itasca.SourceMachine
open WebAssembly

inductive AResult where
  | next (state : AState)
  | done (values : List val)
  | trap
  | host (address : funcaddr) (args : List val) (resultTypes : List valtype) (resume : AState)
  | stuck

end Itasca.SourceMachine


namespace Itasca.SourceMachine
open WebAssembly

def valueType : val → valtype
  | .CONST ty _ => valtype_numtype ty
  | .VCONST _ _ => .V128
  | .REF_NULL rt => valtype_reftype rt
  | .REF_FUNC_ADDR _ => .FUNCREF
  | .REF_HOST_ADDR _ => .EXTERNREF

def defaultValue : valtype → Option val
  | .I32 => some (integerVal .I32 0)
  | .I64 => some (integerVal .I64 0)
  | .F32 => some (.CONST .F32 (.mk_num__1 .F32 (.POS (.SUBNORM 0))))
  | .F64 => some (.CONST .F64 (.mk_num__1 .F64 (.POS (.SUBNORM 0))))
  | .V128 => some (.VCONST .V128 (.mk_uN 0))
  | .FUNCREF => some (.REF_NULL .FUNCREF)
  | .EXTERNREF => some (.REF_NULL .EXTERNREF)
  | .BOT => none

def defaultLocals : List «local» → Option (List val)
  | [] => some []
  | .LOCAL ty :: rest => do
      let value ← defaultValue ty
      let values ← defaultLocals rest
      pure (value :: values)

/-- Calls resolve through the active module's address map. Host calls suspend
with a typed expected result list, ready for the checked host-extension boundary. -/
def call (s : AState) (f : AFrame) (rest : List AFrame) (index : Nat)
    (after : List instr) : AResult :=
  match f.module.FUNCS[index]? with
  | none => .stuck
  | some address =>
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

end Itasca.SourceMachine


namespace Itasca.SourceMachine
open WebAssembly

def labelContext (C : context) (labels : List Label) : context :=
  { C with LABELS := labels.map (fun label => .mk_list label.branchTypes) }

/-- Source typing for the current code and every suspended label continuation.
Saved stack types are explicit and tied to each absolute label height. -/
inductive CodeStackTyped (C : context) :
    List Label → List valtype → List instr → List valtype → Prop where
  | outer {stack code results} :
      Instrs_ok (labelContext C []) code ⟨.mk_list stack, .mk_list results⟩ →
      CodeStackTyped C [] stack code results
  | label {label labels saved operands code results} :
      saved.length = label.height →
      (∀ outer ∈ labels, outer.height ≤ label.height) →
      Instrs_ok (labelContext C (label :: labels)) code
        ⟨.mk_list operands, .mk_list label.resultTypes⟩ →
      Instrs_ok (labelContext C labels) label.cont
        ⟨.mk_list label.branchTypes, .mk_list label.resultTypes⟩ →
      CodeStackTyped C labels (saved ++ label.resultTypes) label.after results →
      CodeStackTyped C (label :: labels) (saved ++ operands) code results

/-- A suspended caller is typed with the callee's pending result types appended
to its current operand values. For the active frame this list is empty. -/
inductive FrameTyped (s : store) (f : AFrame) (incoming : List valtype) : Prop where
  | mk (C : context) :
      ModuleBindings s f.module C →
      C.LOCALS = f.locals.map valueType →
      ResultsTyped s C.LOCALS f.locals →
      ResultsTyped s (f.vals.map valueType) f.vals →
      C.RETURN = some (.mk_list f.resultTypes) →
      CodeStackTyped C f.labels (f.vals.map valueType ++ incoming) f.code f.resultTypes →
      wf_frame f.toFrame → FrameTyped s f incoming

/-- Every saved label prefix already exists in the frame's current values;
pending callee results must never be counted as part of that prefix. -/
def FrameHeights (f : AFrame) : Prop :=
  ∀ label ∈ f.labels, label.height ≤ f.vals.length

inductive FramesTyped (s : store) : List AFrame → List valtype → Prop where
  | nil (results) : FramesTyped s [] results
  | cons {frame rest incoming} :
      FrameTyped s frame incoming →
      FramesTyped s rest frame.resultTypes →
      FramesTyped s (frame :: rest) incoming

/-- Each callable defined body has a generated source typing derivation under
its owning module's actual bindings. The owning context has no ambient
locals, labels, or return type; Func_ok installs precisely the callee's own
locals and entry label. Host bodies are provided by StepH. -/
def FunctionsTyped (s : store) : Prop :=
  ∀ fn ∈ s.FUNCS, match fn.CODE with
    | .HOST _ => Functype_ok fn.TYPE
    | .FUNC index locals body => ∃ C, ModuleBindings s fn.MODULE C ∧
        C.LOCALS = [] ∧ C.LABELS = [] ∧ C.RETURN = none ∧
        Func_ok C (.FUNC index locals body) fn.TYPE

structure ATyped (s : AState) : Prop where
  store : wf_store s.store
  functions : FunctionsTyped s.store
  ambient : wf_frame s.ambient
  frames : FramesTyped s.store s.frames []
  results : Forall wf_val s.results
  activeResults : s.frames ≠ [] → s.results = []
  heights : Forall FrameHeights s.frames

end Itasca.SourceMachine


namespace Itasca.SourceMachine
open WebAssembly

/-- Semantic typing of store payloads used by mutable instructions. Function
bodies remain in `ATyped.functions`; object-payload obligations are explicit here. -/
structure StoreContentsTyped (s : store) : Prop where
  globals : ∀ global ∈ s.GLOBALS, Globalinst_ok s global global.TYPE
  tables : ∀ table ∈ s.TABLES, Tableinst_ok s table table.TYPE
  memories : ∀ memory ∈ s.MEMS, Meminst_ok s memory memory.TYPE
  elements : ∀ element ∈ s.ELEMS, Eleminst_ok s element element.TYPE
  data : ∀ entry ∈ s.DATAS, Datainst_ok s entry .OK

structure CoreTyped (s : AState) : Prop where
  typed : ATyped s
  contents : StoreContentsTyped s.store

end Itasca.SourceMachine


namespace Itasca.Spec
open WebAssembly

/-- A finite machine run carrying the events from each dispatch. -/
inductive Iterations {S : Type} (next : S → List HostEvent → S → Prop) :
    Nat → S → List HostEvent → S → Prop where
  | refl (s : S) : Iterations next 0 s [] s
  | cons {n : Nat} {s s' s'' : S} {events rest : List HostEvent} :
      next s events s' → Iterations next n s' rest s'' →
      Iterations next (n + 1) s (events ++ rest) s''

end Itasca.Spec

end

/-! ## Decode -/

section

/-! ## Decode -/

section

/-! Reconstruct nested specification evaluation contexts from flat frames and
absolute label heights. The innermost frame's current values and code appear
at the unique redex position, before the suspended callers' continuations. -/

namespace Itasca.SourceMachine
open WebAssembly

@[simp] theorem decode_labels_nil (values : List val) (code : List admininstr) :
    decodeLabels [] values code = vals values ++ code := rfl

@[simp] theorem decode_frames_nil (code : List admininstr) : decodeFrames [] code = code := rfl

end Itasca.SourceMachine

end

end
