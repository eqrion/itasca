import Itasca.Runtime.SourceMachine.Decode
import Itasca.Runtime.SourceMachine.Numeric.Decode
import Itasca.Runtime.Spec.Integer
import Itasca.Spec.TypingInversion

/-!
Sections, each formerly its own module: Step, Typing.
-/

/-! ## Step -/

section

/-! Executable abstract transition for the integer vertical slice. Other
instruction families return `stuck` until their transition cases are added;
no total-Wasm progress claim is made by this definition. -/

namespace Itasca.Runtime.SourceMachine

inductive AResult where
  | next (state : AState)
  | done (values : List val)
  | trap
  | host (address : funcaddr) (args : List val) (resultTypes : List valtype) (resume : AState)
  | stuck

/-- Remove the top value while retaining bottom-to-top stack order. -/
def pop (values : List val) : Option (List val × val) :=
  match values.reverse with
  | [] => none
  | value :: rest => some (rest.reverse, value)

/-- Numeric tags are checked in addition to their enclosing value tag. -/
def integer (ty : numtype) : val → Option Nat
  | .CONST ty' (.mk_num__0 ity (.mk_uN bits)) =>
      if ty = ty' ∧ ty = numtype_Inn ity ∧ bits < 2 ^ (if ty = .I32 then 32 else 64)
      then some bits else none
  | _ => none

def integerVal (ty : Inn) (bits : Nat) : val :=
  .CONST (numtype_Inn ty) (.mk_num__0 ty (.mk_uN bits))

def valueType : val → valtype
  | .CONST ty _ => valtype_numtype ty
  | .VCONST _ _ => .V128
  | .REF_NULL rt => valtype_reftype rt
  | .REF_FUNC_ADDR _ => .FUNCREF
  | .REF_HOST_ADDR _ => .EXTERNREF

def advance (s : AState) (f : AFrame) (rest : List AFrame) : AResult :=
  .next { s with frames := f :: rest }

namespace Numeric

/-- Finish one well-tagged integer operation, preserving all non-stack fields. -/
def finish (s : AState) (f : AFrame) (rest : List AFrame) (after : List instr)
    (front : List val) (op : Instruction)
    (a b : BitVec (sizenn (numtype_Inn op.input))) : AResult :=
  match op.apply a b with
  | none => .trap
  | some result => advance s
      { f with code := after, vals := front ++ [integerVal op.output result.toNat] } rest

/-- Checked stack decoding for every scalar integer descriptor. -/
def transition (s : AState) (f : AFrame) (rest : List AFrame)
    (after : List instr) (op : Instruction) : AResult :=
  match pop f.vals with
  | none => .stuck
  | some (front, right) =>
    match integer (numtype_Inn op.input) right with
    | none => .stuck
    | some rightBits =>
      let b := BitVec.ofNat (sizenn (numtype_Inn op.input)) rightBits
      if op.arity = 1 then finish s f rest after front op b b else
      match pop front with
      | none => .stuck
      | some (front, left) =>
        match integer (numtype_Inn op.input) left with
        | none => .stuck
        | some leftBits => finish s f rest after front op
            (BitVec.ofNat (sizenn (numtype_Inn op.input)) leftBits) b

end Numeric

/-- All callers of this helper have already checked operand widths. -/
def integerBinary (op : binop_Inn) (width a b : Nat) : Option Nat :=
  match op with
  | .ADD => some ((a + b) % 2 ^ width)
  | .SUB => some ((a + 2 ^ width - b) % 2 ^ width)
  | _ => none

def blockType (m : moduleinst) : blocktype → Option functype
  | ._RESULT none => some ⟨.mk_list [], .mk_list []⟩
  | ._RESULT (some ty) => some ⟨.mk_list [], .mk_list [ty]⟩
  | ._IDX (.mk_uN i) => m.TYPES[i]?

/-- A branch exits the target label. A loop's continuation re-enters its loop. -/
def branch (s : AState) (f : AFrame) (rest : List AFrame) (depth : Nat) : AResult :=
  match f.labels[depth]? with
  | none => .stuck
  | some target =>
    if target.height + target.arity ≤ f.vals.length ∧
        (f.vals.drop (f.vals.length - target.arity)).map valueType = target.branchTypes then
      advance s { f with vals := f.vals.take target.height ++ f.vals.drop (f.vals.length - target.arity), labels := f.labels.drop (depth + 1), code := target.cont ++ target.after } rest
    else .stuck

def enterLabel (s : AState) (f : AFrame) (rest : List AFrame)
    (bt : blocktype) (body after : List instr) (loop : Bool) : AResult :=
  match blockType f.module bt with
  | none => .stuck
  | some ⟨.mk_list params, .mk_list results⟩ =>
    if params.length ≤ f.vals.length ∧
        (f.vals.drop (f.vals.length - params.length)).map valueType = params then
      let label : Label := {
        branchTypes := if loop then params else results
        resultTypes := results
        cont := if loop then [.LOOP bt body] else []
        height := f.vals.length - params.length
        after := after }
      advance s { f with code := body, labels := label :: f.labels } rest
    else .stuck

/-- Return discards labels and passes only the declared number of results. -/
def returnFrame (s : AState) (f : AFrame) (rest : List AFrame) : AResult :=
  if f.arity ≤ f.vals.length ∧
      (f.vals.drop (f.vals.length - f.arity)).map valueType = f.resultTypes then
    let results := f.vals.drop (f.vals.length - f.arity)
    match rest with
    | [] => .next { s with frames := [], results := results }
    | caller :: callers => advance s { caller with vals := caller.vals ++ results } callers
  else .stuck

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

def astep (s : AState) : AResult :=
  match s.frames with
  | [] => .done s.results
  | f :: rest =>
    match f.code with
    | [] =>
      match f.labels with
      | [] => returnFrame s f rest
      | label :: labels =>
        if f.vals.length = label.height + label.resultTypes.length ∧
            (f.vals.drop label.height).map valueType = label.resultTypes then
          advance s { f with labels := labels, code := label.after } rest
        else .stuck
    | instruction :: after =>
      match instruction with
      | .NOP => advance s { f with code := after } rest
      | .UNREACHABLE => .trap
      | .CONST ty value =>
        match integer ty (.CONST ty value) with
        | some _ => advance s { f with code := after, vals := f.vals ++ [.CONST ty value] } rest
        | none => .stuck
      | .DROP =>
        match pop f.vals with
        | none => .stuck
        | some (values, _) => advance s { f with code := after, vals := values } rest
      | .LOCAL_GET (.mk_uN i) =>
        match f.locals[i]? with
        | none => .stuck
        | some value => advance s { f with code := after, vals := f.vals ++ [value] } rest
      | .LOCAL_SET (.mk_uN i) | .LOCAL_TEE (.mk_uN i) =>
        match pop f.vals, f.locals[i]? with
        | some (values, value), some old =>
          if valueType value = valueType old then
            advance s { f with code := after, locals := f.locals.set i value, vals := if instruction = .LOCAL_SET (.mk_uN i) then values else f.vals } rest
          else .stuck
        | _, _ => .stuck
      | .BINOP ty (.mk_binop__0 ity op) =>
        match pop f.vals with
        | some (values, rhs) =>
          match pop values with
          | some (values, lhs) =>
            match integer ty lhs, integer ty rhs with
            | some a, some b =>
              if ty = numtype_Inn ity then
                match integerBinary op (if ty = .I32 then 32 else 64) a b with
                | some bits => advance s { f with code := after, vals := values ++ [integerVal ity bits] } rest
                | none => Numeric.transition s f rest after (.binary ity op)
              else .stuck
            | _, _ => .stuck
          | none => .stuck
        | none => .stuck
      | .TESTOP ty (.mk_testop__0 ity .EQZ) =>
        match pop f.vals with
        | some (values, value) =>
          match integer ty value with
          | some bits =>
            if ty = numtype_Inn ity then advance s { f with code := after, vals := values ++ [integerVal .I32 (if bits = 0 then 1 else 0)] } rest
            else .stuck
          | none => .stuck
        | none => .stuck
      | .RELOP ty (.mk_relop__0 ity op) =>
        match pop f.vals with
        | some (values, rhs) =>
          match pop values with
          | some (values, lhs) =>
            match integer ty lhs, integer ty rhs with
            | some a, some b =>
              if ty = numtype_Inn ity then
                let answer := match op with
                  | .EQ => some (decide (a = b))
                  | .LT .U => some (decide (a < b))
                  | _ => none
                match answer with
                | some yes => advance s { f with code := after, vals := values ++ [integerVal .I32 (if yes then 1 else 0)] } rest
                | none => Numeric.transition s f rest after (.compare ity op)
              else .stuck
            | _, _ => .stuck
          | none => .stuck
        | none => .stuck
      | .BLOCK bt body => enterLabel s f rest bt body after false
      | .LOOP bt body => enterLabel s f rest bt body after true
      | .IFELSE bt yes no =>
        match pop f.vals with
        | some (values, condition) =>
          match integer .I32 condition with
          | some bits => advance s { f with vals := values, code := .BLOCK bt (if bits = 0 then no else yes) :: after } rest
          | none => .stuck
        | none => .stuck
      | .BR (.mk_uN depth) => branch s f rest depth
      | .BR_IF (.mk_uN depth) =>
        match pop f.vals with
        | some (values, condition) =>
          match integer .I32 condition with
          | some bits => advance s { f with vals := values, code := if bits = 0 then after else .BR (.mk_uN depth) :: after } rest
          | none => .stuck
        | none => .stuck
      | .CALL (.mk_uN index) => call s f rest index after
      | .RETURN => returnFrame s f rest
      | _ =>
        match Numeric.decodeInstruction instruction with
        | some op => Numeric.transition s f rest after op
        | none => .stuck

end Itasca.Runtime.SourceMachine

end

/-! ## Typing -/

section

/-! Local typing facts for the integer abstract machine. These lemmas use the
generated value/instruction predicates; whole-state preservation and progress
require the label/caller typing invariant and are not asserted here. -/

namespace Itasca.Runtime.SourceMachine
open SpecExt Itasca.Runtime.Spec

def integerWidth : Inn → Nat
  | .I32 => 32
  | .I64 => 64

theorem integer_u_n_wf (ty : Inn) (bits : Nat) (h : bits < 2 ^ integerWidth ty) :
    wf_uN (integerWidth ty) (.mk_uN bits) := by
  apply wf_uN.uN_case_0
  cases ty <;> norm_num [integerWidth] at h ⊢ <;> omega

theorem integer_num_wf (ty : Inn) (bits : Nat) (h : bits < 2 ^ integerWidth ty) :
    wf_num_ (numtype_Inn ty) (.mk_num__0 ty (.mk_uN bits)) := by
  apply wf_num_.num__case_0 _ _ _ ?_ ?_ rfl
  · cases ty <;> decide
  · cases ty <;> exact integer_u_n_wf _ bits h

theorem integer_val_wf (ty : Inn) (bits : Nat) (h : bits < 2 ^ integerWidth ty) :
    wf_val (integerVal ty bits) :=
  .val_case_0 _ _ (integer_num_wf ty bits h)

theorem integer_val_typed {s : store} (hs : wf_store s) (ty : Inn) (bits : Nat)
    (h : bits < 2 ^ integerWidth ty) :
    Val_ok s (integerVal ty bits) (valtype_numtype (numtype_Inn ty)) :=
  .numtype s _ _ hs (integer_val_wf ty bits h)

/-- The dynamic integer check accepts every well-formed integer encoding. -/
theorem integer_accepts (ty : Inn) (bits : Nat) (h : bits < 2 ^ integerWidth ty) :
    integer (numtype_Inn ty) (integerVal ty bits) = some bits := by
  cases ty <;> simp_all [integer, integerVal, numtype_Inn, integerWidth]

/-- Runtime module bindings describe the source typing context through checked
addresses. This avoids the generated Moduleinst_ok's unrelated export-membership
side condition, and admits genuine host functions by their declared type. -/
structure ModuleBindings (s : store) (m : moduleinst) (C : context) : Prop where
  types : C.TYPES = m.TYPES
  funcs : List.Forall₂ (fun address ty =>
    ∃ fn, s.FUNCS[address]? = some fn ∧ fn.TYPE = ty) m.FUNCS C.FUNCS
  globals : List.Forall₂ (fun address ty =>
    Externaddr_ok s (.GLOBAL address) (.GLOBAL ty)) m.GLOBALS C.GLOBALS
  tables : List.Forall₂ (fun address ty =>
    Externaddr_ok s (.TABLE address) (.TABLE ty)) m.TABLES C.TABLES
  mems : List.Forall₂ (fun address ty =>
    Externaddr_ok s (.MEM address) (.MEM ty)) m.MEMS C.MEMS
  elems : List.Forall₂ (fun address ty =>
    ∃ entry, s.ELEMS[address]? = some entry ∧ Eleminst_ok s entry ty) m.ELEMS C.ELEMS
  datas : List.Forall₂ (fun address ty =>
    ∃ entry, s.DATAS[address]? = some entry ∧ Datainst_ok s entry ty) m.DATAS C.DATAS
  wf : wf_context C

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

theorem code_stack_height_bound {C : context} {labels : List Label}
    {stack results : List valtype} {code : List instr}
    (h : CodeStackTyped C labels stack code results) :
    ∀ label ∈ labels, label.height ≤ stack.length := by
  cases h with
  | outer => simp
  | label height nesting _ _ _ =>
    intro label hm
    simp only [List.mem_cons] at hm
    rcases hm with rfl | hm
    · simp only [List.length_append]; omega
    · have hh := nesting label hm
      simp only [List.length_append]; omega

theorem frame_typed_heights {s : store} {f : AFrame} (h : FrameTyped s f []) : FrameHeights f := by
  cases h with
  | mk C _ _ _ _ _ code _ =>
    intro label hm
    simpa only [List.length_append, List.length_nil, Nat.add_zero, List.length_map] using
      code_stack_height_bound code label hm

theorem replace_frame_heights {f f' : AFrame} {rest : List AFrame}
    (h : Forall FrameHeights (f :: rest)) (hf' : FrameHeights f') :
    Forall FrameHeights (f' :: rest) := by
  intro frame hm
  simp only [List.mem_cons] at hm
  rcases hm with rfl | hm
  · exact hf'
  · exact h frame (by simp [hm])

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

/-- A concrete value can never have the bottom stack type. -/
theorem value_type_ne_bot (value : val) : valueType value ≠ .BOT := by
  cases value <;> simp only [valueType]
  · rename_i ty value
    cases ty <;> decide
  · decide
  · rename_i ty
    cases ty <;> decide
  · decide
  · decide

/-- Subtyping cannot change any actual operand type. -/
theorem concrete_result_sub_eq {actual expected : List valtype}
    (concrete : Forall (fun ty => ty ≠ valtype.BOT) actual)
    (h : Resulttype_sub (.mk_list actual) (.mk_list expected)) : actual = expected := by
  have rel := Itasca.DeclarativeComplete.result_sub_iff.mp h
  clear h
  induction rel with
  | nil => rfl
  | @cons a b tailA tailB hab hs ih =>
    have ha := concrete a (by simp)
    have hab' : a = b := by cases hab <;> simp_all
    subst b
    have htail : Forall (fun ty => ty ≠ valtype.BOT) tailA := fun t ht => concrete t (by simp [ht])
    rw [ih htail]

theorem value_type_of_typed {s : store} {value : val} {ty : valtype}
    (h : Val_ok s value ty) : valueType value = ty := by
  cases h with
  | numtype => rfl
  | vectype ty _ _ _ => cases ty; rfl
  | reftype _ _ hr _ => cases hr <;> rfl

theorem results_type_of_typed {s : store} {values : List val} {types : List valtype}
    (h : ResultsTyped s types values) : values.map valueType = types := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp only [List.map_cons, value_type_of_typed h, ih]

theorem integer_num_inv {ty : Inn} {number : num_}
    (h : wf_num_ (numtype_Inn ty) number) :
    ∃ bits, number = .mk_num__0 ty (.mk_uN bits) ∧ bits < 2 ^ integerWidth ty := by
  cases h with
  | num__case_0 ity bits _ hw heq =>
    have same : ity = ty := by cases ty <;> cases ity <;> simp_all [numtype_Inn]
    subst ity
    cases bits with
    | mk_uN bits =>
      refine ⟨bits, rfl, ?_⟩
      cases hw with
      | uN_case_0 _ hb =>
        cases ty <;> norm_num [integerWidth, size, valtype_Inn] at hb ⊢ <;> omega
  | num__case_1 fty _ _ heq =>
    cases ty <;> cases fty <;> simp_all [numtype_Inn, numtype_Fnn]

/-- Generated integer value typing supplies exactly the dynamic check's domain. -/
theorem integer_val_inv {s : store} {ty : Inn} {value : val}
    (h : Val_ok s value (valtype_numtype (numtype_Inn ty))) :
    ∃ bits, value = integerVal ty bits ∧ bits < 2 ^ integerWidth ty := by
  have hw := val_ok_wf h
  have ht := value_type_of_typed h
  cases hw with
  | val_case_0 nt number hn =>
    have same : nt = numtype_Inn ty := by cases nt <;> cases ty <;> simp_all [valueType, valtype_numtype, numtype_Inn]
    subst nt
    obtain ⟨bits, rfl, hb⟩ := integer_num_inv hn
    exact ⟨bits, rfl, hb⟩
  | val_case_1 vt bits _ => cases ty <;> simp_all [valueType, valtype_numtype, numtype_Inn]
  | val_case_2 rt => cases ty <;> cases rt <;> simp_all [valueType, valtype_numtype, valtype_reftype, numtype_Inn]
  | val_case_3 address => cases ty <;> simp_all [valueType, valtype_numtype, numtype_Inn]
  | val_case_4 address => cases ty <;> simp_all [valueType, valtype_numtype, numtype_Inn]

end Itasca.Runtime.SourceMachine

end
