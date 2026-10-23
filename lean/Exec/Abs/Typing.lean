import Exec.Abs.Step
import Exec.Spec.Wf
import Itasca.Spec.TypingInversion

/-! Local typing facts for the integer abstract machine. These lemmas use the
generated value/instruction predicates; whole-state preservation and progress
require the label/caller typing invariant and are not asserted here. -/

namespace Exec.Abs
open SpecExt Exec.Spec

def integerWidth : Inn → Nat
  | .I32 => 32
  | .I64 => 64

theorem integer_uN_wf (ty : Inn) (bits : Nat) (h : bits < 2 ^ integerWidth ty) :
    wf_uN (integerWidth ty) (.mk_uN bits) := by
  apply wf_uN.uN_case_0
  cases ty <;> norm_num [integerWidth] at h ⊢ <;> omega

theorem integer_num_wf (ty : Inn) (bits : Nat) (h : bits < 2 ^ integerWidth ty) :
    wf_num_ (numtype_Inn ty) (.mk_num__0 ty (.mk_uN bits)) := by
  apply wf_num_.num__case_0 _ _ _ ?_ ?_ rfl
  · cases ty <;> decide
  · cases ty <;> exact integer_uN_wf _ bits h

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

theorem codeStack_height_bound {C : context} {labels : List Label}
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

theorem frameTyped_heights {s : store} {f : AFrame} (h : FrameTyped s f []) : FrameHeights f := by
  cases h with
  | mk C _ _ _ _ _ code _ =>
    intro label hm
    simpa only [List.length_append, List.length_nil, Nat.add_zero, List.length_map] using
      codeStack_height_bound code label hm

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
theorem valueType_ne_bot (value : val) : valueType value ≠ .BOT := by
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

end Exec.Abs
