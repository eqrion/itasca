import Exec.Abs.Numeric.Astep
import Exec.Abs.Safety
import Exec.Abs.PureHead

namespace Itasca.Runtime.Abs
open SpecExt Itasca.Runtime.Spec

theorem const_progress (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (code : List instr) (ty : Inn) (number : iN)
    (h : FrameTyped s { f with code := .CONST (numtype_Inn ty) (.mk_num__0 ty number) :: code } []) :
    astep ⟨s, ambient,
      { f with code := .CONST (numtype_Inn ty) (.mk_num__0 ty number) :: code } :: rest, []⟩ ≠ .stuck := by
  cases h with
  | mk C bindings localTypes locals values returns hc hw =>
    have hi := codeStack_wf hc (.CONST (numtype_Inn ty) (.mk_num__0 ty number)) (by simp)
    cases hi with
    | instr_case_13 _ _ hn =>
      obtain ⟨bits, heq, hb⟩ := integer_num_inv hn
      cases number with
      | mk_uN n =>
        simp only [num_.mk_num__0.injEq, uN.mk_uN.injEq, true_and] at heq
        subst n
        cases ty <;>
          simp_all [astep, integer, integerWidth, numtype_Inn, advance]

theorem blockType_of_typing {C : context} {m : moduleinst} {bt : blocktype}
    {ft : functype} (types : C.TYPES = m.TYPES) (h : Blocktype_ok C bt ft) :
    blockType m bt = some ft := by
  cases h with
  | valtype opt _ _ => cases opt <;> rfl
  | typeidx index inputs outputs hi heq _ _ =>
    cases index with
    | mk_uN index =>
      simp only [proj_uN_0] at hi heq
      simp only [blockType, ← types, List.getElem?_eq_getElem hi]
      congr 1
      simpa only [getElem!_pos C.TYPES index hi] using heq

/-- Empty source code has equal input/output stacks once bottom types are
excluded by actual runtime values. -/
theorem concrete_empty {C : context} {actual expected : List valtype}
    (hc : Forall (fun ty => ty ≠ valtype.BOT) actual)
    (h : Instrs_ok C [] ⟨.mk_list actual, .mk_list expected⟩) : actual = expected :=
  concrete_result_sub_eq hc (Itasca.DeclarativeComplete.empty_sub h)

theorem value_types_concrete (values : List val) :
    Forall (fun ty => ty ≠ valtype.BOT) (values.map valueType) := by
  intro ty hty
  obtain ⟨value, _, rfl⟩ := List.mem_map.mp hty
  exact valueType_ne_bot value

def EmptyShape (labels : List Label) (stack results : List valtype) : Prop :=
  match labels with
  | [] => stack = results
  | label :: _ => ∃ saved, stack = saved ++ label.resultTypes ∧ saved.length = label.height

theorem code_empty_shape {C : context} {labels : List Label}
    {stack results : List valtype}
    (concrete : Forall (fun ty => ty ≠ valtype.BOT) stack)
    (h : CodeStackTyped C labels stack [] results) :
    EmptyShape labels stack results := by
  cases h with
  | outer code => exact concrete_empty concrete code
  | @label label labels saved operands _ _ height nesting code cont after =>
    have hoperands : Forall (fun ty => ty ≠ valtype.BOT) operands :=
      fun ty hty => concrete ty (List.mem_append_right saved hty)
    have heq := concrete_empty hoperands code
    exact ⟨saved, by rw [heq], height⟩

/-- Every permitted local type has the zero/null default prescribed by Wasm. -/
theorem defaultValue_exists {ty : valtype} (h : ty ≠ .BOT) :
    ∃ value, defaultValue ty = some value := by
  cases ty <;> simp_all [defaultValue]

theorem defaultLocals_exists (types : List valtype)
    (h : Forall (fun ty => ty ≠ valtype.BOT) types) :
    ∃ values, defaultLocals (types.map local.LOCAL) = some values := by
  induction types with
  | nil => exact ⟨[], rfl⟩
  | cons ty types ih =>
    obtain ⟨value, hv⟩ := defaultValue_exists (h ty (by simp))
    obtain ⟨values, hs⟩ := ih (fun ty ht => h ty (by simp [ht]))
    exact ⟨value :: values, by simp [defaultLocals, hv, hs]⟩

theorem function_defaults {s : store} {fn : funcinst} {index : idx}
    {locals : List «local»} {body : expr} (hfunctions : FunctionsTyped s)
    (hmem : fn ∈ s.FUNCS) (hcode : fn.CODE = .FUNC index locals body) :
    ∃ values, defaultLocals locals = some values := by
  have h := hfunctions fn hmem
  simp only [hcode] at h
  obtain ⟨C, bindings, _, _, _, typed⟩ := h
  generalize hft : fn.TYPE = ft at typed
  cases typed with
  | mk_Func_ok _ types _ _ _ _ _ nonbot _ _ _ _ =>
    exact defaultLocals_exists types nonbot

end Itasca.Runtime.Abs
