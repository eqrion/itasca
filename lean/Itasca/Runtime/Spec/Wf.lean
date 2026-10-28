import Itasca.Runtime.Spec.Steps

namespace Itasca.Runtime.Spec
open SpecExt

@[simp] theorem forall_nil {α : Type} (P : α → Prop) : Forall P [] := by
  simp [Forall]

theorem forall_append {α : Type} {P : α → Prop} {xs ys : List α}
    (hx : Forall P xs) (hy : Forall P ys) : Forall P (xs ++ ys) := by
  intro x h
  rcases List.mem_append.mp h with h | h
  · exact hx x h
  · exact hy x h

theorem wf_config_parts {z : state} {body : List admininstr}
    (h : wf_config (.mk_config z body)) :
    wf_state z ∧ Forall wf_admininstr body := by
  cases h with | config_case_0 _ _ hz hb => exact ⟨hz, hb⟩

theorem wf_state_parts {s : store} {f : frame} (h : wf_state (.mk_state s f)) :
    wf_store s ∧ wf_frame f := by
  cases h with | state_case_0 _ _ hs hf => exact ⟨hs, hf⟩

theorem wf_config_make {s : store} {f : frame} {body : List admininstr}
    (hs : wf_store s) (hf : wf_frame f) (hb : Forall wf_admininstr body) :
    wf_config (.mk_config (.mk_state s f) body) :=
  .config_case_0 _ _ (.state_case_0 _ _ hs hf) hb

theorem wf_admininstr_val {v : val} (h : wf_val v) : wf_admininstr (admininstr_val v) := by
  cases h <;> simp only [admininstr_val]
  all_goals constructor <;> assumption

theorem wf_admininstr_instr {i : instr} (h : wf_instr i) :
    wf_admininstr (admininstr_instr i) := by
  cases h <;> simp only [admininstr_instr]
  all_goals constructor <;> assumption

theorem wf_instrs {code : List instr} (h : Forall wf_instr code) :
    Forall wf_admininstr (code.map admininstr_instr) := by
  intro ai hai
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hai
  exact wf_admininstr_instr (h i hi)

theorem val_ok_wf {s : store} {v : val} {t : valtype} (h : Val_ok s v t) : wf_val v := by
  cases h with
  | numtype _ _ _ hw => exact hw
  | vectype _ _ _ hw => exact hw
  | reftype _ _ hr _ => cases hr <;> simp only [val_ref] <;> constructor

theorem resultsTyped_length {s : store} {ts : List valtype} {vs : List val}
    (h : ResultsTyped s ts vs) : vs.length = ts.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem resultsTyped_wf {s : store} {ts : List valtype} {vs : List val}
    (h : ResultsTyped s ts vs) : Forall wf_val vs := by
  induction h with
  | nil => exact forall_nil _
  | cons hv _ ih =>
    intro v hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact val_ok_wf hv
    · exact ih v hm

theorem wf_vals {vs : List val} (h : Forall wf_val vs) : Forall wf_admininstr (vals vs) := by
  intro ai hai
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hai
  exact wf_admininstr_val (h v hv)

theorem wf_config_vals {s : store} {f : frame} {vs : List val}
    (hs : wf_store s) (hf : wf_frame f) (hv : Forall wf_val vs) :
    wf_config (.mk_config (.mk_state s f) (vals vs)) :=
  wf_config_make hs hf (wf_vals hv)

theorem wf_config_trap {s : store} {f : frame} (hs : wf_store s) (hf : wf_frame f) :
    wf_config (.mk_config (.mk_state s f) [.TRAP]) := by
  apply wf_config_make hs hf
  intro ai hai
  simp only [List.mem_singleton] at hai
  subst ai
  exact .admininstr_case_73

theorem wf_config_label {z : state} {body : List admininstr} {cont : List instr}
    (arity : Nat) (h : wf_config (.mk_config z body)) (hc : Forall wf_instr cont) :
    wf_config (.mk_config z [.LABEL_ arity cont body]) := by
  obtain ⟨hz, hb⟩ := wf_config_parts h
  apply wf_config.config_case_0 _ _ hz
  intro ai hai
  simp only [List.mem_singleton] at hai
  subst ai
  exact .admininstr_case_71 _ _ _ hc hb

theorem wf_config_frame {s : store} {inner outer : frame} {body : List admininstr}
    (arity : Nat) (h : wf_config (.mk_config (.mk_state s inner) body))
    (hf : wf_frame outer) :
    wf_config (.mk_config (.mk_state s outer) [.FRAME_ arity inner body]) := by
  obtain ⟨hz, hb⟩ := wf_config_parts h
  obtain ⟨hs, hi⟩ := wf_state_parts hz
  apply wf_config_make hs hf
  intro ai hai
  simp only [List.mem_singleton] at hai
  subst ai
  exact .admininstr_case_72 _ _ _ hi hb

theorem wf_config_instrs {z : state} {body after : List admininstr} {vs : List val}
    (h : wf_config (.mk_config z body)) (hv : Forall wf_val vs)
    (ha : Forall wf_admininstr after) :
    wf_config (.mk_config z (vals vs ++ (body ++ after))) := by
  obtain ⟨hz, hb⟩ := wf_config_parts h
  exact .config_case_0 _ _ hz (forall_append (wf_vals hv) (forall_append hb ha))

end Itasca.Runtime.Spec
