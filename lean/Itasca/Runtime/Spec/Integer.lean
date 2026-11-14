import SpecExt.Builtins
import «wasm2.0»
import Mathlib.Tactic
import SpecExt.Builtins.Float.Sign

/-!
Sections, each formerly its own module: Steps, Wf, Extend, Mutation, ExtensionTyping, Float, Context, Integer.
-/

/-! ## Steps -/

section

/-!
Host-extended source execution sequences and event traces. Runtime correspondence and exact recording compose these source runs without assuming a chosen host reply.
-/

namespace Itasca.Runtime.Spec
open SpecExt

/-- Endpoint well-formedness follows directly from generated constructors.
This proof deliberately does not use the unfinished Step_is_wf theorem. -/
theorem step_wf {c c' : config} (h : Step c c') : wf_config c ∧ wf_config c' := by
  cases h <;> exact ⟨by assumption, by assumption⟩

theorem step_h_wf {c c' : config} {es : List HostEvent}
    (h : StepH c es c') : wf_config c ∧ wf_config c' := by
  cases h with
  | step h => exact step_wf h
  | _ => exact ⟨by assumption, by assumption⟩

theorem steps_h_wf {c c' : config} {es : List HostEvent}
    (h : StepsH c es c') : wf_config c ∧ wf_config c' := by
  induction h with
  | refl h => exact ⟨h, h⟩
  | cons h _ ih => exact ⟨(step_h_wf h).1, ih.2⟩

theorem steps_h_single {c c' : config} {es : List HostEvent}
    (h : StepH c es c') : StepsH c es c' := by
  simpa using StepsH.cons h (StepsH.refl (step_h_wf h).2)

theorem steps_h_trans {c c' c'' : config} {es rest : List HostEvent}
    (h : StepsH c es c') (h' : StepsH c' rest c'') :
    StepsH c (es ++ rest) c'' := by
  induction h with
  | refl _ => simpa using h'
  | cons h _ ih => simpa [List.append_assoc] using StepsH.cons h (ih h')

end Itasca.Runtime.Spec

end

/-! ## Wf -/

section

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

theorem results_typed_length {s : store} {ts : List valtype} {vs : List val}
    (h : ResultsTyped s ts vs) : vs.length = ts.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem results_typed_wf {s : store} {ts : List valtype} {vs : List val}
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

end

/-! ## Extend -/

section

/-! Store extension facts for the generated relation, including its explicit
well-formedness premises. No generated well-formedness theorem is used. -/

namespace Itasca.Runtime.Spec

theorem extend_func_refl (x : funcinst) (h : wf_funcinst x) : Extend_funcinst x x := by
  cases x
  exact .mk_Extend_funcinst _ _ _ h

theorem extend_global_refl (x : globalinst) (h : wf_globalinst x) : Extend_globalinst x x := by
  rcases x with ⟨⟨mutability, ty⟩, value⟩
  exact .mk_Extend_globalinst _ _ _ _ (Or.inr rfl) h h

theorem extend_mem_refl (x : meminst) (h : wf_meminst x) : Extend_meminst x x := by
  rcases x with ⟨⟨⟨⟨n⟩, max⟩⟩, bytes⟩
  cases max with
  | none => exact .mk_Extend_meminst n none bytes n bytes (Nat.le_refl _) (Nat.le_refl _) h h
  | some max =>
    cases max with
    | mk_uN m => exact .mk_Extend_meminst n (some m) bytes n bytes (Nat.le_refl _) (Nat.le_refl _) h h

theorem extend_table_refl (x : tableinst) (h : wf_tableinst x) : Extend_tableinst x x := by
  rcases x with ⟨⟨⟨⟨n⟩, max⟩, rt⟩, refs⟩
  cases max with
  | none => exact .mk_Extend_tableinst n none rt refs n refs (Nat.le_refl _) (Nat.le_refl _) h h
  | some max =>
    cases max with
    | mk_uN m => exact .mk_Extend_tableinst n (some m) rt refs n refs (Nat.le_refl _) (Nat.le_refl _) h h

theorem extend_data_refl (x : datainst) (h : wf_datainst x) : Extend_datainst x x := by
  cases x
  exact .mk_Extend_datainst _ _ (Or.inl rfl) h h

theorem extend_elem_refl (x : eleminst) : Extend_eleminst x x := by
  cases x
  exact .mk_Extend_eleminst _ _ _ (Or.inl rfl)

private theorem at_wf {α : Type} [Inhabited α] {p : α → Prop} {xs : List α}
    (h : Forall p xs) {i : Nat} (hi : i < xs.length) : p xs[i]! := by
  simpa only [getElem!_pos xs i hi] using h xs[i] (List.getElem_mem hi)

/-- Every well-formed store extends itself, including stores with host functions. -/
theorem extend_store_refl (s : store) (h : wf_store s) : Extend_store s s := by
  have bounds {α : Type} (xs : List α) : Forall (fun i => i < xs.length) (List.range xs.length) := by
    intro i hi
    exact List.mem_range.mp hi
  cases h with
  | store_case_ funcs globals tables mems elems datas hf hg ht hm hd =>
    apply Extend_store.mk_Extend_store
    all_goals first
      | exact bounds _
      | exact wf_store.store_case_ _ _ _ _ _ _ hf hg ht hm hd
      | (intro i hi; exact extend_global_refl _ (at_wf hg (List.mem_range.mp hi)))
      | (intro i hi; exact extend_mem_refl _ (at_wf hm (List.mem_range.mp hi)))
      | (intro i hi; exact extend_table_refl _ (at_wf ht (List.mem_range.mp hi)))
      | (intro i hi; exact extend_func_refl _ (at_wf hf (List.mem_range.mp hi)))
      | (intro i hi; exact extend_data_refl _ (at_wf hd (List.mem_range.mp hi)))
      | (intro i hi; exact extend_elem_refl _)

theorem extend_func_trans {a b c : funcinst}
    (h : Extend_funcinst a b) (h' : Extend_funcinst b c) : Extend_funcinst a c := by
  cases h
  exact h'

theorem extend_global_trans {a b c : globalinst}
    (h : Extend_globalinst a b) (h' : Extend_globalinst b c) : Extend_globalinst a c := by
  cases h with
  | mk_Extend_globalinst mutability ty x y xy hx hy =>
    cases h' with
    | mk_Extend_globalinst _ _ _ z yz _ hz =>
      apply Extend_globalinst.mk_Extend_globalinst _ _ _ _ _ hx hz
      rcases xy with hm | rfl
      · exact Or.inl hm
      · exact yz

theorem extend_data_trans {a b c : datainst}
    (h : Extend_datainst a b) (h' : Extend_datainst b c) : Extend_datainst a c := by
  cases h with
  | mk_Extend_datainst x y xy hx hy =>
    cases h' with
    | mk_Extend_datainst _ z yz _ hz =>
      apply Extend_datainst.mk_Extend_datainst _ _ _ hx hz
      rcases xy with rfl | hy0
      · exact yz
      · rcases yz with rfl | hz0
        · exact Or.inr hy0
        · exact Or.inr hz0

theorem extend_elem_trans {a b c : eleminst}
    (h : Extend_eleminst a b) (h' : Extend_eleminst b c) : Extend_eleminst a c := by
  cases h with
  | mk_Extend_eleminst ty x y xy =>
    cases h' with
    | mk_Extend_eleminst _ _ z yz =>
      apply Extend_eleminst.mk_Extend_eleminst
      rcases xy with rfl | hy0
      · exact yz
      · rcases yz with rfl | hz0
        · exact Or.inr hy0
        · exact Or.inr hz0


private theorem extend_mem_inv {a b : meminst} (h : Extend_meminst a b) :
    ∃ n mx xs n' ys,
      a = ⟨.PAGE ⟨.mk_uN n, OMap uN.mk_uN mx⟩, xs⟩ ∧
      b = ⟨.PAGE ⟨.mk_uN n', OMap uN.mk_uN mx⟩, ys⟩ ∧
      n ≤ n' ∧ xs.length ≤ ys.length ∧ wf_meminst a ∧ wf_meminst b := by
  cases h with
  | mk_Extend_meminst n mx xs n' ys hn hl ha hb =>
    exact ⟨n, mx, xs, n', ys, rfl, rfl, hn, hl, ha, hb⟩

private theorem option_u_n_injective {a b : Option Nat}
    (h : OMap uN.mk_uN a = OMap uN.mk_uN b) : a = b := by
  cases a <;> cases b <;> simp_all [OMap]

theorem extend_mem_trans {a b c : meminst}
    (h : Extend_meminst a b) (h' : Extend_meminst b c) : Extend_meminst a c := by
  obtain ⟨n, mx, xs, n', ys, rfl, rfl, hn, hl, ha, _⟩ := extend_mem_inv h
  obtain ⟨n₂, mx₂, ys₂, n'', zs, heq, rfl, hn', hl', _, hc⟩ := extend_mem_inv h'
  injection heq with hty hbytes
  injection hty with hlim
  injection hlim with hnEq hmx
  injection hnEq with hnEq
  have hmEq := option_u_n_injective hmx
  subst n₂; subst mx₂; subst ys₂
  exact .mk_Extend_meminst _ _ _ _ _ (Nat.le_trans hn hn') (Nat.le_trans hl hl') ha hc

private theorem extend_table_inv {a b : tableinst} (h : Extend_tableinst a b) :
    ∃ n mx rt xs n' ys,
      a = ⟨⟨⟨.mk_uN n, OMap uN.mk_uN mx⟩, rt⟩, xs⟩ ∧
      b = ⟨⟨⟨.mk_uN n', OMap uN.mk_uN mx⟩, rt⟩, ys⟩ ∧
      n ≤ n' ∧ xs.length ≤ ys.length ∧ wf_tableinst a ∧ wf_tableinst b := by
  cases h with
  | mk_Extend_tableinst n mx rt xs n' ys hn hl ha hb =>
    exact ⟨n, mx, rt, xs, n', ys, rfl, rfl, hn, hl, ha, hb⟩

theorem extend_table_trans {a b c : tableinst}
    (h : Extend_tableinst a b) (h' : Extend_tableinst b c) : Extend_tableinst a c := by
  obtain ⟨n, mx, rt, xs, n', ys, rfl, rfl, hn, hl, ha, _⟩ := extend_table_inv h
  obtain ⟨n₂, mx₂, rt₂, ys₂, n'', zs, heq, rfl, hn', hl', _, hc⟩ := extend_table_inv h'
  injection heq with hty hbytes
  injection hty with hlim hrt
  injection hlim with hnEq hmx
  injection hnEq with hnEq
  have hmEq := option_u_n_injective hmx
  subst n₂; subst mx₂; subst ys₂; subst rt₂
  exact .mk_Extend_tableinst _ _ _ _ _ _ (Nat.le_trans hn hn') (Nat.le_trans hl hl') ha hc

private theorem range_bound_trans {α : Type} {β : Type} {γ : Type}
    (xs : List α) (ys : List β) (zs : List γ)
    (h : Forall (fun i => i < ys.length) (List.range xs.length))
    (h' : Forall (fun i => i < zs.length) (List.range ys.length)) :
    Forall (fun i => i < zs.length) (List.range xs.length) := by
  intro i hi
  exact h' i (List.mem_range.mpr (h i hi))

private theorem range_rel_trans {α : Type} [Inhabited α] {R : α → α → Prop}
    (trans : ∀ {a b c}, R a b → R b c → R a c)
    (xs ys zs : List α)
    (hb : Forall (fun i => i < ys.length) (List.range xs.length))
    (h : Forall (fun i => R xs[i]! ys[i]!) (List.range xs.length))
    (h' : Forall (fun i => R ys[i]! zs[i]!) (List.range ys.length)) :
    Forall (fun i => R xs[i]! zs[i]!) (List.range xs.length) := by
  intro i hi
  exact trans (h i hi) (h' i (List.mem_range.mpr (hb i hi)))

/-- Extension composes across host calls and ordinary public store operations. -/
theorem extend_store_trans {a b c : store}
    (h : Extend_store a b) (h' : Extend_store b c) : Extend_store a c := by
  cases h with
  | mk_Extend_store ag bg rg am bm rm atb bt rt af bf rf ad bd rd ae be re ha hb =>
    cases h' with
    | mk_Extend_store _ cg rg' _ cm rm' _ ct rt' _ cf rf' _ cd rd' _ ce re' _ hc =>
      exact .mk_Extend_store a c
        ag (range_bound_trans _ _ _ bg cg) (range_rel_trans (R := Extend_globalinst) extend_global_trans _ _ _ bg rg rg')
        am (range_bound_trans _ _ _ bm cm) (range_rel_trans (R := Extend_meminst) extend_mem_trans _ _ _ bm rm rm')
        atb (range_bound_trans _ _ _ bt ct) (range_rel_trans (R := Extend_tableinst) extend_table_trans _ _ _ bt rt rt')
        af (range_bound_trans _ _ _ bf cf) (range_rel_trans (R := Extend_funcinst) extend_func_trans _ _ _ bf rf rf')
        ad (range_bound_trans _ _ _ bd cd) (range_rel_trans (R := Extend_datainst) extend_data_trans _ _ _ bd rd rd')
        ae (range_bound_trans _ _ _ be ce) (range_rel_trans (R := Extend_eleminst) extend_elem_trans _ _ _ be re re') ha hc

end Itasca.Runtime.Spec

end

/-! ## Mutation -/

section

/-! Store allocation and mutation facts. Every endpoint retains the generated
well-formedness premise; these facts do not assume the stronger `Store_ok`.
Object relations preserve types and allow exactly the mutations admitted by
SpecTec's extension relation. -/

namespace Itasca.Runtime.Spec

/-- Each old address remains present and its object is related. -/
def ObjectsExtend {α : Type} [Inhabited α] (R : α → α → Prop)
    (xs ys : List α) : Prop :=
  xs.length ≤ ys.length ∧ ∀ i, i < xs.length → R xs[i]! ys[i]!

/-- A single object replacement leaves all other addresses unchanged. -/
theorem objects_extend_set {α : Type} [Inhabited α] {R : α → α → Prop}
    {xs : List α} (i : Nat) (value : α) (h : ObjectsExtend R xs xs)
    (hv : i < xs.length → R xs[i]! value) :
    ObjectsExtend R xs (xs.set i value) := by
  refine ⟨by simp, ?_⟩
  intro j hj
  by_cases hij : i = j
  · subst j
    simpa [getElem!_pos, hj] using hv hj
  · simpa [getElem!_pos, hj, List.getElem_set, hij, Ne.symm hij] using h.2 j hj

/-- Pointwise object extension is the generated store relation. -/
theorem extend_store_of_objects {s t : store} (hs : wf_store s) (ht : wf_store t)
    (hglobal : ObjectsExtend Extend_globalinst s.GLOBALS t.GLOBALS)
    (hmem : ObjectsExtend Extend_meminst s.MEMS t.MEMS)
    (htable : ObjectsExtend Extend_tableinst s.TABLES t.TABLES)
    (hfunc : ObjectsExtend Extend_funcinst s.FUNCS t.FUNCS)
    (hdata : ObjectsExtend Extend_datainst s.DATAS t.DATAS)
    (helem : ObjectsExtend Extend_eleminst s.ELEMS t.ELEMS)
    : Extend_store s t := by
  apply Extend_store.mk_Extend_store
  · intro i hi; exact List.mem_range.mp hi
  · intro i hi; exact lt_of_lt_of_le (List.mem_range.mp hi) hglobal.1
  · intro i hi; exact hglobal.2 i (List.mem_range.mp hi)
  · intro i hi; exact List.mem_range.mp hi
  · intro i hi; exact lt_of_lt_of_le (List.mem_range.mp hi) hmem.1
  · intro i hi; exact hmem.2 i (List.mem_range.mp hi)
  · intro i hi; exact List.mem_range.mp hi
  · intro i hi; exact lt_of_lt_of_le (List.mem_range.mp hi) htable.1
  · intro i hi; exact htable.2 i (List.mem_range.mp hi)
  · intro i hi; exact List.mem_range.mp hi
  · intro i hi; exact lt_of_lt_of_le (List.mem_range.mp hi) hfunc.1
  · intro i hi; exact hfunc.2 i (List.mem_range.mp hi)
  · intro i hi; exact List.mem_range.mp hi
  · intro i hi; exact lt_of_lt_of_le (List.mem_range.mp hi) hdata.1
  · intro i hi; exact hdata.2 i (List.mem_range.mp hi)
  · intro i hi; exact List.mem_range.mp hi
  · intro i hi; exact lt_of_lt_of_le (List.mem_range.mp hi) helem.1
  · intro i hi; exact helem.2 i (List.mem_range.mp hi)
  · exact hs
  · exact ht

/-- Extract the pointwise description without using generated metatheorems. -/
theorem extend_store_objects {s t : store} (h : Extend_store s t) :
    ObjectsExtend Extend_globalinst s.GLOBALS t.GLOBALS ∧
    ObjectsExtend Extend_meminst s.MEMS t.MEMS ∧
    ObjectsExtend Extend_tableinst s.TABLES t.TABLES ∧
    ObjectsExtend Extend_funcinst s.FUNCS t.FUNCS ∧
    ObjectsExtend Extend_datainst s.DATAS t.DATAS ∧
    ObjectsExtend Extend_eleminst s.ELEMS t.ELEMS := by
  cases h with
  | mk_Extend_store ag bg rg am bm rm atb bt rt af bf rf ad bd rd ae be re hs ht =>
    have len {α β : Type} (xs : List α) (ys : List β)
        (h : Forall (fun i => i < ys.length) (List.range xs.length)) :
        xs.length ≤ ys.length := by
      by_contra hn
      have hi := h ys.length (List.mem_range.mpr (by omega))
      omega
    exact ⟨⟨len _ _ bg, fun i hi => rg i (List.mem_range.mpr hi)⟩,
      ⟨len _ _ bm, fun i hi => rm i (List.mem_range.mpr hi)⟩,
      ⟨len _ _ bt, fun i hi => rt i (List.mem_range.mpr hi)⟩,
      ⟨len _ _ bf, fun i hi => rf i (List.mem_range.mpr hi)⟩,
      ⟨len _ _ bd, fun i hi => rd i (List.mem_range.mpr hi)⟩,
      ⟨len _ _ be, fun i hi => re i (List.mem_range.mpr hi)⟩⟩

/-- Replace one global object by an extension, preserving all other addresses. -/
theorem extend_store_set_global (s : store) (i : Nat) (value : globalinst)
    (hs : wf_store s) (ht : wf_store { s with GLOBALS := s.GLOBALS.set i value })
    (hv : i < s.GLOBALS.length → Extend_globalinst s.GLOBALS[i]! value) :
    Extend_store s { s with GLOBALS := s.GLOBALS.set i value } := by
  obtain ⟨hg, hm, ht', hf, hd, he⟩ := extend_store_objects (extend_store_refl s hs)
  exact extend_store_of_objects hs ht
    (objects_extend_set i value hg hv) hm ht' hf hd he

/-- Replace one mem object by an extension, preserving all other addresses. -/
theorem extend_store_set_mem (s : store) (i : Nat) (value : meminst)
    (hs : wf_store s) (ht : wf_store { s with MEMS := s.MEMS.set i value })
    (hv : i < s.MEMS.length → Extend_meminst s.MEMS[i]! value) :
    Extend_store s { s with MEMS := s.MEMS.set i value } := by
  obtain ⟨hg, hm, ht', hf, hd, he⟩ := extend_store_objects (extend_store_refl s hs)
  exact extend_store_of_objects hs ht
    hg (objects_extend_set i value hm hv) ht' hf hd he

/-- Replace one table object by an extension, preserving all other addresses. -/
theorem extend_store_set_table (s : store) (i : Nat) (value : tableinst)
    (hs : wf_store s) (ht : wf_store { s with TABLES := s.TABLES.set i value })
    (hv : i < s.TABLES.length → Extend_tableinst s.TABLES[i]! value) :
    Extend_store s { s with TABLES := s.TABLES.set i value } := by
  obtain ⟨hg, hm, ht', hf, hd, he⟩ := extend_store_objects (extend_store_refl s hs)
  exact extend_store_of_objects hs ht
    hg hm (objects_extend_set i value ht' hv) hf hd he

/-- Replace one data object by an extension, preserving all other addresses. -/
theorem extend_store_set_data (s : store) (i : Nat) (value : datainst)
    (hs : wf_store s) (ht : wf_store { s with DATAS := s.DATAS.set i value })
    (hv : i < s.DATAS.length → Extend_datainst s.DATAS[i]! value) :
    Extend_store s { s with DATAS := s.DATAS.set i value } := by
  obtain ⟨hg, hm, ht', hf, hd, he⟩ := extend_store_objects (extend_store_refl s hs)
  exact extend_store_of_objects hs ht
    hg hm ht' hf (objects_extend_set i value hd hv) he

/-- Replace one elem object by an extension, preserving all other addresses. -/
theorem extend_store_set_elem (s : store) (i : Nat) (value : eleminst)
    (hs : wf_store s) (ht : wf_store { s with ELEMS := s.ELEMS.set i value })
    (hv : i < s.ELEMS.length → Extend_eleminst s.ELEMS[i]! value) :
    Extend_store s { s with ELEMS := s.ELEMS.set i value } := by
  obtain ⟨hg, hm, ht', hf, hd, he⟩ := extend_store_objects (extend_store_refl s hs)
  exact extend_store_of_objects hs ht
    hg hm ht' hf hd (objects_extend_set i value he hv)

theorem extend_global_mutable (ty : valtype) (before after : val)
    (hb : wf_globalinst ⟨⟨some .MUT, ty⟩, before⟩)
    (ha : wf_globalinst ⟨⟨some .MUT, ty⟩, after⟩) :
    Extend_globalinst ⟨⟨some .MUT, ty⟩, before⟩ ⟨⟨some .MUT, ty⟩, after⟩ := by
  exact .mk_Extend_globalinst _ _ _ _ (Or.inl rfl) hb ha

/-- Memory contents may change freely while the declared minimum and length grow. -/
theorem extend_mem_contents (n n' : Nat) (maximum : Option Nat) (before after : List byte)
    (hn : n ≤ n') (hl : before.length ≤ after.length)
    (hb : wf_meminst ⟨.PAGE ⟨.mk_uN n, OMap uN.mk_uN maximum⟩, before⟩)
    (ha : wf_meminst ⟨.PAGE ⟨.mk_uN n', OMap uN.mk_uN maximum⟩, after⟩) :
    Extend_meminst ⟨.PAGE ⟨.mk_uN n, OMap uN.mk_uN maximum⟩, before⟩
      ⟨.PAGE ⟨.mk_uN n', OMap uN.mk_uN maximum⟩, after⟩ := by
  exact .mk_Extend_meminst _ _ _ _ _ hn hl hb ha

/-- Table mutation preserves its reference type and maximum, and never shrinks. -/
theorem extend_table_contents (n n' : Nat) (maximum : Option Nat) (ty : reftype)
    (before after : List ref) (hn : n ≤ n') (hl : before.length ≤ after.length)
    (hb : wf_tableinst ⟨⟨⟨.mk_uN n, OMap uN.mk_uN maximum⟩, ty⟩, before⟩)
    (ha : wf_tableinst ⟨⟨⟨.mk_uN n', OMap uN.mk_uN maximum⟩, ty⟩, after⟩) :
    Extend_tableinst ⟨⟨⟨.mk_uN n, OMap uN.mk_uN maximum⟩, ty⟩, before⟩
      ⟨⟨⟨.mk_uN n', OMap uN.mk_uN maximum⟩, ty⟩, after⟩ := by
  exact .mk_Extend_tableinst _ _ _ _ _ _ hn hl hb ha

end Itasca.Runtime.Spec

end

/-! ## ExtensionTyping -/

section

namespace Itasca.Runtime.Spec

theorem extend_store_wf {s t : store} (h : Extend_store s t) : wf_store s ∧ wf_store t := by
  cases h; exact ⟨by assumption, by assumption⟩

theorem extend_func_eq {a b : funcinst} (h : Extend_funcinst a b) : b = a := by
  cases h; rfl

theorem extend_global_type {a b : globalinst} (h : Extend_globalinst a b) : b.TYPE = a.TYPE := by
  cases h; rfl

private theorem limits_grow_sub (n n' : Nat) (mx : Option Nat) (growth : n ≤ n')
    (old : wf_limits ⟨.mk_uN n, OMap uN.mk_uN mx⟩)
    (fresh : wf_limits ⟨.mk_uN n', OMap uN.mk_uN mx⟩) :
    Limits_sub ⟨.mk_uN n', OMap uN.mk_uN mx⟩ ⟨.mk_uN n, OMap uN.mk_uN mx⟩ := by
  cases mx with
  | none => exact .eps n' n growth fresh old
  | some maximum =>
    exact .max n' maximum n (some maximum) growth (by simp [Forall]) fresh old

theorem extend_mem_type_sub {a b : meminst} (h : Extend_meminst a b) :
    Memtype_sub b.TYPE a.TYPE := by
  cases h with
  | mk_Extend_meminst n mx bytes n' bytes' growth _ old fresh =>
    have wo : wf_memtype (.PAGE ⟨.mk_uN n, OMap uN.mk_uN mx⟩) := by cases old; assumption
    have wn : wf_memtype (.PAGE ⟨.mk_uN n', OMap uN.mk_uN mx⟩) := by cases fresh; assumption
    exact .mk_Memtype_sub _ _ (limits_grow_sub n n' mx growth
      (by cases wo; assumption) (by cases wn; assumption)) wn wo

theorem extend_table_type_sub {a b : tableinst} (h : Extend_tableinst a b) :
    Tabletype_sub b.TYPE a.TYPE := by
  cases h with
  | mk_Extend_tableinst n mx rt refs n' refs' growth _ old fresh =>
    have wo : wf_tabletype ⟨⟨.mk_uN n, OMap uN.mk_uN mx⟩, rt⟩ := by cases old; assumption
    have wn : wf_tabletype ⟨⟨.mk_uN n', OMap uN.mk_uN mx⟩, rt⟩ := by cases fresh; assumption
    exact .mk_Tabletype_sub _ rt _ (limits_grow_sub n n' mx growth
      (by cases wo; assumption) (by cases wn; assumption)) wn wo

private theorem memtype_sub_wf {a b : memtype} (h : Memtype_sub a b) : wf_memtype a := by
  cases h; assumption

private theorem tabletype_sub_wf {a b : tabletype} (h : Tabletype_sub a b) : wf_tabletype a := by
  cases h; assumption

/-- Extension preserves every typed external address, including declared
memory/table bounds when the underlying object grows. -/
theorem externaddr_ok_extend {s t : store} (extension : Extend_store s t)
    {address : externaddr} {ty : externtype} (typed : Externaddr_ok s address ty) :
    Externaddr_ok t address ty := by
  obtain ⟨globals, memories, tables, functions, _, _⟩ := extend_store_objects extension
  have fresh := (extend_store_wf extension).2
  induction typed with
  | global address value bound found _ wt =>
    have equal := extend_global_type (globals.2 address bound)
    rw [found] at equal
    rw [← equal] at wt ⊢
    exact .global t address _ (bound.trans_le globals.1) rfl fresh wt
  | func address value bound found _ wt =>
    have equal := extend_func_eq (functions.2 address bound)
    rw [found] at equal
    rw [← equal] at wt ⊢
    exact .func t address _ (bound.trans_le functions.1) rfl fresh wt
  | mem address value bound found _ wt =>
    have sub := extend_mem_type_sub (memories.2 address bound)
    rw [found] at sub
    have newType : wf_externtype (.MEM t.MEMS[address]!.TYPE) := by
      constructor; exact memtype_sub_wf sub
    exact .sub t (.MEM address) (.MEM value.TYPE) (.MEM t.MEMS[address]!.TYPE)
      (.mem t address _ (bound.trans_le memories.1) rfl fresh newType)
      (.mem _ _ sub newType wt) fresh wt newType
  | table address value bound found _ wt =>
    have sub := extend_table_type_sub (tables.2 address bound)
    rw [found] at sub
    have newType : wf_externtype (.TABLE t.TABLES[address]!.TYPE) := by
      constructor; exact tabletype_sub_wf sub
    exact .sub t (.TABLE address) (.TABLE value.TYPE) (.TABLE t.TABLES[address]!.TYPE)
      (.table t address _ (bound.trans_le tables.1) rfl fresh newType)
      (.table _ _ sub newType wt) fresh wt newType
  | sub address ty actual prior sub _ wt wa ih =>
    exact .sub t address ty actual ih sub fresh wt wa

theorem ref_ok_extend {s t : store} (extension : Extend_store s t)
    {value : ref} {ty : reftype} (typed : Ref_ok s value ty) : Ref_ok t value ty := by
  have fresh := (extend_store_wf extension).2
  cases typed with
  | null ty _ => exact .null t ty fresh
  | func address ty addressTyped _ wf =>
    exact .func t address ty (externaddr_ok_extend extension addressTyped) fresh wf
  | extern address _ => exact .extern t address fresh

/-- Dropping a segment preserves its semantic instance typing. -/
theorem eleminst_ok_extend {s t : store} (extension : Extend_store s t)
    {a b : eleminst} {ty : elemtype} (objects : Extend_eleminst a b)
    (typed : Eleminst_ok s a ty) : Eleminst_ok t b ty := by
  cases objects with
  | mk_Extend_eleminst rt refs refs' contents =>
    cases typed with
    | mk_Eleminst_ok _ _ values bound _ =>
      rcases contents with rfl | rfl
      · exact .mk_Eleminst_ok t _ refs (fun value member => ref_ok_extend extension (values value member))
          bound (extend_store_wf extension).2
      · exact .mk_Eleminst_ok t _ [] (by simp [Forall]) (by norm_num) (extend_store_wf extension).2

theorem datainst_ok_extend {s t : store} (extension : Extend_store s t)
    {a b : datainst} {ty : datatype} (objects : Extend_datainst a b)
    (typed : Datainst_ok s a ty) : Datainst_ok t b ty := by
  cases objects with
  | mk_Extend_datainst bytes bytes' contents old fresh =>
    cases typed with
    | mk_Datainst_ok _ bound _ _ =>
      rcases contents with rfl | rfl
      · exact .mk_Datainst_ok t bytes bound (extend_store_wf extension).2 fresh
      · exact .mk_Datainst_ok t [] (by norm_num) (extend_store_wf extension).2 fresh
end Itasca.Runtime.Spec
namespace Itasca.Runtime.Spec

theorem function_lookup_extend {s t : store} (extension : Extend_store s t)
    {index : Nat} {fn : funcinst} (found : s.FUNCS[index]? = some fn) :
    t.FUNCS[index]? = some fn := by
  have functions := (extend_store_objects extension).2.2.2.1
  obtain ⟨bound, equal⟩ := List.getElem?_eq_some_iff.mp found
  have retained := extend_func_eq (functions.2 index bound)
  have room := bound.trans_le functions.1
  rw [getElem!_pos s.FUNCS index bound, getElem!_pos t.FUNCS index room] at retained
  exact List.getElem?_eq_some_iff.mpr ⟨room, retained.trans equal⟩

theorem element_lookup_extend {s t : store} (extension : Extend_store s t)
    {index : Nat} {entry : eleminst} {ty : elemtype}
    (found : s.ELEMS[index]? = some entry) (typed : Eleminst_ok s entry ty) :
    ∃ fresh, t.ELEMS[index]? = some fresh ∧ Eleminst_ok t fresh ty := by
  have elements := (extend_store_objects extension).2.2.2.2.2
  obtain ⟨bound, equal⟩ := List.getElem?_eq_some_iff.mp found
  have retained := elements.2 index bound
  have room := bound.trans_le elements.1
  rw [getElem!_pos s.ELEMS index bound, equal] at retained
  refine ⟨t.ELEMS[index]!, ?_, eleminst_ok_extend extension retained typed⟩
  simp [getElem!_pos t.ELEMS index room]

theorem data_lookup_extend {s t : store} (extension : Extend_store s t)
    {index : Nat} {entry : datainst} {ty : datatype}
    (found : s.DATAS[index]? = some entry) (typed : Datainst_ok s entry ty) :
    ∃ fresh, t.DATAS[index]? = some fresh ∧ Datainst_ok t fresh ty := by
  have segments := (extend_store_objects extension).2.2.2.2.1
  obtain ⟨bound, equal⟩ := List.getElem?_eq_some_iff.mp found
  have retained := segments.2 index bound
  have room := bound.trans_le segments.1
  rw [getElem!_pos s.DATAS index bound, equal] at retained
  refine ⟨t.DATAS[index]!, ?_, datainst_ok_extend extension retained typed⟩
  simp [getElem!_pos t.DATAS index room]
end Itasca.Runtime.Spec

end

/-! ## Float -/

section

/-! The concrete arithmetic result lists satisfy the generated numeric rules.
Membership in these lists is the nondeterministic choice consumed by Step. -/
namespace Itasca.Runtime.Spec
open SpecExt SpecExt.Builtins.Float

theorem float_num_wf (ty : Fnn) (value : fN)
    (h : wf_fN (sizenn (numtype_Fnn ty)) value) :
    wf_num_ (numtype_Fnn ty) (.mk_num__1 ty value) :=
  .num__case_1 _ _ _ h rfl

theorem float_results_wf (ty : Fnn) (values : List fN)
    (h : Forall (wf_fN (sizenn (numtype_Fnn ty))) values) :
    Forall (fun value => wf_num_ (numtype_Fnn ty) (.mk_num__1 ty value)) values := by
  intro value hv
  exact float_num_wf ty value (h value hv)

theorem float_f32_add_relation (a b : fN)
    (ha : wf_fN 32 a) (hb : wf_fN 32 b) :
    fun_binop_ .F32 (.mk_binop__1 .F32 .ADD) (.mk_num__1 .F32 a) (.mk_num__1 .F32 b)
      (some ((fadd_ 32 a b).map (num_.mk_num__1 .F32))) := by
  apply fun_binop_.fun_binop__case_24
  · exact add_wf 32 (by omega) a b ha hb
  · exact float_results_wf .F32 _ (add_wf 32 (by omega) a b ha hb)

theorem float_f32_sub_relation (a b : fN)
    (ha : wf_fN 32 a) (hb : wf_fN 32 b) :
    fun_binop_ .F32 (.mk_binop__1 .F32 .SUB) (.mk_num__1 .F32 a) (.mk_num__1 .F32 b)
      (some ((fsub_ 32 a b).map (num_.mk_num__1 .F32))) := by
  apply fun_binop_.fun_binop__case_26
  · exact sub_wf 32 (by omega) a b ha hb
  · exact float_results_wf .F32 _ (sub_wf 32 (by omega) a b ha hb)

theorem float_f32_mul_relation (a b : fN)
    (ha : wf_fN 32 a) (hb : wf_fN 32 b) :
    fun_binop_ .F32 (.mk_binop__1 .F32 .MUL) (.mk_num__1 .F32 a) (.mk_num__1 .F32 b)
      (some ((fmul_ 32 a b).map (num_.mk_num__1 .F32))) := by
  apply fun_binop_.fun_binop__case_28
  · exact mul_wf 32 (by omega) a b
  · exact float_results_wf .F32 _ (mul_wf 32 (by omega) a b)

theorem float_f32_div_relation (a b : fN)
    (ha : wf_fN 32 a) (hb : wf_fN 32 b) :
    fun_binop_ .F32 (.mk_binop__1 .F32 .DIV) (.mk_num__1 .F32 a) (.mk_num__1 .F32 b)
      (some ((fdiv_ 32 a b).map (num_.mk_num__1 .F32))) := by
  apply fun_binop_.fun_binop__case_30
  · exact div_wf 32 (by omega) a b
  · exact float_results_wf .F32 _ (div_wf 32 (by omega) a b)

theorem float_f32_sqrt_relation (a : fN) (ha : wf_fN 32 a) :
    fun_unop_ .F32 (.mk_unop__1 .F32 .SQRT) (.mk_num__1 .F32 a)
      (some ((fsqrt_ 32 a).map (num_.mk_num__1 .F32))) := by
  apply fun_unop_.fun_unop__case_12
  exact float_results_wf .F32 _ (sqrt_wf 32 (by omega) a ha)

theorem float_f32_ceil_relation (a : fN) (ha : wf_fN 32 a) :
    fun_unop_ .F32 (.mk_unop__1 .F32 .CEIL) (.mk_num__1 .F32 a)
      (some ((fceil_ 32 a).map (num_.mk_num__1 .F32))) := by
  apply fun_unop_.fun_unop__case_14
  exact float_results_wf .F32 _ (integral_wf 32 (by omega) _ a ha)

theorem float_f32_floor_relation (a : fN) (ha : wf_fN 32 a) :
    fun_unop_ .F32 (.mk_unop__1 .F32 .FLOOR) (.mk_num__1 .F32 a)
      (some ((ffloor_ 32 a).map (num_.mk_num__1 .F32))) := by
  apply fun_unop_.fun_unop__case_16
  exact float_results_wf .F32 _ (integral_wf 32 (by omega) _ a ha)

theorem float_f32_trunc_relation (a : fN) (ha : wf_fN 32 a) :
    fun_unop_ .F32 (.mk_unop__1 .F32 .TRUNC) (.mk_num__1 .F32 a)
      (some ((ftrunc_ 32 a).map (num_.mk_num__1 .F32))) := by
  apply fun_unop_.fun_unop__case_18
  exact float_results_wf .F32 _ (integral_wf 32 (by omega) _ a ha)

theorem float_f32_nearest_relation (a : fN) (ha : wf_fN 32 a) :
    fun_unop_ .F32 (.mk_unop__1 .F32 .NEAREST) (.mk_num__1 .F32 a)
      (some ((fnearest_ 32 a).map (num_.mk_num__1 .F32))) := by
  apply fun_unop_.fun_unop__case_20
  exact float_results_wf .F32 _ (integral_wf 32 (by omega) _ a ha)

theorem float_f64_add_relation (a b : fN)
    (ha : wf_fN 64 a) (hb : wf_fN 64 b) :
    fun_binop_ .F64 (.mk_binop__1 .F64 .ADD) (.mk_num__1 .F64 a) (.mk_num__1 .F64 b)
      (some ((fadd_ 64 a b).map (num_.mk_num__1 .F64))) := by
  apply fun_binop_.fun_binop__case_25
  · exact add_wf 64 (by omega) a b ha hb
  · exact float_results_wf .F64 _ (add_wf 64 (by omega) a b ha hb)

theorem float_f64_sub_relation (a b : fN)
    (ha : wf_fN 64 a) (hb : wf_fN 64 b) :
    fun_binop_ .F64 (.mk_binop__1 .F64 .SUB) (.mk_num__1 .F64 a) (.mk_num__1 .F64 b)
      (some ((fsub_ 64 a b).map (num_.mk_num__1 .F64))) := by
  apply fun_binop_.fun_binop__case_27
  · exact sub_wf 64 (by omega) a b ha hb
  · exact float_results_wf .F64 _ (sub_wf 64 (by omega) a b ha hb)

theorem float_f64_mul_relation (a b : fN)
    (ha : wf_fN 64 a) (hb : wf_fN 64 b) :
    fun_binop_ .F64 (.mk_binop__1 .F64 .MUL) (.mk_num__1 .F64 a) (.mk_num__1 .F64 b)
      (some ((fmul_ 64 a b).map (num_.mk_num__1 .F64))) := by
  apply fun_binop_.fun_binop__case_29
  · exact mul_wf 64 (by omega) a b
  · exact float_results_wf .F64 _ (mul_wf 64 (by omega) a b)

theorem float_f64_div_relation (a b : fN)
    (ha : wf_fN 64 a) (hb : wf_fN 64 b) :
    fun_binop_ .F64 (.mk_binop__1 .F64 .DIV) (.mk_num__1 .F64 a) (.mk_num__1 .F64 b)
      (some ((fdiv_ 64 a b).map (num_.mk_num__1 .F64))) := by
  apply fun_binop_.fun_binop__case_31
  · exact div_wf 64 (by omega) a b
  · exact float_results_wf .F64 _ (div_wf 64 (by omega) a b)

theorem float_f64_sqrt_relation (a : fN) (ha : wf_fN 64 a) :
    fun_unop_ .F64 (.mk_unop__1 .F64 .SQRT) (.mk_num__1 .F64 a)
      (some ((fsqrt_ 64 a).map (num_.mk_num__1 .F64))) := by
  apply fun_unop_.fun_unop__case_13
  exact float_results_wf .F64 _ (sqrt_wf 64 (by omega) a ha)

theorem float_f64_ceil_relation (a : fN) (ha : wf_fN 64 a) :
    fun_unop_ .F64 (.mk_unop__1 .F64 .CEIL) (.mk_num__1 .F64 a)
      (some ((fceil_ 64 a).map (num_.mk_num__1 .F64))) := by
  apply fun_unop_.fun_unop__case_15
  exact float_results_wf .F64 _ (integral_wf 64 (by omega) _ a ha)

theorem float_f64_floor_relation (a : fN) (ha : wf_fN 64 a) :
    fun_unop_ .F64 (.mk_unop__1 .F64 .FLOOR) (.mk_num__1 .F64 a)
      (some ((ffloor_ 64 a).map (num_.mk_num__1 .F64))) := by
  apply fun_unop_.fun_unop__case_17
  exact float_results_wf .F64 _ (integral_wf 64 (by omega) _ a ha)

theorem float_f64_trunc_relation (a : fN) (ha : wf_fN 64 a) :
    fun_unop_ .F64 (.mk_unop__1 .F64 .TRUNC) (.mk_num__1 .F64 a)
      (some ((ftrunc_ 64 a).map (num_.mk_num__1 .F64))) := by
  apply fun_unop_.fun_unop__case_19
  exact float_results_wf .F64 _ (integral_wf 64 (by omega) _ a ha)

theorem float_f64_nearest_relation (a : fN) (ha : wf_fN 64 a) :
    fun_unop_ .F64 (.mk_unop__1 .F64 .NEAREST) (.mk_num__1 .F64 a)
      (some ((fnearest_ 64 a).map (num_.mk_num__1 .F64))) := by
  apply fun_unop_.fun_unop__case_21
  exact float_results_wf .F64 _ (integral_wf 64 (by omega) _ a ha)

end Itasca.Runtime.Spec

end

/-! ## Context -/

section

/-!
Source evaluation-context algebra and transport of reduction. Source-machine simulations use these lemmas to rebuild nested labels and frames.
-/

namespace Itasca.Runtime.Spec
open SpecExt

/-- A label evaluation context, preserving the inner state. -/
def labelContext (arity : Nat) (cont : List instr) : config → config
  | .mk_config z body => .mk_config z [.LABEL_ arity cont body]

/-- A frame evaluation context; the enclosing frame is not changed. -/
def frameContext (arity : Nat) (outer : frame) : config → config
  | .mk_config (.mk_state s inner) body =>
      .mk_config (.mk_state s outer) [.FRAME_ arity inner body]

/-- Values to the left and pending instructions to the right of the redex. -/
def instrContext (vs : List val) (after : List admininstr) : config → config
  | .mk_config z body => .mk_config z (vals vs ++ (body ++ after))

/-- Lift an execution through any context preserving steps and well-formedness. -/
theorem steps_h_map {wrap : config → config}
    (hw : ∀ c, wf_config c → wf_config (wrap c))
    (hs : ∀ c es c', StepH c es c' → StepH (wrap c) es (wrap c'))
    {c c' : config} {es : List HostEvent} (h : StepsH c es c') :
    StepsH (wrap c) es (wrap c') := by
  induction h with
  | refl h => exact .refl (hw _ h)
  | cons h _ ih => exact .cons (hs _ _ _ h) ih

theorem step_h_label {c c' : config} {es : List HostEvent}
    (h : StepH c es c') (arity : Nat) (cont : List instr) (hc : Forall wf_instr cont) :
    StepH (labelContext arity cont c) es (labelContext arity cont c') := by
  cases c with | mk_config z body =>
    cases c' with | mk_config z' body' =>
      obtain ⟨hw, hw'⟩ := step_h_wf h
      exact .ctxt_label h (wf_config_label arity hw hc) (wf_config_label arity hw' hc) hw hw'

theorem step_h_frame {c c' : config} {es : List HostEvent}
    (h : StepH c es c') (arity : Nat) (outer : frame) (hf : wf_frame outer) :
    StepH (frameContext arity outer c) es (frameContext arity outer c') := by
  cases c with | mk_config z body =>
    cases z
    cases c' with | mk_config z' body' =>
      cases z'
      obtain ⟨hw, hw'⟩ := step_h_wf h
      exact .ctxt_frame h (wf_config_frame arity hw hf) (wf_config_frame arity hw' hf) hw hw'

theorem step_h_instrs {c c' : config} {es : List HostEvent}
    (h : StepH c es c') (vs : List val) (after : List admininstr)
    (hv : Forall wf_val vs) (ha : Forall wf_admininstr after) :
    StepH (instrContext vs after c) es (instrContext vs after c') := by
  cases c with | mk_config z body =>
    cases c' with | mk_config z' body' =>
      by_cases hn : vs ≠ [] ∨ after ≠ []
      · obtain ⟨hw, hw'⟩ := step_h_wf h
        exact .ctxt_instrs h hn (wf_config_instrs hw hv ha) (wf_config_instrs hw' hv ha) hw hw'
      · have hv0 : vs = [] := Decidable.byContradiction (fun hne => hn (Or.inl hne))
        have ha0 : after = [] := Decidable.byContradiction (fun hne => hn (Or.inr hne))
        subst vs
        subst after
        simpa [instrContext, vals] using h

theorem steps_h_instrs {c c' : config} {es : List HostEvent}
    (h : StepsH c es c') (vs : List val) (after : List admininstr)
    (hv : Forall wf_val vs) (ha : Forall wf_admininstr after) :
    StepsH (instrContext vs after c) es (instrContext vs after c') := by
  apply steps_h_map (wrap := instrContext vs after) ?_ (fun _ _ _ h => step_h_instrs h vs after hv ha) h
  intro c hw
  cases c
  exact wf_config_instrs hw hv ha

end Itasca.Runtime.Spec

end

/-! ## Integer -/

section

/-! Generated integer comparison relations. The input integers are interpreted
at their declared width by the caller; comparisons always return an i32 Boolean. -/

namespace Itasca.Runtime.Spec

theorem boolean_u32_wf (answer : Bool) :
    wf_uN 32 (.mk_uN (nat_of_bool answer)) := by
  cases answer <;> apply wf_uN.uN_case_0 <;> decide

theorem predicate_u32_wf (answer : Prop) [Decidable answer] :
    wf_uN 32 (.mk_uN (if answer then 1 else 0)) := by
  by_cases h : answer <;> simp only [h, if_true, if_false]
  all_goals apply wf_uN.uN_case_0; decide

theorem predicate_i32_wf (answer : Prop) [Decidable answer] :
    wf_num_ .I32 (.mk_num__0 .I32 (.mk_uN (if answer then 1 else 0))) := by
  exact .num__case_0 _ _ _ (by decide) (predicate_u32_wf answer) rfl

/-- EQ returns exactly the Boolean specified by the generated rule. -/
theorem integer_eq_relation (ty : Inn) (a b : Nat) :
    fun_relop_ (numtype_Inn ty) (.mk_relop__0 ty .EQ)
      (.mk_num__0 ty (.mk_uN a)) (.mk_num__0 ty (.mk_uN b))
      (some (.mk_num__0 .I32 (.mk_uN (if a = b then 1 else 0)))) := by
  have hn := predicate_i32_wf (a = b)
  have hbool : nat_of_bool (uN.mk_uN a == uN.mk_uN b) = (if a = b then 1 else 0) := by
    change nat_of_bool (a == b) = _
    by_cases h : a = b
    · subst b; simp [nat_of_bool]
    · have hb : (a == b) = false := beq_eq_false_iff_ne.mpr h
      simp [hb, h, nat_of_bool]
  have hi : fun_ieq_ (sizenn (numtype_Inn ty)) (.mk_uN a) (.mk_uN b)
      (.mk_uN (if a = b then 1 else 0)) := by
    rw [← hbool]
    exact (fun_ieq_.fun_ieq__case_0 (sizenn (numtype_Inn ty)) (.mk_uN a) (.mk_uN b) (boolean_u32_wf _))
  cases ty with
  | I32 => exact .fun_relop__case_0 _ _ _ hi hn
  | I64 => exact .fun_relop__case_1 _ _ _ hi hn

/-- NE returns exactly the Boolean specified by the generated rule. -/
theorem integer_ne_relation (ty : Inn) (a b : Nat) :
    fun_relop_ (numtype_Inn ty) (.mk_relop__0 ty .NE)
      (.mk_num__0 ty (.mk_uN a)) (.mk_num__0 ty (.mk_uN b))
      (some (.mk_num__0 .I32 (.mk_uN (if a ≠ b then 1 else 0)))) := by
  have hn := predicate_i32_wf (a ≠ b)
  have hbool : nat_of_bool (uN.mk_uN a != uN.mk_uN b) = (if a ≠ b then 1 else 0) := by
    change nat_of_bool (a != b) = _
    by_cases h : a = b
    · subst b; simp [bne, nat_of_bool]
    · have hb : (a == b) = false := beq_eq_false_iff_ne.mpr h
      simp [bne, hb, h, nat_of_bool]
  have hi : fun_ine_ (sizenn (numtype_Inn ty)) (.mk_uN a) (.mk_uN b)
      (.mk_uN (if a ≠ b then 1 else 0)) := by
    rw [← hbool]
    exact (fun_ine_.fun_ine__case_0 (sizenn (numtype_Inn ty)) (.mk_uN a) (.mk_uN b) (boolean_u32_wf _))
  cases ty with
  | I32 => exact .fun_relop__case_2 _ _ _ hi hn
  | I64 => exact .fun_relop__case_3 _ _ _ hi hn

/-- LTU returns exactly the Boolean specified by the generated rule. -/
theorem integer_ltu_relation (ty : Inn) (a b : Nat) :
    fun_relop_ (numtype_Inn ty) (.mk_relop__0 ty (.LT .U))
      (.mk_num__0 ty (.mk_uN a)) (.mk_num__0 ty (.mk_uN b))
      (some (.mk_num__0 .I32 (.mk_uN (if a < b then 1 else 0)))) := by
  have hn := predicate_i32_wf (a < b)
  have hbool : nat_of_bool (decide (a < b)) = (if a < b then 1 else 0) := by
    change nat_of_bool (decide (a < b)) = _
    by_cases h : a < b <;> simp [h, nat_of_bool]
  have hi : fun_ilt_ (sizenn (numtype_Inn ty)) .U (.mk_uN a) (.mk_uN b)
      (.mk_uN (if a < b then 1 else 0)) := by
    rw [← hbool]
    exact (fun_ilt_.fun_ilt__case_0 (sizenn (numtype_Inn ty)) (.mk_uN a) (.mk_uN b) (boolean_u32_wf _))
  cases ty with
  | I32 => exact .fun_relop__case_4 .U _ _ _ hi hn
  | I64 => exact .fun_relop__case_5 .U _ _ _ hi hn

/-- GTU returns exactly the Boolean specified by the generated rule. -/
theorem integer_gtu_relation (ty : Inn) (a b : Nat) :
    fun_relop_ (numtype_Inn ty) (.mk_relop__0 ty (.GT .U))
      (.mk_num__0 ty (.mk_uN a)) (.mk_num__0 ty (.mk_uN b))
      (some (.mk_num__0 .I32 (.mk_uN (if a > b then 1 else 0)))) := by
  have hn := predicate_i32_wf (a > b)
  have hbool : nat_of_bool (decide (a > b)) = (if a > b then 1 else 0) := by
    change nat_of_bool (decide (a > b)) = _
    by_cases h : a > b <;> simp [h, nat_of_bool]
  have hi : fun_igt_ (sizenn (numtype_Inn ty)) .U (.mk_uN a) (.mk_uN b)
      (.mk_uN (if a > b then 1 else 0)) := by
    rw [← hbool]
    exact (fun_igt_.fun_igt__case_0 (sizenn (numtype_Inn ty)) (.mk_uN a) (.mk_uN b) (boolean_u32_wf _))
  cases ty with
  | I32 => exact .fun_relop__case_6 .U _ _ _ hi hn
  | I64 => exact .fun_relop__case_7 .U _ _ _ hi hn

/-- LEU returns exactly the Boolean specified by the generated rule. -/
theorem integer_leu_relation (ty : Inn) (a b : Nat) :
    fun_relop_ (numtype_Inn ty) (.mk_relop__0 ty (.LE .U))
      (.mk_num__0 ty (.mk_uN a)) (.mk_num__0 ty (.mk_uN b))
      (some (.mk_num__0 .I32 (.mk_uN (if a ≤ b then 1 else 0)))) := by
  have hn := predicate_i32_wf (a ≤ b)
  have hbool : nat_of_bool (decide (a ≤ b)) = (if a ≤ b then 1 else 0) := by
    change nat_of_bool (decide (a ≤ b)) = _
    by_cases h : a ≤ b <;> simp [h, nat_of_bool]
  have hi : fun_ile_ (sizenn (numtype_Inn ty)) .U (.mk_uN a) (.mk_uN b)
      (.mk_uN (if a ≤ b then 1 else 0)) := by
    rw [← hbool]
    exact (fun_ile_.fun_ile__case_0 (sizenn (numtype_Inn ty)) (.mk_uN a) (.mk_uN b) (boolean_u32_wf _))
  cases ty with
  | I32 => exact .fun_relop__case_8 .U _ _ _ hi hn
  | I64 => exact .fun_relop__case_9 .U _ _ _ hi hn

/-- GEU returns exactly the Boolean specified by the generated rule. -/
theorem integer_geu_relation (ty : Inn) (a b : Nat) :
    fun_relop_ (numtype_Inn ty) (.mk_relop__0 ty (.GE .U))
      (.mk_num__0 ty (.mk_uN a)) (.mk_num__0 ty (.mk_uN b))
      (some (.mk_num__0 .I32 (.mk_uN (if a ≥ b then 1 else 0)))) := by
  have hn := predicate_i32_wf (a ≥ b)
  have hbool : nat_of_bool (decide (a ≥ b)) = (if a ≥ b then 1 else 0) := by
    change nat_of_bool (decide (a ≥ b)) = _
    by_cases h : a ≥ b <;> simp [h, nat_of_bool]
  have hi : fun_ige_ (sizenn (numtype_Inn ty)) .U (.mk_uN a) (.mk_uN b)
      (.mk_uN (if a ≥ b then 1 else 0)) := by
    rw [← hbool]
    exact (fun_ige_.fun_ige__case_0 (sizenn (numtype_Inn ty)) (.mk_uN a) (.mk_uN b) (boolean_u32_wf _))
  cases ty with
  | I32 => exact .fun_relop__case_10 .U _ _ _ hi hn
  | I64 => exact .fun_relop__case_11 .U _ _ _ hi hn

end Itasca.Runtime.Spec

end
