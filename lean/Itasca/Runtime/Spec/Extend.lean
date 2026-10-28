import «wasm2.0»
import Mathlib.Tactic

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

private theorem option_uN_injective {a b : Option Nat}
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
  have hmEq := option_uN_injective hmx
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
  have hmEq := option_uN_injective hmx
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
