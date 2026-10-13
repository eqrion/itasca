import Itasca.Support.EnvTranslation

open Aeneas Aeneas.Std

namespace Itasca.EnvTranslation

private theorem mapped_lookup {α β : Type} [Inhabited β]
    (xs : List α) (f : α → β) (i : Nat) (t : β)
    (hi : i < (xs.map f).length) (ht : (xs.map f)[i]! = t) :
    ∃ x, ∃ hx : i < xs.length, xs[i] = x ∧ f x = t := by
  have hx : i < xs.length := by simpa using hi
  exact ⟨xs[i], hx, rfl, by simpa [getElem!_pos, hx] using ht⟩

/-- A bounded lookup in the translated context recovers the concrete local. -/
theorem Matches.local_lookup {env ctx C} (h : Matches env ctx C)
    (idx : U32) (t : valtype) (hi : idx.val < C.LOCALS.length) (ht : C.LOCALS[idx.val]! = t) :
    ∃ v, ∃ hv : idx.val < ctx.locals.val.length,
      ctx.locals.val[idx.val] = v ∧ Translate.valueType v = t := by
  exact mapped_lookup _ _ _ _ (by simpa [h.locals] using hi) (by simpa [h.locals] using ht)

theorem Matches.global_lookup {env ctx C} (h : Matches env ctx C)
    (idx : U32) (t : globaltype) (hi : idx.val < C.GLOBALS.length) (ht : C.GLOBALS[idx.val]! = t) :
    ∃ gt, ∃ hv : idx.val < env.global_types.val.length,
      env.global_types.val[idx.val] = gt ∧ Translate.globalType gt = t := by
  exact mapped_lookup _ _ _ _ (by simpa [h.globals] using hi) (by simpa [h.globals] using ht)

theorem Matches.func_lookup {env ctx C} (h : Matches env ctx C)
    (idx : U32) (t : functype) (hi : idx.val < C.FUNCS.length) (ht : C.FUNCS[idx.val]! = t) :
    ∃ ft, ∃ hv : idx.val < env.func_types.val.length,
      env.func_types.val[idx.val] = ft ∧ funcType ft = t := by
  exact mapped_lookup _ _ _ _ (by simpa [h.funcs] using hi) (by simpa [h.funcs] using ht)

theorem Matches.type_lookup {env ctx C} (h : Matches env ctx C)
    (idx : U32) (t : functype) (hi : idx.val < C.TYPES.length) (ht : C.TYPES[idx.val]! = t) :
    ∃ ft, ∃ hv : idx.val < env.types.val.length,
      env.types.val[idx.val] = ft ∧ funcType ft = t := by
  exact mapped_lookup _ _ _ _ (by simpa [h.types] using hi) (by simpa [h.types] using ht)

theorem Matches.table_lookup {env ctx C} (h : Matches env ctx C)
    (idx : U32) (t : tabletype) (hi : idx.val < C.TABLES.length) (ht : C.TABLES[idx.val]! = t) :
    ∃ tt, ∃ hv : idx.val < env.table_types.val.length,
      env.table_types.val[idx.val] = tt ∧ tableType tt = t := by
  exact mapped_lookup _ _ _ _ (by simpa [h.tables] using hi) (by simpa [h.tables] using ht)

theorem Matches.table_funcref {env ctx C} (h : Matches env ctx C)
    (idx : U32) (lim : limits) (hi : idx.val < C.TABLES.length)
    (ht : C.TABLES[idx.val]! = .mk_tabletype lim .FUNCREF) :
    ∃ hv : idx.val < env.table_types.val.length, env.table_types.val[idx.val].elem = .FuncRef := by
  obtain ⟨tt, hv, htt, htype⟩ := h.table_lookup idx _ hi ht
  refine ⟨hv, ?_⟩
  rw [htt]
  cases he : tt.elem <;> simp_all [tableType, Translate.referenceType]

theorem Matches.table_exists {env ctx C} (h : Matches env ctx C)
    (hi : 0 < C.TABLES.length) : 0 < env.table_types.val.length := by simpa [h.tables] using hi

theorem Matches.memory_exists {env ctx C} (h : Matches env ctx C)
    (hi : 0 < C.MEMS.length) : 0 < env.mem_types.val.length := by simpa [h.mems] using hi

end Itasca.EnvTranslation
