import Itasca.Wasm2.Bulk.Dispatch
import Itasca.Wasm2.NumericExt.Visitor

/-!
# Visitor transfer for bulk instructions

`bulk_transfer` shows that if `code.step_bulk` accepts with one visitor, it accepts with any
replacement visitor whose callbacks accept, reaching the same reader state.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.Visitor

/-- Accepted replacement hooks preserve every successful bulk reader state. -/
theorem bulk_transfer {V W : Type} (visitor : code.OpVisitor V)
    (replacement : code.OpVisitor W) (ha : FullVisitor.Accepts replacement)
    (st final : code.OpIterState) (data : Slice U8) (env : module.Env) (opcode : U32)
    (v v' : V) (w : W)
    (h : code.step_bulk visitor st data env opcode v = .ok (.Ok (), final, v')) :
    ∃ w', code.step_bulk replacement st data env opcode w = .ok (.Ok (), final, w') := by
  rw [code.step_bulk.eq_runs] at h ⊢
  unfold bulkStep at h ⊢
  split at h
  case h_1 =>
    exact CoreVisitor.run.accepted_lift _ _ _ v w final v' h (fun a => ha.on_memory_init w final a)
  case h_2 =>
    exact CoreVisitor.run.accepted_lift _ _ _ v w final v' h (fun a => ha.on_data_drop w final a)
  case h_3 =>
    exact CoreVisitor.run.accepted_lift _ _ _ v w final v' h (fun a => ha.on_memory_copy w final)
  case h_4 =>
    exact CoreVisitor.run.accepted_lift _ _ _ v w final v' h (fun a => ha.on_memory_fill w final)
  case h_5 =>
    exact CoreVisitor.run.accepted_lift _ _ _ v w final v' h (fun a => ha.on_table_init w final a.1 a.2)
  case h_6 =>
    exact CoreVisitor.run.accepted_lift _ _ _ v w final v' h (fun a => ha.on_elem_drop w final a.1)
  case h_7 =>
    exact CoreVisitor.run.accepted_lift _ _ _ v w final v' h (fun a => ha.on_table_copy w final a.1 a.2)
  case h_8 =>
    exact CoreVisitor.run.accepted_lift _ _ _ v w final v' h (fun a => ha.on_table_grow w final a)
  case h_9 =>
    exact CoreVisitor.run.accepted_lift _ _ _ v w final v' h (fun a => ha.on_table_size w final a)
  case h_10 =>
    exact CoreVisitor.run.accepted_lift _ _ _ v w final v' h (fun a => ha.on_table_fill w final a)
  case h_11 => simp at h

end Itasca.Wasm2.Visitor
