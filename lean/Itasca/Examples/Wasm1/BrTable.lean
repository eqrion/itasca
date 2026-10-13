import Itasca.Wasm1.Soundness
import Itasca.Examples.Wasm1.Support

open Aeneas Aeneas.Std

namespace Itasca.Examples.Wasm1BrTable

open Wasm1Support


def emptyContext : code.Context := ⟨alloc.vec.Vec.new _, alloc.vec.Vec.new _⟩

def brTableBytes : Slice U8 := alloc.vec.Vec.deref
  (alloc.vec.Vec.from [0#u8, 0x0E#u8, 1#u8, 0#u8, 0#u8, 0x0B#u8] (by scalar_tac))

private theorem leb_at (pos next : Usize) (value : U32)
    (hp : pos.val < brTableBytes.length)
    (hn : next.val = pos.val + 1)
    (hb : (brTableBytes.val[pos.val]).val = value.val)
    (hv : value.val < 128) :
    reader.read_u32_leb brTableBytes pos = .ok (.Ok (value, next)) := by
  obtain ⟨v, p, hr, hv', hp'⟩ := reader.read_u32_leb.single_byte brTableBytes pos hp
    (by simpa [hb] using hv)
  have heq : v = value := UScalar.eq_of_val_eq (hv'.trans hb)
  have hpeq : p = next := UScalar.eq_of_val_eq (hp'.trans hn.symm)
  simpa [heq, hpeq] using hr

private theorem labels_one (st next : code.OpIterState) (target : code.Ctrl)
    (hlabel : code.read_label st brTableBytes = .ok (.Ok (0#u32, target), next))
    (htarget : code.branch_target_bt target = .ok .Empty) :
    code.read_table_labels code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor st brTableBytes 1#u32 () =
      .ok (.Ok (some .Empty), next, ()) := by
  have hmerge : code.merge_target none .Empty = .ok (.Ok .Empty) := rfl
  obtain ⟨i, hi, hiv⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x := 0#u32) (y := 1#u32) (by scalar_tac))
  have hieq : i = 1#u32 := by scalar_tac
  subst i
  have hdone : code.read_table_labels_loop code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      next brTableBytes 1#u32 () (some .Empty) 1#u32 =
      .ok (.Ok (some .Empty), next, ()) := by
    unfold code.read_table_labels_loop
    rw [loop]
    simp [code.read_table_labels_loop.body]
  unfold code.read_table_labels code.read_table_labels_loop
  rw [loop]
  simp only [code.read_table_labels_loop.body, show (0#u32 = 1#u32) = False from by decide,
    ↓reduceIte, hlabel, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  simpa [code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor, code.OpVisitor.on_br_table_label.default,
    code.visit, htarget, hmerge, hi, core.result.Result.Insts.CoreOpsTry.branch,
    code.read_table_labels_loop, code.read_table_labels_loop.body] using hdone

/-- The public validator executes a nonempty branch-table label loop on a polymorphic stack. -/
theorem br_table_body_accepted (env : module.Env) :
    code.validate_body brTableBytes env emptyContext = .ok (.Ok ()) := by
  let initial := Wasm1.Loop.initial .Empty
  let first := { initial with pos := 1#usize }
  let frame : code.Ctrl := ⟨.Body, .Empty, Control.signature (.Empty), 0#usize, false⟩
  let poly : code.Ctrl := { frame with polymorphic_base := true }
  obtain ⟨marked, hmark, hmv, hml, hmc, hmp⟩ := WP.spec_imp_exists
    (code.mark_unreachable.spec first [] frame rfl (by simp [frame]))
  have hstep0 : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor first brTableBytes env
      emptyContext code.OP_UNREACHABLE () = .ok (.Ok (), marked, ()) := by
    simp [global_simps, code.read_unreachable, hmark,
      code.OpVisitor.on_unreachable.default, code.visit, core.result.Result.Insts.CoreOpsTry.branch]
  let table := { marked with pos := 2#usize }
  let entry := { marked with pos := 3#usize }
  let default := { marked with pos := 4#usize }
  let afterDefault := { marked with pos := 5#usize }
  have hcount : reader.read_u32_leb brTableBytes table.pos = .ok (.Ok (1#u32, 3#usize)) :=
    leb_at 2#usize 3#usize 1#u32 (by decide) rfl rfl (by decide)
  have hentryRead : reader.read_u32_leb brTableBytes entry.pos = .ok (.Ok (0#u32, 4#usize)) :=
    leb_at 3#usize 4#usize 0#u32 (by decide) rfl rfl (by decide)
  obtain ⟨_, hentry, rfl⟩ := WP.spec_imp_exists
    (code.read_label.from_leb entry brTableBytes 0#u32 4#usize hentryRead
      (by simp [entry, hmc]))
  have hentry' : code.read_label entry brTableBytes = .ok (.Ok (0#u32, poly), default) := by
    simpa [entry, default, hmc, poly] using hentry
  have hlabels := labels_one entry default poly hentry' rfl
  have hdefaultRead : reader.read_u32_leb brTableBytes default.pos = .ok (.Ok (0#u32, 5#usize)) :=
    leb_at 4#usize 5#usize 0#u32 (by decide) rfl rfl (by decide)
  obtain ⟨_, hdefault, rfl⟩ := WP.spec_imp_exists
    (code.read_label.from_leb default brTableBytes 0#u32 5#usize hdefaultRead
      (by simp [default, hmc]))
  have hdefault' : code.read_label default brTableBytes = .ok (.Ok (0#u32, poly), afterDefault) := by
    simpa [default, afterDefault, hmc, poly] using hdefault
  have hpop := code.pop_with_type.polymorphic afterDefault .I32
    (by apply UScalar.eq_of_val_eq; simp [afterDefault, alloc.vec.Vec.len, Control.base, hmc, hml, frame])
    (by simp [afterDefault, Control.polymorphic, hmc])
  have hargs := code.pop_types.empty afterDefault
    (alloc.vec.Vec.deref (alloc.vec.Vec.new types.ValueType)) rfl
  obtain ⟨branched, hbranch, hbv, hbl, hbc, hbp⟩ := WP.spec_imp_exists
    (code.mark_unreachable.spec afterDefault [] poly
      (by simp [afterDefault, poly, hmc]) (by simp [poly, frame]))
  have hreadTable : code.read_br_table code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      table brTableBytes () = .ok (.Ok (0#u32, .Empty), branched, ()) := by
    have hentryEq : { table with pos := 3#usize } = entry := rfl
    simp [code.read_br_table, hcount, hentryEq, hlabels, hdefault',
      show code.branch_target_bt poly = .ok .Empty from rfl,
      code.merge_target, code.BlockType.Insts.CoreCmpPartialEqBlockType.eq,
      hpop, code.block_results, hargs, hbranch, core.result.Result.Insts.CoreOpsTry.branch]
  have hstepTable : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor table brTableBytes env
      emptyContext code.OP_BR_TABLE () = .ok (.Ok (), branched, ()) := by
    simp [hreadTable, code.visit,
      code.OpVisitor.on_br_table.default, core.result.Result.Insts.CoreOpsTry.branch]
  let last := { branched with pos := 6#usize }
  have hlastCtrl : last.ctrls.val = [] ++ [poly] := by
    simpa [last, poly] using hbc
  have hlastVals : last.vals.val = [] ++ (Control.results poly.block_type).map code.StackType.Val := by
    simp [last, hbv, poly, frame, Control.results]
  obtain ⟨⟨_, finished⟩, hend, rfl, hfc, hfv, hfp⟩ := WP.spec_imp_exists
    (code.read_end.concrete last [] poly [] hlastCtrl hlastVals rfl (by simp [poly, frame]))
  dsimp only at hfc hfv hfp
  apply public_of_loop brTableBytes env emptyContext .Empty (.Ok ())
    (by simp [brTableBytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES]) rfl
  rw [loop_step brTableBytes env emptyContext initial first marked code.OP_UNREACHABLE
    (by simp [initial, Wasm1.Loop.initial])
    (read_at brTableBytes initial 1#usize code.OP_UNREACHABLE (by decide) rfl
      (by simp [brTableBytes, initial, Wasm1.Loop.initial, alloc.vec.Vec.deref, code.OP_UNREACHABLE])) hstep0]
  rw [loop_step brTableBytes env emptyContext marked table branched code.OP_BR_TABLE
    (by simp [hmc])
    (read_at brTableBytes marked 2#usize code.OP_BR_TABLE
      (by simp [hmp, first, brTableBytes, alloc.vec.Vec.deref]) (by simp [hmp, first])
      (by simp [hmp, first, brTableBytes, alloc.vec.Vec.deref, code.OP_BR_TABLE])) hstepTable]
  rw [loop_step brTableBytes env emptyContext branched last finished code.OP_END
    (by simp [hbc])
    (read_at brTableBytes branched 6#usize code.OP_END
      (by simp [hbp, afterDefault, brTableBytes, alloc.vec.Vec.deref]) (by simp [hbp, afterDefault])
      (by simp [hbp, afterDefault, brTableBytes, alloc.vec.Vec.deref, code.OP_END]))
    (step_end brTableBytes env emptyContext last finished .Body .Empty hend)]
  exact loop_done brTableBytes env emptyContext finished hfc hfp

theorem br_table_body_validated (env : module.Env) :
    Wasm1.Validated brTableBytes env emptyContext .Empty :=
  code.validate_body.wasm_sound brTableBytes env emptyContext .Empty rfl (br_table_body_accepted env)

end Itasca.Examples.Wasm1BrTable
