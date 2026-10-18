import «wasm2.0»

/-! Wasm 1.0 checks active segment bounds before publishing an instance.
These rules use source expressions, source addresses, and source object lengths.
The staged state is distinct from the externally visible pre-instantiation store.
They specify the bounds rejection and rollback boundary, not allocation or start
execution; those are separate premises in a complete instantiation derivation. -/
namespace SpecExt.Wasm1

inductive SegmentBoundsFailure (staged : store) (inst : moduleinst)
    (elements : List elem) (datas : List data) : Prop where
  | element {index target count address : Nat} {offset : expr} {table : tableinst}
      {referenceType : reftype} {initializers : List expr} :
      elements[index]? = some (.ELEM referenceType initializers (.ACTIVE (.mk_uN target) offset)) →
      Eval_expr ⟨staged, ⟨[], inst⟩⟩ offset ⟨staged, ⟨[], inst⟩⟩
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN count))] →
      inst.TABLES[target]? = some address →
      staged.TABLES[address]? = some table →
      table.REFS.length < count + initializers.length →
      SegmentBoundsFailure staged inst elements datas
  | data {index target count address : Nat} {offset : expr} {memory : meminst} {bytes : List byte} :
      datas[index]? = some (.DATA bytes (.ACTIVE (.mk_uN target) offset)) →
      Eval_expr ⟨staged, ⟨[], inst⟩⟩ offset ⟨staged, ⟨[], inst⟩⟩
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN count))] →
      inst.MEMS[target]? = some address →
      staged.MEMS[address]? = some memory →
      memory.BYTES.length < count + bytes.length →
      SegmentBoundsFailure staged inst elements datas

/-- A failed preflight check discards the staged instance and exposes exactly
its original store. This rule performs no segment writes and no start call. -/
inductive BoundsRollback (before staged : store) (inst : moduleinst)
    (elements : List elem) (datas : List data) : store → Prop where
  | reject : SegmentBoundsFailure staged inst elements datas →
      BoundsRollback before staged inst elements datas before

theorem BoundsRollback.unchanged {before staged inst elements datas after}
    (run : BoundsRollback before staged inst elements datas after) : after = before := by
  cases run
  rfl

end SpecExt.Wasm1
