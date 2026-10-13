import Itasca.Generated.Funs

open Aeneas Aeneas.Std

namespace Itasca

/-- The signatures used by the body proof are a projection of the single
runtime control stack. No separate signature vector is stored by Rust. -/
def code.BodyState.blocks (st : code.BodyState) : alloc.vec.Vec signature.BlockType :=
  alloc.vec.Vec.from (st.core.ctrls.val.map code.Ctrl.signature) (by simp)

@[simp] theorem code.BodyState.blocks_val (st : code.BodyState) :
    st.blocks.val = st.core.ctrls.val.map code.Ctrl.signature := by
  simp [code.BodyState.blocks]

@[simp] theorem code.BodyState.blocks_length (st : code.BodyState) :
    st.blocks.val.length = st.core.ctrls.val.length := by simp

@[simp] theorem code.BodyState.blocks_len (st : code.BodyState) :
    alloc.vec.Vec.len st.blocks = alloc.vec.Vec.len st.core.ctrls :=
  UScalar.eq_of_val_eq (by simp)

@[simp] theorem code.BodyState.blocks_is_empty (st : code.BodyState) :
    alloc.vec.Vec.is_empty Global st.blocks = alloc.vec.Vec.is_empty Global st.core.ctrls := by
  simp [alloc.vec.Vec.is_empty]

theorem code.BodyState.blocks_index (st : code.BodyState) (i : Usize) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice signature.BlockType) st.blocks i =
      (do let c ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice code.Ctrl) st.core.ctrls i
          .ok c.signature) := by
  simp only [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize,
    alloc.vec.Vec.getElem?_Nat_eq, code.BodyState.blocks_val, List.getElem?_map]
  cases st.core.ctrls.val[i.val]? <;> simp

theorem code.BodyState.blocks_eq_of_ctrls {st st' : code.BodyState}
    (h : st.core.ctrls = st'.core.ctrls) : st.blocks = st'.blocks := by
  apply alloc.vec.Vec.ext
  simp [h]

@[simp] theorem code.BodyState.blocks_eq_iff (st st' : code.BodyState) :
    st.blocks = st'.blocks ↔
      st.core.ctrls.val.map code.Ctrl.signature = st'.core.ctrls.val.map code.Ctrl.signature := by
  rw [alloc.vec.Vec.eq_iff]
  simp

@[simp] theorem code.BodyState.blocks_pos (st : code.BodyState) (pos : Usize) :
    (code.BodyState.mk { st.core with pos }).blocks = st.blocks := rfl

@[simp] theorem code.BodyState.blocks_vals (st : code.BodyState)
    (vals : alloc.vec.Vec code.StackType) :
    (code.BodyState.mk { st.core with vals }).blocks = st.blocks := rfl

end Itasca
