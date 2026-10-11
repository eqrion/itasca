import Itasca.Generated.Funs

open Aeneas Aeneas.Std

namespace Itasca

/-- The signatures used by the body proof are a projection of the single
runtime control stack. No separate signature vector is stored by Rust. -/
def multi_value.State.blocks (st : multi_value.State) : alloc.vec.Vec signature.BlockType :=
  alloc.vec.Vec.from (st.core.ctrls.val.map code.Ctrl.signature) (by simp)

@[simp] theorem multi_value.State.blocks_val (st : multi_value.State) :
    st.blocks.val = st.core.ctrls.val.map code.Ctrl.signature := by
  simp [multi_value.State.blocks]

@[simp] theorem multi_value.State.blocks_length (st : multi_value.State) :
    st.blocks.val.length = st.core.ctrls.val.length := by simp

@[simp] theorem multi_value.State.blocks_len (st : multi_value.State) :
    alloc.vec.Vec.len st.blocks = alloc.vec.Vec.len st.core.ctrls :=
  UScalar.eq_of_val_eq (by simp)

@[simp] theorem multi_value.State.blocks_is_empty (st : multi_value.State) :
    alloc.vec.Vec.is_empty Global st.blocks = alloc.vec.Vec.is_empty Global st.core.ctrls := by
  simp [alloc.vec.Vec.is_empty]

theorem multi_value.State.blocks_index (st : multi_value.State) (i : Usize) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice signature.BlockType) st.blocks i =
      (do let c ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice code.Ctrl) st.core.ctrls i
          .ok c.signature) := by
  simp only [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize,
    alloc.vec.Vec.getElem?_Nat_eq, multi_value.State.blocks_val, List.getElem?_map]
  cases st.core.ctrls.val[i.val]? <;> simp

theorem multi_value.State.blocks_eq_of_ctrls {st st' : multi_value.State}
    (h : st.core.ctrls = st'.core.ctrls) : st.blocks = st'.blocks := by
  apply alloc.vec.Vec.ext
  simp [h]

@[simp] theorem multi_value.State.blocks_eq_iff (st st' : multi_value.State) :
    st.blocks = st'.blocks ↔
      st.core.ctrls.val.map code.Ctrl.signature = st'.core.ctrls.val.map code.Ctrl.signature := by
  rw [alloc.vec.Vec.eq_iff]
  simp

@[simp] theorem multi_value.State.blocks_pos (st : multi_value.State) (pos : Usize) :
    (multi_value.State.mk { st.core with pos }).blocks = st.blocks := rfl

@[simp] theorem multi_value.State.blocks_vals (st : multi_value.State)
    (vals : alloc.vec.Vec code.StackType) :
    (multi_value.State.mk { st.core with vals }).blocks = st.blocks := rfl

end Itasca
