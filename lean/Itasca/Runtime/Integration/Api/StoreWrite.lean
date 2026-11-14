import Itasca.Runtime.Integration.Api.StoreDefine
import Itasca.Runtime.Integration.Execution.Mutation.Operations

/-! Public store writes preserve executable certificates and identify the
requested object that changes. Memory borrows specify their write-back closures. -/

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std Store Interp

/-- Scalar globals have a zero unused high word. -/
private theorem global_high_zero {M : Type} (store : runtime.store.Store M)
    (global : runtime.store.GlobalInst) (shape : GlobalShape store global)
    (scalar : global.ty.valtype ≠ .V128) : global.hi = 0#u64 := by
  cases kind : global.ty.valtype <;> simp only [GlobalShape, kind] at shape
  all_goals first | exact shape | exact shape.2 | exact False.elim (scalar kind)

/-- Setting an issued mutable global writes the requested address and exact
source value. Foreign, immutable, and mistyped writes leave the store unchanged. -/
@[step] theorem _root_.Itasca.runtime.store.Store.set_global.spec {M : Type}
    (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (address : runtime.GlobalAddr) (value : runtime.Value)
    (issued : ExternalIssued store (.Global address)) (valueIssued : IssuedValue store value) :
    runtime.store.Store.set_global memory store address value ⦃ (result, after) =>
      ExecutableInv view code after ∧ CumulativeStoreMutation view code store after ∧
      match result with
      | .Err _ => after = store
      | .Ok () => GlobalMutation store after (sourceValue value) ∧
        ∃ old : runtime.store.GlobalInst, store.globals.val[address.index.val]? = some old ∧
          old.ty.mutability = .Var ∧ old.ty.valtype = rawType value ∧
          (decodeStore view code after).GLOBALS = (decodeStore view code store).GLOBALS.set address.index.val
            ⟨.mk_globaltype (decodeMut old.ty.mutability) (sourceType old.ty.valtype), sourceValue value⟩ ⦄ := by
  classical
  have unchanged := CumulativeStoreMutation.refl_of_shape held.shape held.storeSyntax held.segmentBounds
  unfold runtime.store.Store.set_global
  step with runtime.store.Store.check.spec memory store address.store as ⟨checked, checkEq⟩
  rw [checkEq]
  by_cases sameStore : address.store = store.id
  · simp only [if_pos sameStore, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with check_value_eq memory store value as ⟨checkedValue, valueEq⟩
    rw [valueEq]
    by_cases owner : OwnedBy store.id value
    · simp only [checkOwner, if_pos owner, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      have owned := valueIssued.in_store owner
      have position := issued sameStore
      let old := store.globals.val[address.index.val]
      have found : store.globals.val[address.index.val]? = some old := List.getElem?_eq_getElem position
      have restored : store.globals.set address.index old = store.globals := vec_set_current _ _ position
      have indexed := vec_index_mut_eq store.globals address.index old found
      rw [alloc.vec.Vec.index_mut_slice_index] at indexed
      rw [indexed]
      simp only [bind_ok, bind_tc_ok]
      step with mut_ne old.ty.mutability .Var as ⟨different, differentEq⟩
      cases different with
      | true =>
        simp only [ite_true, restored, WP.spec_ok, uncurry_apply_pair]
        exact ⟨held, unchanged, trivial⟩
      | false =>
        simp only [Bool.false_eq_true, if_false]
        have mutable : old.ty.mutability = .Var := by
          by_contra notMutable
          exact Bool.noConfusion (differentEq.mpr notMutable)
        step with value_type_eq value as ⟨kind, kindEq⟩
        subst kind
        rw [value_type_ne_eq]
        simp only [bind_ok, bind_tc_ok]
        by_cases typed : old.ty.valtype = rawType value
        · simp only [if_pos typed, Bool.false_eq_true, if_false]
          obtain ⟨words, encoded, represented⟩ := WP.spec_imp_exists (encode_value_spec value store.id owned.1)
          have canonical := encode_global_shape store value old.ty typed owned
          rw [encoded] at canonical
          simp only [WP.spec_ok] at canonical
          rw [encoded]
          simp only [bind_ok, bind_tc_ok, WP.spec_ok, uncurry_apply_pair]
          have high : old.ty.valtype ≠ .V128 → words.2 = old.hi := by
            intro scalar
            exact (global_high_zero store {old with lo := words.1, hi := words.2} canonical scalar).trans
              (global_high_zero store old (held.shape.globals old (List.mem_of_getElem? found)) scalar).symm
          have mutation : GlobalMutation store
              {store with globals := store.globals.set address.index {old with lo := words.1, hi := words.2}}
              (sourceValue value) := by
            refine ⟨address.index, old, words.1, words.2, found, mutable, ?_, ?_, high, rfl⟩
            · rw [source_value_type, typed]
            · rwa [typed]
          have cumulative := global_mutation_cumulative_of_shape view code store _ held.shape
            held.storeSyntax held.segmentBounds _ mutation (source_value_wf value) (source_value_owned store value owned)
          refine ⟨held.update cumulative, cumulative, mutation, old, found, mutable, typed, ?_⟩
          simp only [decodeStore, alloc.vec.Vec.set_val_eq, List.map_set, decodeGlobal]
          rw [typed, decode_encoded_value store value owned words encoded]
        · simp only [if_neg typed, ite_true, restored, WP.spec_ok, uncurry_apply_pair]
          exact ⟨held, unchanged, trivial⟩
    · simp only [checkOwner, if_neg owner, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, uncurry_apply_pair]
      exact ⟨held, unchanged, trivial⟩
  · simp only [if_neg sameStore, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, uncurry_apply_pair]
    exact ⟨held, unchanged, trivial⟩

/-- Setting a table updates exactly the issued table and requested element.
All ownership, type, and bounds rejections leave the store unchanged. -/
@[step] theorem _root_.Itasca.runtime.store.Store.set_table.spec {M : Type}
    (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (address : runtime.TableAddr) (index : U32) (value : runtime.Value)
    (issued : ExternalIssued store (.Table address)) (valueIssued : IssuedValue store value) :
    runtime.store.Store.set_table memory store address index value ⦃ (result, after) =>
      ExecutableInv view code after ∧ CumulativeStoreMutation view code store after ∧
      match result with
      | .Err _ => after = store
      | .Ok () => ∃ old : runtime.store.TableInst, ∃ words : U64 × U64,
        store.tables.val[address.index.val]? = some old ∧ index.val < old.elements.length ∧
        elementValueType old.ty = rawType value ∧ runtime.value.encode value = .ok words ∧
        TableMutation store after address old words.1 ∧
        after = {store with
          tables := store.tables.set address.index {old with elements := old.elements.set (UScalar.cast .Usize index) words.1}} ⦄ := by
  classical
  have unchanged := CumulativeStoreMutation.refl_of_shape held.shape held.storeSyntax held.segmentBounds
  unfold runtime.store.Store.set_table
  step with runtime.store.Store.check.spec memory store address.store as ⟨checked, checkEq⟩
  rw [checkEq]
  by_cases sameStore : address.store = store.id
  · simp only [if_pos sameStore, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with check_value_eq memory store value as ⟨checkedValue, valueEq⟩
    rw [valueEq]
    by_cases owner : OwnedBy store.id value
    · simp only [checkOwner, if_pos owner, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      have owned := valueIssued.in_store owner
      have position := issued sameStore
      let old := store.tables.val[address.index.val]
      have found : store.tables.val[address.index.val]? = some old := List.getElem?_eq_getElem position
      have restored : store.tables.set address.index old = store.tables := vec_set_current _ _ position
      have indexed := vec_index_mut_eq store.tables address.index old found
      rw [alloc.vec.Vec.index_mut_slice_index] at indexed
      rw [indexed]
      simp only [bind_ok, bind_tc_ok, element_value_type_exact]
      step with value_type_eq value as ⟨kind, kindEq⟩
      subst kind
      rw [value_type_ne_eq]
      simp only [bind_ok, bind_tc_ok]
      by_cases typed : elementValueType old.ty = rawType value
      · simp only [if_pos typed, Bool.false_eq_true, if_false, lift, bind_ok, bind_tc_ok]
        by_cases outside : UScalar.cast .Usize index ≥ old.elements.len
        · simp only [if_pos outside, restored, WP.spec_ok, uncurry_apply_pair]
          exact ⟨held, unchanged, trivial⟩
        · simp only [if_neg outside]
          have inside : index.val < old.elements.length := by
            have castEq := U32.cast_Usize_val_eq index
            scalar_tac
          have actual : (UScalar.cast .Usize index).val < old.elements.length := by
            simpa only [U32.cast_Usize_val_eq] using inside
          let previous := old.elements.val[(UScalar.cast .Usize index).val]
          have lookup : old.elements.val[(UScalar.cast .Usize index).val]? = some previous :=
            List.getElem?_eq_getElem actual
          obtain ⟨words, encoded, represented⟩ := WP.spec_imp_exists (encode_value_spec value store.id owned.1)
          have reference := encode_reference_shape store value old.ty typed owned
          rw [encoded] at reference
          simp only [WP.spec_ok] at reference
          rw [encoded]
          simp only [bind_ok, bind_tc_ok, lift, alloc.vec.Vec.index_mut_slice_index]
          have element := vec_index_mut_eq old.elements (UScalar.cast .Usize index) previous lookup
          rw [alloc.vec.Vec.index_mut_slice_index] at element
          rw [element]
          simp only [bind_ok, bind_tc_ok, WP.spec_ok, uncurry_apply_pair]
          have mutation : TableMutation store
              {store with
                tables := store.tables.set address.index {old with elements := old.elements.set (UScalar.cast .Usize index) words.1}}
              address old words.1 := by
            refine ⟨_, rfl, ?_, ?_⟩
            · simp only [alloc.vec.Vec.length, alloc.vec.Vec.set_val_eq, List.length_set]
            · intro word member
              exact List.mem_or_eq_of_mem_set (by simpa only [alloc.vec.Vec.set_val_eq] using member)
          have cumulative := table_mutation_cumulative_of_shape view code store _ held.shape
            held.storeSyntax held.segmentBounds address old words.1 found mutation reference
          exact ⟨held.update cumulative, cumulative, old, words, found, inside, typed, rfl, mutation, rfl⟩
      · simp only [if_neg typed, ite_true, restored, WP.spec_ok, uncurry_apply_pair]
        exact ⟨held, unchanged, trivial⟩
    · simp only [checkOwner, if_neg owner, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, uncurry_apply_pair]
      exact ⟨held, unchanged, trivial⟩
  · simp only [if_neg sameStore, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, uncurry_apply_pair]
    exact ⟨held, unchanged, trivial⟩

/-- A mutable memory borrow preserves executable certificates when the caller
writes back the same number of bytes. An error reply restores the original
visible bytes through the platform closure, without equating opaque buffers. -/
@[step] theorem _root_.Itasca.runtime.store.Store.memory_mut.spec {M : Type}
    (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8)
    (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (address : runtime.MemoryAddr) (issued : ExternalIssued store (.Memory address)) :
    runtime.store.Store.memory_mut memory store address ⦃ (result, back) =>
      match result with
      | .Err error => error = .WrongStore ∧ address.store ≠ store.id ∧
        ∀ reply, ExecutableInv view code (back reply) ∧
          CumulativeStoreMutation view code store (back reply) ∧ back reply = store
      | .Ok bytes => ∃ object : runtime.store.MemInst M,
        address.store = store.id ∧ store.memories.val[address.index.val]? = some object ∧
        bytes = view object.buf ∧
        (∀ replacement : Slice U8, replacement.length = bytes.length →
          ExecutableInv view code (back (.Ok replacement)) ∧
          MemoryMutation view store (back (.Ok replacement)) address object ∧
          CumulativeStoreMutation view code store (back (.Ok replacement)) ∧
          (decodeStore view code (back (.Ok replacement))).MEMS =
            (decodeStore view code store).MEMS.set address.index.val
              ⟨(decodeMemory view object).TYPE, decodeBytes replacement.val⟩) ∧
        ∀ error, ExecutableInv view code (back (.Err error)) ∧
          CumulativeStoreMutation view code store (back (.Err error)) ⦄ := by
  unfold runtime.store.Store.memory_mut
  by_cases sameStore : address.store = store.id
  · simp only [bne_iff_ne, if_neg (not_not.mpr sameStore)]
    have position := issued sameStore
    let object := store.memories.val[address.index.val]
    have found : store.memories.val[address.index.val]? = some object := List.getElem?_eq_getElem position
    rw [vec_index_mut_eq store.memories address.index object found]
    simp only [bind_ok, bind_tc_ok]
    obtain ⟨writeBack, borrowed, written⟩ := laws.write object.buf
    simp only [borrowed, bind_ok, WP.spec_ok, uncurry_apply_pair]
    have mutation (replacement : Slice U8) (sameLength : replacement.length = (view object.buf).length) :
        MemoryMutation view store
          {store with memories := store.memories.set address.index {object with buf := writeBack replacement}}
          address object := by
      exact ⟨writeBack replacement, rfl, by rw [written replacement sameLength]; exact sameLength⟩
    have cumulative (replacement : Slice U8) (sameLength : replacement.length = (view object.buf).length) :=
      memory_mutation_cumulative_of_shape view code store _ held.shape held.storeSyntax
        held.segmentBounds address object found (mutation replacement sameLength)
    refine ⟨object, sameStore, found, rfl, ?_, ?_⟩
    · intro replacement sameLength
      refine ⟨held.update (cumulative replacement sameLength), mutation replacement sameLength,
        cumulative replacement sameLength, ?_⟩
      simp only [decodeStore, alloc.vec.Vec.set_val_eq, List.map_set, decodeMemory,
        written replacement sameLength, sameLength]
    · intro error
      exact ⟨held.update (cumulative (view object.buf) rfl), cumulative (view object.buf) rfl⟩
  · simp only [bne_iff_ne, if_pos sameStore, WP.spec_ok, uncurry_apply_pair]
    refine ⟨trivial, sameStore, ?_⟩
    intro reply
    exact ⟨held, CumulativeStoreMutation.refl_of_shape held.shape held.storeSyntax held.segmentBounds, trivial⟩

end Itasca.Runtime.Integration
