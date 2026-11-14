import Itasca.Runtime.Store.Api.MemoryBindingLoop
import Itasca.Runtime.Store.Linking.LinkLoop

/-! Exact byte-name comparison and export search, without decoding query bytes. -/

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

@[step] theorem _root_.Itasca.metadata.Env.impl.exports.spec (env : Itasca.metadata.Env) :
    Itasca.metadata.Env.impl.exports env ⦃ exports => exports = env.exports.deref ⦄ := by
  simp only [Itasca.metadata.Env.impl.exports, WP.spec_ok]

@[step] theorem _root_.Itasca.runtime.store.same_bytes_loop.spec
    (left right : Slice U8) (index : Usize) (same : Bool)
    (lengths : left.length = right.length) (inside : index.val ≤ left.length) :
    runtime.store.same_bytes_loop left right index same ⦃ result =>
      result = (same && decide (left.val.drop index.val = right.val.drop index.val)) ⦄ := by
  unfold runtime.store.same_bytes_loop
  apply loop.spec_decr_nat (fun state => left.length - state.1.val)
    (fun state => state.1.val ≤ left.length ∧
      (state.2 && decide (left.val.drop state.1.val = right.val.drop state.1.val)) =
        (same && decide (left.val.drop index.val = right.val.drop index.val)))
  · intro state invariant
    rcases state with ⟨position, equal⟩
    rcases invariant with ⟨bound, preserved⟩
    unfold runtime.store.same_bytes_loop.body
    dsimp only at bound preserved ⊢
    by_cases more : position < left.len
    · simp only [if_pos more]
      have leftBound : position.val < left.length := by scalar_tac
      have rightBound : position.val < right.length := by omega
      have capacity : position.val < Usize.max := by scalar_tac
      cases equal with
      | false => simpa only [Bool.false_eq_true, ite_false, Bool.false_and, WP.spec_ok] using preserved
      | true =>
        simp only [ite_true]
        step as ⟨first, firstEq⟩
        step as ⟨second, secondEq⟩
        step as ⟨next, nextEq⟩
        refine ⟨?_, ?_, ?_⟩
        · omega
        · rw [List.drop_eq_getElem_cons leftBound, List.drop_eq_getElem_cons rightBound] at preserved
          simpa only [nextEq, firstEq, secondEq, List.cons.injEq, Bool.decide_and, Bool.true_and] using preserved
        · omega
    · simp only [if_neg more]
      have last : position.val = left.length := by scalar_tac
      simp only [Slice.length] at last lengths
      have rightLast : position.val = right.val.length := by omega
      simpa only [List.drop_eq_nil_iff.mpr (by omega : left.val.length ≤ position.val),
        List.drop_eq_nil_iff.mpr (by omega : right.val.length ≤ position.val),
        Bool.and_true, decide_true, WP.spec_ok] using preserved
  · exact ⟨inside, rfl⟩

@[step] theorem _root_.Itasca.runtime.store.same_bytes.spec (left right : Slice U8) :
    runtime.store.same_bytes left right ⦃ result => result = decide (left.val = right.val) ⦄ := by
  unfold runtime.store.same_bytes
  dsimp only
  by_cases different : (left.len != right.len) = true
  · simp only [if_pos different]
    have lengths : left.length ≠ right.length := by scalar_tac
    have unequal : left.val ≠ right.val := fun same => lengths (congrArg List.length same)
    simp only [WP.spec_ok, unequal, decide_false]
  · simp only [if_neg different]
    have lengths : left.length = right.length := by scalar_tac
    step with runtime.store.same_bytes_loop.spec left right 0#usize true lengths (by scalar_tac)
      as ⟨result, compared⟩
    simp only [UScalar.ofNatCore_val_eq, List.drop_zero, Bool.true_and] at compared
    exact compared

/-- Resolve a validated raw descriptor through the instance address maps. -/
def resolveExport (inst : runtime.store.ModuleInst) (entry : Itasca.metadata.Export) : runtime.Extern :=
  match entry.desc with
  | .Func index => .Func (inst.funcs.val.getD index.val ⟨0#usize, 0#usize⟩)
  | .Table index => .Table (inst.tables.val.getD index.val ⟨0#usize, 0#usize⟩)
  | .Memory index => .Memory (inst.memories.val.getD index.val ⟨0#usize, 0#usize⟩)
  | .Global index => .Global (inst.globals.val.getD index.val ⟨0#usize, 0#usize⟩)

/-- First matching raw byte-name at or after the supplied cursor. -/
def exportSearch (inst : runtime.store.ModuleInst) (query : Slice U8) (index : Nat)
    (found : Option runtime.Extern) : Option runtime.Extern :=
  found.orElse fun _ => ((inst.module.module.env.exports.val.drop index).find?
    (fun entry => decide (entry.name.val = query.val))).map (resolveExport inst)

@[step] theorem _root_.Itasca.runtime.store.Store.export_loop.spec {M : Type}
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst)
    (bounds : ModuleExportBounds inst.module.module.env) (shape : InstanceShape store inst)
    (query : Slice U8) (index : Usize) (found : Option runtime.Extern)
    (inside : index.val ≤ inst.module.module.env.exports.length) :
    runtime.store.Store.export_loop query inst.funcs inst.tables inst.memories inst.globals
      inst.module.module.env index found ⦃ result => result = exportSearch inst query index.val found ⦄ := by
  unfold runtime.store.Store.export_loop
  apply loop.spec_decr_nat (fun state => inst.module.module.env.exports.length - state.1.val)
    (fun state => state.1.val ≤ inst.module.module.env.exports.length ∧
      exportSearch inst query state.1.val state.2 = exportSearch inst query index.val found)
  · intro state invariant
    rcases state with ⟨position, prior⟩
    rcases invariant with ⟨bound, preserved⟩
    unfold runtime.store.Store.export_loop.body
    step with Itasca.metadata.Env.impl.exports.spec inst.module.module.env as ⟨exports, exportsEq⟩
    subst exports
    by_cases more : position < inst.module.module.env.exports.deref.len
    · simp only [if_pos more]
      simp only [alloc.vec.Vec.deref, Slice.len, Slice.length, Slice.from_val] at more
      have available : position.val < inst.module.module.env.exports.length := by scalar_tac
      have capacity : position.val < Usize.max := by scalar_tac
      cases prior with
      | some external =>
        simpa only [core.option.Option.is_none, Option.isNone, Bool.false_eq_true, ite_false, exportSearch, Option.orElse, WP.spec_ok] using preserved
      | none =>
        simp only [core.option.Option.is_none, Option.isNone, ite_true]
        have sliceBound : position.val < inst.module.module.env.exports.deref.length := by
          simpa only [alloc.vec.Vec.deref, Slice.length, Slice.from_val, alloc.vec.Vec.length] using available
        step as ⟨entry, entryEq⟩
        simp only [alloc.vec.Vec.deref, Slice.from_val] at entryEq
        have member : entry ∈ inst.module.module.env.exports.val := by
          rw [entryEq]
          exact List.getElem_mem available
        have mapped := export_address_bounds bounds shape entry member
        step with runtime.store.same_bytes.spec entry.name.deref query as ⟨same, sameEq⟩
        rw [sameEq]
        by_cases matching : entry.name.val = query.val
        · simp only [alloc.vec.Vec.deref, Slice.from_val, matching, decide_true, ite_true]
          have resolved : (match entry.desc with
            | .Func n => do
              let address ← inst.funcs.index_usize (UScalar.cast .Usize n)
              pure (runtime.Extern.Func address)
            | .Table n => do
              let address ← inst.tables.index_usize (UScalar.cast .Usize n)
              pure (runtime.Extern.Table address)
            | .Memory n => do
              let address ← inst.memories.index_usize (UScalar.cast .Usize n)
              pure (runtime.Extern.Memory address)
            | .Global n => do
              let address ← inst.globals.index_usize (UScalar.cast .Usize n)
              pure (runtime.Extern.Global address)) ⦃ answer => answer = resolveExport inst entry ⦄ := by
            cases descriptor : entry.desc <;> simp only [descriptor] at mapped ⊢ <;>
              step as ⟨address, addressEq⟩ <;>
              simp only [resolveExport, descriptor, addressEq, U32.cast_Usize_val_eq,
                List.getD_eq_getElem _ _ mapped]
          simp only [lift, bind_ok]
          step with resolved as ⟨external, externalEq⟩
          subst external
          step as ⟨next, nextEq⟩
          refine ⟨by omega, ?_, by omega⟩
          rw [exportSearch, List.drop_eq_getElem_cons available] at preserved
          simpa only [exportSearch, Option.orElse, List.find?_cons, ← entryEq, matching,
            decide_true, ite_true, Option.map_some] using preserved
        · have notMatching : (decide (entry.name.val = query.val)) = false := by
            simp only [matching, decide_false]
          simp only [alloc.vec.Vec.deref, Slice.from_val, matching, decide_false, Bool.false_eq_true, ite_false, bind_ok]
          step as ⟨next, nextEq⟩
          refine ⟨by omega, ?_, by omega⟩
          rw [exportSearch, List.drop_eq_getElem_cons available] at preserved
          simpa only [exportSearch, Option.orElse, List.find?_cons, ← entryEq,
            notMatching, ite_false, nextEq] using preserved
    · simp only [if_neg more]
      simp only [alloc.vec.Vec.deref, Slice.len, Slice.length, Slice.from_val] at more
      have last : position.val = inst.module.module.env.exports.length := by scalar_tac
      cases prior <;> simpa only [exportSearch, last, alloc.vec.Vec.length, List.drop_length,
        List.find?_nil, Option.map_none, Option.orElse, WP.spec_ok] using preserved
  · exact ⟨inside, rfl⟩

/-- A resolved validated export denotes an issued address of this store. -/
theorem resolveExport_issued {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (bounds : ModuleExportBounds inst.module.module.env)
    (shape : InstanceShape store inst) (entry : Itasca.metadata.Export)
    (member : entry ∈ inst.module.module.env.exports.val) :
    ExternalIssued store (resolveExport inst entry) := by
  have bound := export_address_bounds bounds shape entry member
  obtain ⟨_, _, _, _, _, _, _, _, funcs, tables, memories, globals, _, _⟩ := shape
  cases descriptor : entry.desc <;> simp only [descriptor] at bound
  · simp only [resolveExport, descriptor, List.getD_eq_getElem _ _ bound, ExternalIssued]
    exact fun _ => (funcs _ (List.getElem_mem bound)).2
  · simp only [resolveExport, descriptor, List.getD_eq_getElem _ _ bound, ExternalIssued]
    exact fun _ => (tables _ (List.getElem_mem bound)).2
  · simp only [resolveExport, descriptor, List.getD_eq_getElem _ _ bound, ExternalIssued]
    exact fun _ => (memories _ (List.getElem_mem bound)).2
  · simp only [resolveExport, descriptor, List.getD_eq_getElem _ _ bound, ExternalIssued]
    exact fun _ => (globals _ (List.getElem_mem bound)).2

/-- The raw address selected by an export agrees with its decoded source address. -/
theorem resolveExport_source {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (bounds : ModuleExportBounds inst.module.module.env)
    (shape : InstanceShape store inst) (entry : Itasca.metadata.Export)
    (member : entry ∈ inst.module.module.env.exports.val) :
    (decodeExport inst entry).ADDR = decodeExternal (resolveExport inst entry) := by
  have bound := export_address_bounds bounds shape entry member
  cases descriptor : entry.desc <;> simp only [descriptor] at bound <;>
    simp only [decodeExport, decodeExternal, resolveExport, descriptor, List.getD_eq_getElem _ _ bound,
      List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem bound,
      Option.map_some, Option.getD_some]

/-- A missing result means precisely that no raw export name matches the query. -/
theorem exportSearch_none_iff (inst : runtime.store.ModuleInst) (query : Slice U8) :
    exportSearch inst query 0 none = none ↔
      ∀ entry ∈ inst.module.module.env.exports.val, entry.name.val ≠ query.val := by
  simp only [exportSearch, Option.orElse, List.drop_zero, Option.map_eq_none_iff,
    List.find?_eq_none, decide_eq_true_eq]

/-- A successful search supplies the matching raw descriptor, not merely a decoded name. -/
theorem exportSearch_some (inst : runtime.store.ModuleInst) (query : Slice U8)
    (external : runtime.Extern) (found : exportSearch inst query 0 none = some external) :
    ∃ entry ∈ inst.module.module.env.exports.val,
      entry.name.val = query.val ∧ resolveExport inst entry = external := by
  simp only [exportSearch, Option.orElse, List.drop_zero] at found
  obtain ⟨entry, searched, resolved⟩ := Option.map_eq_some_iff.mp found
  have matching := List.find?_some searched
  refine ⟨entry, List.mem_of_find?_eq_some searched, ?_, resolved⟩
  simpa only [decide_eq_true_eq] using matching

end Itasca.Runtime.Store
