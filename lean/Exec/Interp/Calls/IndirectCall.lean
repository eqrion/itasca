import Exec.Interp.Calls.DirectCall
set_option maxRecDepth 4096

namespace Exec.Interp
open Aeneas Aeneas.Std

/-- Actual indirect resolution checks the table position, null reference, and
interned signature before delegating to the ordinary call implementation. -/
theorem execute_call_indirect_effect {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (instanceIndex functionIndex base : Usize) (entry index callee : U32)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (table type : U32) (tableAddress : runtime.TableAddr) (object : runtime.store.TableInst)
    (position : U32) (signature calleeBase : Usize)
    (instanceFound : store.instances.val[instanceIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[functionIndex.val]? = some compiled)
    (pairFound : compiled.indirect.val[entry.val]? = some (table,type))
    (tableMapped : inst.tables.val[table.val]? = some tableAddress)
    (tableFound : store.tables.val[tableAddress.index.val]? = some object)
    (input : UScalar.cast .U32 exec.slots.val[base.val+index.val]! = position)
    (indexBound : base.val+index.val < exec.slots.length)
    (signatureFound : inst.types.val[type.val]? = some signature)
    (baseOffset : calleeBase.val = base.val+callee.val)
    (targets : ∀ reference : U64, object.elements.val[position.val]? = some reference →
      reference ≠ 0#u64 → ∃ address : Usize, ∃ function : runtime.store.FuncInst,
        (UScalar.cast .Usize reference).val = address.val+1 ∧
        store.funcs.val[address.val]? = some function)
    (post : core.result.Result Unit runtime.ExecError × runtime.interp.Execution ×
      runtime.store.Store M × P → Prop)
    (outside : ¬position.val < object.elements.length →
      post (.Err (.Trap .TableOutOfBounds),exec,store,platform))
    (null : object.elements.val[position.val]? = some (0#u64) →
      post (.Err (.Trap .UninitializedElement),exec,store,platform))
    (mismatch : ∀ (reference : U64) (address : Usize) (function : runtime.store.FuncInst),
      object.elements.val[position.val]? = some reference → reference ≠ 0#u64 →
      (UScalar.cast .Usize reference).val = address.val+1 →
      store.funcs.val[address.val]? = some function → function.signature ≠ signature →
      post (.Err (.Trap .IndirectCallTypeMismatch),exec,store,platform))
    (called : ∀ (reference : U64) (address : Usize) (function : runtime.store.FuncInst),
      object.elements.val[position.val]? = some reference → reference ≠ 0#u64 →
      (UScalar.cast .Usize reference).val = address.val+1 →
      store.funcs.val[address.val]? = some function → function.signature = signature →
      runtime.interp.call memory hooks floats allocator exec store platform
        {store := store.id,index := address} calleeBase ⦃ post ⦄) :
    runtime.interp.execute_call_indirect memory hooks floats allocator exec store platform
      instanceIndex functionIndex base entry index callee ⦃ post ⦄ := by
  unfold runtime.interp.execute_call_indirect
  step with vec_index_given store.instances instanceIndex inst instanceFound as ⟨found,hfound⟩
  subst found
  step with vec_index_given inst.module.functions functionIndex compiled functionFound as ⟨found,hfound⟩
  subst found
  simp only [lift,bind_ok]
  step with vec_index_given compiled.indirect (UScalar.cast .Usize entry) (table,type)
    (by simpa only [U32.cast_Usize_val_eq] using pairFound) as ⟨foundTable,foundType,hfoundTable,hfoundType⟩
  subst foundTable
  subst foundType
  step with vec_index_given inst.tables (UScalar.cast .Usize table) tableAddress
    (by simpa only [U32.cast_Usize_val_eq] using tableMapped) as ⟨found,hfound⟩
  subst found
  step as ⟨slot,slotEq⟩
  have slotValue : slot.val = base.val+index.val := by scalar_tac
  have inputFound : exec.slots.val[slot.val]? = some exec.slots.val[base.val+index.val]! := by
    rw [slotValue,getElem!_pos exec.slots.val _ indexBound]
    exact List.getElem?_eq_getElem indexBound
  step with vec_index_given exec.slots slot exec.slots.val[base.val+index.val]! inputFound as ⟨word,wordEq⟩
  have wordInput : UScalar.cast .U32 word = position := by simpa only [wordEq] using input
  simp only [wordInput]
  step with vec_index_given store.tables tableAddress.index object tableFound as ⟨found,hfound⟩
  subst found
  simp only [alloc.vec.Vec.len]
  split
  · rename_i h
    have bound : ¬position.val < object.elements.length := by scalar_tac
    simpa [runtime.ExecError.Insts.CoreConvertFromTrap.from] using outside bound
  · rename_i h
    have bound : position.val < object.elements.length := by scalar_tac
    have refFound : object.elements.val[position.val]? = some object.elements.val[position.val]! := by
      rw [getElem!_pos object.elements.val _ bound]
      exact List.getElem?_eq_getElem bound
    step with vec_index_given object.elements (UScalar.cast .Usize position)
      object.elements.val[position.val]! (by simpa only [U32.cast_Usize_val_eq] using refFound)
      as ⟨reference,referenceEq⟩
    have selected : object.elements.val[position.val]? = some reference := by simpa only [referenceEq] using refFound
    split
    · rename_i zero
      simpa [runtime.ExecError.Insts.CoreConvertFromTrap.from] using null (by simpa only [zero] using selected)
    · rename_i nonzero
      obtain ⟨address,function,addressEq,targetFound⟩ := targets reference selected nonzero
      step as ⟨actualAddress,actualEq⟩
      have sameAddress : actualAddress = address := by scalar_tac
      subst actualAddress
      step with vec_index_given store.funcs address function targetFound as ⟨found,hfound⟩
      subst found
      step with vec_index_given inst.types (UScalar.cast .Usize type) signature
        (by simpa only [U32.cast_Usize_val_eq] using signatureFound) as ⟨found,hfound⟩
      subst found
      split
      · rename_i different
        have ne : function.signature ≠ signature := by simpa using different
        simpa [runtime.ExecError.Insts.CoreConvertFromTrap.from] using
          mismatch reference address function selected nonzero addressEq targetFound ne
      · rename_i same
        have eq : function.signature = signature := UScalar.eq_of_val_eq (by simpa using same)
        step as ⟨actualBase,hbase⟩
        have sameBase : actualBase = calleeBase := by
          apply UScalar.eq_of_val_eq
          simpa only [U32.cast_Usize_val_eq,baseOffset] using hbase
        subst actualBase
        exact called reference address function selected nonzero addressEq targetFound eq

end Exec.Interp
