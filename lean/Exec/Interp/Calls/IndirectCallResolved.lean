import Exec.Interp.Calls.IndirectCall
namespace Exec.Interp
open Aeneas Aeneas.Std

/-- A concrete non-null, signature-matched table entry makes the extracted
indirect-call handler invoke exactly its resolved function address. -/
theorem admin_call_indirect_resolved {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (instanceIndex functionIndex base : Usize) (entry index callee : U32)
    (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
    (table type : U32) (tableAddress : runtime.TableAddr) (object : runtime.store.Table)
    (position : U32) (signature calleeBase address : Usize)
    (reference : U64) (function : runtime.store.Function)
    (instanceFound : store.instances.val[instanceIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[functionIndex.val]? = some compiled)
    (pairFound : compiled.indirect.val[entry.val]? = some (table,type))
    (tableMapped : inst.tables.val[table.val]? = some tableAddress)
    (tableFound : store.tables.val[tableAddress.index.val]? = some object)
    (input : UScalar.cast .U32 exec.slots.val[base.val+index.val]! = position)
    (indexBound : base.val+index.val < exec.slots.length)
    (signatureFound : inst.types.val[type.val]? = some signature)
    (baseOffset : calleeBase.val = base.val+callee.val)
    (selected : object.elements.val[position.val]? = some reference)
    (nonzero : reference ≠ 0#u64)
    (addressEq : (UScalar.cast .Usize reference).val = address.val+1)
    (targetFound : store.funcs.val[address.val]? = some function)
    (signatureEq : function.signature = signature)
    (post : core.result.Result Unit runtime.ExecError × runtime.interp.Execution ×
      runtime.store.Store M × P → Prop)
    (called : runtime.interp.call memory hooks floats allocator exec store platform
      ⟨store.id,address⟩ calleeBase ⦃ post ⦄) :
    runtime.interp.admin_call_indirect memory hooks floats allocator exec store platform
      instanceIndex functionIndex base entry index callee ⦃ post ⦄ := by
  apply admin_call_indirect_effect memory hooks floats allocator exec store platform
    instanceIndex functionIndex base entry index callee inst compiled table type tableAddress object
    position signature calleeBase instanceFound functionFound pairFound tableMapped tableFound input
    indexBound signatureFound baseOffset
  · intro actual lookup _
    have same : actual = reference := Option.some.inj (lookup.symm.trans selected)
    subst actual
    exact ⟨address,function,addressEq,targetFound⟩
  · intro outside
    exact False.elim (outside (List.getElem?_eq_some_iff.mp selected).1)
  · intro null
    exact False.elim (nonzero (Option.some.inj (selected.symm.trans null)))
  · intro actual target fn lookup _ encoded found mismatch
    have same : actual = reference := Option.some.inj (lookup.symm.trans selected)
    subst actual
    have sameAddress : target = address := by scalar_tac
    subst target
    have sameFunction : fn = function := Option.some.inj (found.symm.trans targetFound)
    subst fn
    exact False.elim (mismatch signatureEq)
  · intro actual target fn lookup _ encoded found _
    have same : actual = reference := Option.some.inj (lookup.symm.trans selected)
    subst actual
    have sameAddress : target = address := by scalar_tac
    subst target
    exact called
end Exec.Interp
