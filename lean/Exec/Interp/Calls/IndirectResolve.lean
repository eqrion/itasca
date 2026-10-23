import Exec.Abs.Indirect.Definition
import Exec.Representation.Store

namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt

/-- An actual table range failure is an unresolved source indirect call. -/
theorem indirect_resolve_outside {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (f : Abs.AFrame) (table type position : Nat)
    (object : runtime.store.TableInst)
    (tableEq : fun_table ⟨Store.decodeStore view code store,f.toFrame⟩ (.mk_uN table) = Store.decodeTable object)
    (outside : object.elements.length ≤ position) :
    Abs.Indirect.resolve (Store.decodeStore view code store) f table type position = none := by
  simp [Abs.Indirect.resolve,tableEq,Store.decodeTable,List.getElem?_eq_none outside]

/-- A null runtime table word is exactly a null source reference. -/
theorem indirect_resolve_null {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (f : Abs.AFrame) (table type position : Nat)
    (object : runtime.store.TableInst)
    (tableEq : fun_table ⟨Store.decodeStore view code store,f.toFrame⟩ (.mk_uN table) = Store.decodeTable object)
    (selected : object.elements.val[position]? = some (0#u64)) :
    Abs.Indirect.resolve (Store.decodeStore view code store) f table type position = none := by
  simp [Abs.Indirect.resolve,tableEq,Store.decodeTable,selected,Store.decodeRef]

/-- Nonnull reference resolution retains the entire encoded address and uses
the exact source type comparison of the selected runtime function. -/
theorem indirect_resolve_reference {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (f : Abs.AFrame) (table type position : Nat)
    (object : runtime.store.TableInst) (reference : U64) (address : Usize)
    (function : runtime.store.FuncInst)
    (tableEq : fun_table ⟨Store.decodeStore view code store,f.toFrame⟩ (.mk_uN table) = Store.decodeTable object)
    (funcref : object.ty = .FuncRef)
    (selected : object.elements.val[position]? = some reference)
    (word : reference.val = address.val+1)
    (found : store.funcs.val[address.val]? = some function) :
    Abs.Indirect.resolve (Store.decodeStore view code store) f table type position =
      if fun_type ⟨Store.decodeStore view code store,f.toFrame⟩ (.mk_uN type) =
          (Store.decodeFunction code store function).TYPE then some address.val else none := by
  unfold Abs.Indirect.resolve
  rw [tableEq]
  simp [Store.decodeTable,selected,Store.decodeRef,funcref,word,Store.decodeStore,found]

end Exec.Interp
