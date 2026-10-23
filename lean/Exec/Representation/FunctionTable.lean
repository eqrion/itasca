import Exec.Representation.Store
import Exec.Abs.CallSafety

namespace Exec.Interp
open Aeneas Aeneas.Std

/-- Source function signatures use the same address/type relation as the
abstract machine's module typing context. -/
abbrev FunctionsMatch (store : _root_.store) (moduleInst : moduleinst)
    (functions : List functype) : Prop :=
  List.Forall₂ (fun address ty => ∃ fn, store.FUNCS[address]? = some fn ∧ fn.TYPE = ty)
    moduleInst.FUNCS functions

/-- Concrete signature tables retain issued addresses and actual canonical
signature lookups. This is metadata correspondence, not execution correctness. -/
def FunctionTable {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (functions : List functype) : Prop :=
  List.Forall₂ (fun address ty => address.store = store.id ∧
    ∃ function signature, store.funcs.val[address.index.val]? = some function ∧
      store.types.val[function.signature.val]? = some signature ∧ Store.decodeFuncType signature = ty)
    inst.funcs.val functions

theorem FunctionTable.resolve {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {functions : List functype}
    (table : FunctionTable store inst functions) (index : Nat) (ty : functype)
    (signature : functions[index]? = some ty) :
    ∃ address function rawType, inst.funcs.val[index]? = some address ∧
      address.store = store.id ∧ store.funcs.val[address.index.val]? = some function ∧
      store.types.val[function.signature.val]? = some rawType ∧ Store.decodeFuncType rawType = ty := by
  have within : index < functions.length := (List.getElem?_eq_some_iff.mp signature).1
  have addressBound : index < inst.funcs.val.length := by rw [table.length_eq]; exact within
  have related :=  table.get addressBound within
  obtain ⟨owned, function, rawType, found, typed, decoded⟩ := related
  have actualType : functions[index] = ty := by simpa only [List.getElem?_eq_getElem within, Option.some.injEq] using signature
  exact ⟨inst.funcs.val[index], function, rawType, List.getElem?_eq_getElem addressBound,
    owned, found, typed, decoded.trans actualType⟩

private theorem decodeFunction_type {M : Type} (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (function : runtime.store.FuncInst) (signature : Itasca.types.FuncType)
    (lookup : store.types.val[function.signature.val]? = some signature) :
    (Store.decodeFunction code store function).TYPE = Store.decodeFuncType signature := by
  unfold Store.decodeFunction
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, lookup, Option.map_some, Option.getD_some]
  cases function.code with
  | Host id => rfl
  | Wasm inst fn => dsimp only; split <;> rfl

/-- The concrete table produces the source module-binding relation exactly. -/
theorem FunctionTable.source {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {functions : List functype}
    (table : FunctionTable store inst functions) (view : M → Slice U8)
    (code : Store.CodeInterpretation) :
    FunctionsMatch (Store.decodeStore view code store) (Store.decodeInstance store inst) functions := by
  change List.Forall₂ _ (inst.funcs.val.map (fun a => a.index.val)) functions
  unfold FunctionTable at table
  generalize addressesEq : inst.funcs.val = addresses at table ⊢
  clear addressesEq
  induction table with
  | nil => exact .nil
  | @cons address ty addresses types matching tail ih =>
    apply List.Forall₂.cons _ ih
    obtain ⟨_, function, signature, found, typed, decoded⟩ := matching
    refine ⟨Store.decodeFunction code store function, ?_, (decodeFunction_type code store function signature typed).trans decoded⟩
    simp only [Store.decodeStore, List.getElem?_map, found, Option.map_some]

end Exec.Interp
