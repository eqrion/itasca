import Exec.Code.Local.Lowering.Float.FloatCoreEmission
namespace Exec.Code
open Aeneas.Std

/-- An indirect call retains both source indices and the actual function-local
pair entry. The table selector follows the full parameter word region. -/
inductive IndirectCallEmission (pairs : List (U32 × U32)) (C : context) :
    List valtype → instr → List Bytecode → List valtype → Prop where
  | call (front params results : List valtype) (typeIndex tableIndex entry index base : U32)
      (bounds : limits)
      (signature : C.TYPES[typeIndex.val]? = some ⟨.mk_list params,.mk_list results⟩)
      (table : C.TABLES[tableIndex.val]? = some (.mk_tabletype bounds .FUNCREF))
      (pair : pairs[entry.val]? = some (tableIndex,typeIndex))
      (basePosition : base.val = slots C.LOCALS + slots front)
      (indexPosition : index.val = base.val + slots params) :
      IndirectCallEmission pairs C ((front ++ params) ++ [.I32])
        (.CALL_INDIRECT (.mk_uN tableIndex.val) (.mk_uN typeIndex.val))
        [.CallIndirect entry index base] (front ++ results)

theorem IndirectCallEmission.length_one {pairs C before instruction emitted after}
    (emission : IndirectCallEmission pairs C before instruction emitted after) : emitted.length = 1 := by
  cases emission; rfl

theorem IndirectCallEmission.append_pairs {pairs C before instruction emitted after}
    (emission : IndirectCallEmission pairs C before instruction emitted after)
    (extra : List (U32 × U32)) :
    IndirectCallEmission (pairs ++ extra) C before instruction emitted after := by
  cases emission with
  | call front params results typeIndex tableIndex entry index base bounds signature table pair basePosition indexPosition =>
    apply IndirectCallEmission.call front params results typeIndex tableIndex entry index base bounds signature table
      _ basePosition indexPosition
    have bound := (List.getElem?_eq_some_iff.mp pair).1
    simpa [List.getElem?_append,bound] using pair
end Exec.Code
