import Itasca.Binary.Wasm2.References
import Itasca.Binary.Wasm2.Bulk
import Itasca.Binary.PrefixUnique

open Aeneas Aeneas.Std

namespace Itasca.MultiValue

open ModuleBinary

theorem ReferencesBinary.Immediate.prefix_unique (opcode : U8) :
    PrefixUnique (ReferencesBinary.Immediate opcode) := by
  intro x y a b rest tail hx hy he
  cases hx <;> cases hy
  case refNull.refNull =>
    rename_i x y
    obtain ⟨hv, rfl⟩ := List.cons.inj he
    have heq : x = y := by cases x <;> cases y <;> simp_all [ReferencesBinary.referenceByte]
    subst y
    exact ⟨rfl, rfl, rfl⟩
  case refIsNull.refIsNull => exact ⟨rfl, rfl, he⟩
  case refFunc.refFunc | tableGet.tableGet | tableSet.tableSet =>
    rename_i x hx y hy
    obtain ⟨hv, rfl, rfl⟩ := leb_prefix_unique hx hy he
    obtain rfl := UScalar.eq_of_val_eq hv
    exact ⟨rfl, rfl, rfl⟩
  case selectTyped.selectTyped =>
    rename_i x count hx y count' hy
    obtain ⟨_, rfl, hrest⟩ := leb_prefix_unique hx hy (by simpa [List.append_assoc] using he)
    obtain ⟨hv, rfl⟩ := List.cons.inj hrest
    obtain rfl := valueByte_injective hv
    exact ⟨rfl, rfl, rfl⟩
  case callIndirect.callIndirect =>
    rename_i tx ix tbs ibs ht hi ty iy tbs' ibs' ht' hi'
    obtain ⟨hv, rfl, hrest⟩ := leb_prefix_unique ht ht' (by simpa [List.append_assoc] using he)
    obtain ⟨hv', rfl, rfl⟩ := leb_prefix_unique hi hi' hrest
    obtain rfl := UScalar.eq_of_val_eq hv
    obtain rfl := UScalar.eq_of_val_eq hv'
    exact ⟨rfl, rfl, rfl⟩

theorem BulkBinary.Immediate.prefix_unique (opcode : U32) :
    PrefixUnique (BulkBinary.Immediate opcode) := by
  intro x y a b rest tail hx hy he
  cases hx <;> cases hy
  case memoryInit.memoryInit =>
    rename_i x bs hx y bs' hy
    obtain ⟨hv, rfl, hrest⟩ := leb_prefix_unique hx hy (by simpa [List.append_assoc] using he)
    obtain rfl := UScalar.eq_of_val_eq hv
    exact ⟨rfl, rfl, (List.cons.inj hrest).2⟩
  case dataDrop.dataDrop | elemDrop.elemDrop | tableGrow.tableGrow |
      tableSize.tableSize | tableFill.tableFill =>
    rename_i x hx y hy
    obtain ⟨hv, rfl, rfl⟩ := leb_prefix_unique hx hy he
    obtain rfl := UScalar.eq_of_val_eq hv
    exact ⟨rfl, rfl, rfl⟩
  case memoryCopy.memoryCopy => exact ⟨rfl, rfl, (List.cons.inj (List.cons.inj he).2).2⟩
  case memoryFill.memoryFill => exact ⟨rfl, rfl, (List.cons.inj he).2⟩
  case tableInit.tableInit | tableCopy.tableCopy =>
    rename_i ax bx abs bbs ha hb ay by_ abs' bbs' ha' hb'
    obtain ⟨hv, rfl, hrest⟩ := leb_prefix_unique ha ha' (by simpa [List.append_assoc] using he)
    obtain ⟨hv', rfl, rfl⟩ := leb_prefix_unique hb hb' hrest
    obtain rfl := UScalar.eq_of_val_eq hv
    obtain rfl := UScalar.eq_of_val_eq hv'
    exact ⟨rfl, rfl, rfl⟩

end Itasca.MultiValue
