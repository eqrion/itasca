import Itasca.Binary.Source
import Itasca.Support.Translation

namespace Itasca.Binary.Source
open Aeneas.Std WebAssembly

private theorem map_eq {f : α → β} (h : Function.Injective f) {xs ys : List α} :
    xs.map f = ys.map f ↔ xs = ys := (List.map_injective_iff.mpr h).eq_iff

private theorem option_eq {f : α → β} (h : Function.Injective f) {x y : Option α} :
    x.map f = y.map f ↔ x = y := Option.map_inj_right (fun _ _ eq => h eq)

private theorem vec_eq {x y : alloc.vec.Vec α} : x.val = y.val ↔ x = y :=
  ⟨alloc.vec.Vec.ext _ _, congrArg _⟩

private theorem unsigned {ty} : Function.Injective (@UScalar.val ty) := @UScalar.eq_of_val_eq _
private theorem signed {ty} : Function.Injective (@IScalar.val ty) := @IScalar.eq_of_val_eq _

private theorem byteInjective : Function.Injective sourceByte := by
  intro x y h
  exact UScalar.eq_of_val_eq (congrArg UInt8.toNat h)

private theorem ueq {ty} {x y : UScalar ty} : x.val = y.val ↔ x = y := unsigned.eq_iff
private theorem ieq {ty} {x y : IScalar ty} : x.val = y.val ↔ x = y := signed.eq_iff
private theorem idxList {xs ys : List U32} : xs.map UScalar.val = ys.map UScalar.val ↔ xs = ys := map_eq unsigned
private theorem idxOpt {x y : Option U32} : x.map UScalar.val = y.map UScalar.val ↔ x = y := option_eq unsigned
private theorem byteList {xs ys : List U8} : xs.map sourceByte = ys.map sourceByte ↔ xs = ys := map_eq byteInjective
attribute [local simp] ueq ieq idxList idxOpt byteList vec_eq

theorem blockTypeInjective : Function.Injective Body.blockType := by
  intro x y h
  cases x <;> cases y <;> simp_all [Body.blockType, Translation.value_type_injective.eq_iff, ueq]

theorem tokenInjective : Function.Injective token := by
  intro x y h
  cases x <;> cases y <;> simp_all [token, blockTypeInjective.eq_iff]

private theorem valueTypeInjective : Function.Injective valueType := by
  intro x y h
  cases x <;> cases y <;> simpa [valueType] using h

theorem referenceType : Function.Injective Translation.referenceType := by
  intro x y h
  cases x <;> cases y <;> simpa [Translation.referenceType] using h

private theorem funcType : Function.Injective Translation.Environment.funcType := by
  intro x y h
  cases x <;> cases y <;> simpa [Translation.Environment.funcType, map_eq Translation.value_type_injective] using h

theorem limitsType : Function.Injective Translation.Environment.limitsType := by
  intro x y h
  have hi : Function.Injective (fun i : U32 => uN.mk_uN i.val) := fun _ _ eq => unsigned (uN.mk_uN.inj eq)
  cases x <;> cases y <;> simpa [Translation.Environment.limitsType, option_eq hi] using h

theorem tableType : Function.Injective Translation.Environment.tableType := by
  intro x y h
  cases x <;> cases y <;> simpa [Translation.Environment.tableType, limitsType.eq_iff, referenceType.eq_iff] using h

theorem memType : Function.Injective Translation.Environment.memType := by
  intro x y h
  cases x <;> cases y <;> simpa [Translation.Environment.memType, limitsType.eq_iff] using h

theorem globalType : Function.Injective Translation.globalType := by
  intro x y h
  cases x <;> cases y <;> simpa [Translation.globalType, Translation.value_type_injective.eq_iff, Translation.mutability_injective.eq_iff] using h

theorem constantInjective : Function.Injective constant := by
  intro x y h
  cases x <;> cases y <;> simpa [constant, referenceType.eq_iff] using h

theorem importDescInjective : Function.Injective importDesc := by
  intro x y h
  cases x <;> cases y <;> simpa [importDesc, tableType.eq_iff, memType.eq_iff, globalType.eq_iff] using h

theorem exportDescInjective : Function.Injective exportDesc := by
  intro x y h
  cases x <;> cases y <;> simpa [exportDesc] using h

theorem elementModeInjective : Function.Injective elementMode := by
  intro x y h
  cases x <;> cases y <;> simpa [elementMode, constantInjective.eq_iff] using h

private theorem dataModeInjective : Function.Injective dataMode := by
  intro x y h
  cases x <;> cases y <;> simpa [dataMode, constantInjective.eq_iff] using h

theorem localDeclInjective : Function.Injective localDecl := by
  intro x y h
  cases x <;> cases y <;> simpa [localDecl, valueTypeInjective.eq_iff] using h

private theorem codeInjective : Function.Injective code := by
  intro x y h
  cases x <;> cases y <;> simpa [code, map_eq localDeclInjective] using h

theorem importEntryInjective : Function.Injective importEntry := by
  intro x y h
  cases x <;> cases y <;> simpa [importEntry, bytes, importDescInjective.eq_iff] using h

theorem globalEntryInjective : Function.Injective globalEntry := by
  intro x y h
  cases x <;> cases y <;> simpa [globalEntry, globalType.eq_iff, constantInjective.eq_iff] using h

theorem exportEntryInjective : Function.Injective exportEntry := by
  intro x y h
  cases x <;> cases y <;> simpa [exportEntry, bytes, exportDescInjective.eq_iff] using h

theorem elementInjective : Function.Injective element := by
  intro x y h
  cases x <;> cases y <;> simpa [element, referenceType.eq_iff, elementModeInjective.eq_iff, map_eq constantInjective] using h

theorem dataEntryInjective : Function.Injective dataEntry := by
  intro x y h
  cases x <;> cases y <;> simpa [dataEntry, bytes, dataModeInjective.eq_iff] using h

/-- The raw source translation preserves every field distinguished by the reader grammar. -/
theorem rawModuleInjective : Function.Injective rawModule := by
  intro x y h
  cases x <;> cases y <;> simpa [rawModule, map_eq funcType, map_eq importEntryInjective, map_eq tableType,
    map_eq memType, map_eq globalEntryInjective, map_eq exportEntryInjective, map_eq elementInjective,
    map_eq codeInjective, map_eq dataEntryInjective] using h

end Itasca.Binary.Source
