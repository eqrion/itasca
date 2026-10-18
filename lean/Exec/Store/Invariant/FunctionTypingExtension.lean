import Exec.Abs.ModuleBindingsExtension
import Exec.Store.Invariant.Extension
import Exec.Store.Initialization.SegmentReady
namespace Exec.Store
open Aeneas Aeneas.Std

/-- Every old concrete function retains its generated source typing when
instantiation appends objects and signatures. New definitions are handled by
the independent canonical module certificate. -/
theorem staged_functions_typed_old {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (before after : runtime.store.Store M)
    (beforeShape : Shape view before) (afterShape : Shape view after)
    (beforeSyntax : StoreSyntax code before) (afterSyntax : StoreSyntax code after)
    (retained : StagedPrefix before after)
    (typed : Abs.FunctionsTyped (decodeStore view code before))
    (function : runtime.store.Function) (member : function ∈ before.funcs.val) :
    let fn := decodeFunction code after function
    match fn.CODE with
    | .HOST _ => Functype_ok fn.TYPE
    | .FUNC index locals body => ∃ C, Abs.ModuleBindings (decodeStore view code after) fn.MODULE C ∧
        C.LOCALS = [] ∧ C.LABELS = [] ∧ C.RETURN = none ∧
        Func_ok C (.FUNC index locals body) fn.TYPE := by
  dsimp only
  rw [decodeFunction_prefix code before after retained view beforeShape function member]
  exact typed.extend_old
    (staged_extends view code before after beforeShape afterShape beforeSyntax afterSyntax retained)
    (decodeFunction code before function) (List.mem_map.mpr ⟨function, member, rfl⟩)

/-- Old function typing only needs syntactic well-formedness of the staged
store. Resource accounting may still be uncharged until commit. -/
theorem staged_functions_typed_old_wf {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (before after : runtime.store.Store M) (beforeShape : Shape view before)
    (beforeSyntax : StoreSyntax code before)
    (afterWf : wf_store (decodeStore view code after))
    (retained : StagedPrefix before after)
    (typed : Abs.FunctionsTyped (decodeStore view code before))
    (function : runtime.store.Function) (member : function ∈ before.funcs.val) :
    let fn := decodeFunction code after function
    match fn.CODE with
    | .HOST _ => Functype_ok fn.TYPE
    | .FUNC index locals body => ∃ C, Abs.ModuleBindings (decodeStore view code after) fn.MODULE C ∧
        C.LOCALS = [] ∧ C.LABELS = [] ∧ C.RETURN = none ∧
        Func_ok C (.FUNC index locals body) fn.TYPE := by
  obtain ⟨functions, globals, tables, memories, elements, datas⟩ :=
    decodeStore_prefix view code before after beforeShape retained
  have extension := store_prefix_extends _ _
    (decodeStore_wf view code before beforeShape beforeSyntax) afterWf
    functions globals tables memories elements datas
  dsimp only
  rw [decodeFunction_prefix code before after retained view beforeShape function member]
  exact typed.extend_old extension (decodeFunction code before function)
    (List.mem_map.mpr ⟨function, member, rfl⟩)

/-- Initializer mutations preserve decoded functions, including their indirect
signature and instance dependencies. -/
theorem SegmentAddressSpace.decoded_functions {M : Type} {before after : runtime.store.Store M}
    (metadata : SegmentAddressSpace before after) (view : M → Slice U8) (code : CodeInterpretation) :
    (decodeStore view code after).FUNCS = (decodeStore view code before).FUNCS := by
  have same : decodeFunction code after = decodeFunction code before := by
    funext function
    simp only [decodeFunction, decodeInstance, metadata.signatures, metadata.instances]
  simp only [decodeStore, metadata.functions, same]

/-- Semantic extension of the initialized store transports all function-body
typing, even when initialization returns a trap after earlier writes. -/
theorem SegmentAddressSpace.functions_typed {M : Type} {before after : runtime.store.Store M}
    (metadata : SegmentAddressSpace before after) (view : M → Slice U8) (code : CodeInterpretation)
    (extension : Extend_store (decodeStore view code before) (decodeStore view code after))
    (typed : Abs.FunctionsTyped (decodeStore view code before)) :
    Abs.FunctionsTyped (decodeStore view code after) :=
  typed.extend_same extension (metadata.decoded_functions view code)
end Exec.Store
