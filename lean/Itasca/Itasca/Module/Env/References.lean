import Itasca.Module.CodeMetadata
import Itasca.Module.Definitions
import Itasca.Spec.Typing

/-! Function declarations recorded by global, export and element sections. -/

open WebAssembly Aeneas Aeneas.Std

namespace Itasca.Module.References

def initializer : wasm_types.ConstExpr → List U32
  | .RefFunc index => [index]
  | _ => []

def global (entry : metadata.Global) : List U32 := entry.init.toList.flatMap initializer

def exportIndices (entry : metadata.Export) : List U32 :=
  match entry.desc with
  | .Func index => [index]
  | _ => []

def element (entry : metadata.Element) : List U32 :=
  match entry.init with
  | .Functions indices => indices.val
  | .Expressions exprs => exprs.val.flatMap initializer

def collected (env : metadata.ModuleMetadata metadata.CodeMetadata) : List U32 :=
  env.code.globals.val.flatMap global ++ env.exports.val.flatMap exportIndices ++
    env.elements.val.flatMap element

/-- Repeated declarations of the same index set a single flag. -/
def Coherent (env : metadata.ModuleMetadata metadata.CodeMetadata) : Prop :=
  ∀ i : Nat, uN.mk_uN i ∈ Translation.Environment.declaredReferences env.code ↔
    ∃ idx ∈ collected env, idx.val = i

/-- Updating declarations retains every other descriptor field. -/
structure Added (before after : metadata.CodeMetadata) (indices : List U32) : Prop where
  fields : after = { before with funcs := after.funcs }
  funcs : after.funcs.val = before.funcs.val.zipIdx.map fun (d, i) =>
    { d with can_ref_func := d.can_ref_func || indices.any (fun idx => idx.val == i) }

/-- Setting the declaration flags adds exactly the in-range indices in the section. -/
theorem Added.declared {before after indices} (h : Added before after indices)
    (bound : ∀ idx ∈ indices, idx.val < before.funcs.val.length) (i : Nat) :
    WebAssembly.uN.mk_uN i ∈ Translation.Environment.declaredReferences after ↔
      WebAssembly.uN.mk_uN i ∈ Translation.Environment.declaredReferences before ∨
      ∃ idx ∈ indices, idx.val = i := by
  rw [Translation.Environment.mem_declaredReferences, Translation.Environment.mem_declaredReferences,
    h.funcs]
  by_cases hi : i < before.funcs.val.length
  · simp [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (by simpa using hi :
        i < before.funcs.val.zipIdx.length), List.getElem?_map, List.any_eq_true]
  · have noidx : ¬ ∃ idx ∈ indices, idx.val = i := by
      rintro ⟨idx, hm, rfl⟩; exact hi (bound _ hm)
    simp [List.getElem?_map, List.getElem?_eq_none (by omega : before.funcs.val.length ≤ i),
      List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hi : before.funcs.val.zipIdx.length ≤ i), noidx]

/-- The declared indices of a constant expression match those the SpecTec reference collector finds
in its instruction form. -/
theorem initializer_indices (value : wasm_types.ConstExpr) :
    Spec.DeclaredReferences.instructionsIndices true (Module.Constants.expression value) =
      (initializer value).map (fun index => uN.mk_uN index.val) := by
  cases value <;> simp [Module.Constants.expression, Module.Constants.instruction,
    initializer, Spec.DeclaredReferences.instructionsIndices, Spec.DeclaredReferences.instructionIndices,
    Spec.i32Const, Spec.Constants.i64, Spec.Constants.f32, Spec.Constants.f64]

end Itasca.Module.References

namespace Itasca.metadata

/-- Initializer validation has already checked any referenced function index. -/
@[step] theorem declare_initializer.spec (env : CodeMetadata) (init : wasm_types.ConstExpr)
    (valid : ∀ idx ∈ Module.References.initializer init, idx.val < env.funcs.val.length) :
    declare_initializer env init ⦃ out =>
      Module.References.Added env out (Module.References.initializer init) ⦄ := by
  cases init <;> simp only [declare_initializer, Module.References.initializer, WP.spec_ok] at *
  all_goals try
    constructor
    · rfl
    · apply List.ext_getElem <;> simp
  rename_i idx
  have hi : idx.val < env.funcs.val.length := valid idx (by simp)
  step*
  constructor
  · rfl
  · apply List.ext_getElem
    · simp [index_mut_back_post]
    · intro i h₁ h₂
      by_cases he : idx.val = i
      · subst i
        simp [alloc.vec.Vec.set, *]
      · have hbe : (idx.val == i) = false := beq_eq_false_iff_ne.mpr he
        simp [alloc.vec.Vec.set, hbe, *]

end Itasca.metadata
