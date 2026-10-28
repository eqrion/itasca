import Itasca.Runtime.Theorems.Composition.SignatureWords
import Itasca.Runtime.Theorems.Api.InvocationBoundary
import Itasca.Runtime.Interp.Relations.SourceIndirectResources
namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

/-- Allocator refusal sizes for the public argument/result buffers. -/
def SignatureAllocation {A : Type} (allocator : runtime.platform.Alloc A) (signature : functype) : Prop :=
  (∃ (slots : alloc.vec.Vec U64) (n : Usize), n.val≤signatureWords signature ∧
    allocator.reserve slots n=.ok (false,slots)) ∨
  (∃ (results : alloc.vec.Vec runtime.Value) (n : Usize), n.val≤signature.2.1.length ∧
    allocator.reserve results n=.ok (false,results))

/-- Actual refusal witnesses use only source signature/frame requirements.
Signature buffers are explicit; this does not revise the planned T4 contract. -/
def CanonicalInvocationResourceCause {A M P : Type} (allocator : runtime.platform.Alloc A)
    (hooks : runtime.platform.Platform P M) (initial : config) (store : _root_.store)
    (signature : functype) (address : funcaddr) (valueLimit frameLimit : Nat) : runtime.ExecError → Prop
  | .Exhausted .Values =>
    valueLimit<signatureWords signature ∨
    (∃ words, SourceCanonicalFunctionCapacity store address words ∧ valueLimit<words) ∨
    ∃ source callee base words, StepsH initial [] (Abs.decode source) ∧
      SourceInvocationSite source callee base ∧ SourceCanonicalFunctionCapacity source.store callee words ∧
      valueLimit<base+words
  | .Exhausted .Allocation => SignatureAllocation allocator signature ∨
    (∃ words, SourceCanonicalFunctionCapacity store address words ∧
      ((∃ (slots : alloc.vec.Vec U64) (n : Usize), n.val≤words ∧ allocator.reserve slots n=.ok (false,slots)) ∨
        ∃ frames : alloc.vec.Vec runtime.interp.Frame, allocator.reserve frames 1#usize=.ok (false,frames))) ∨
    ∃ source, StepsH initial [] (Abs.decode source) ∧ SourceInvocationAllocation allocator source
  | .Exhausted .Objects => False
  | error => InvocationBoundaryCause hooks initial frameLimit error
end Itasca.Runtime.Theorems
