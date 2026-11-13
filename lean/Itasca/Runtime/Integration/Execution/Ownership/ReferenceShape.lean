import Itasca.Runtime.Integration.Execution.Mutation.BulkResult
import Itasca.Runtime.Interp.Machine.Functions.CompiledFunctions
import Itasca.Runtime.SourceMachine.BrTable
import Itasca.Runtime.Representation.Values
import Itasca.Runtime.Store.Invariant.CodeAgreement
import Itasca.Runtime.Interp.Relations.FrameStoreMetadata
import Itasca.Runtime.Compiler.Local.Control.Function.CumulativeFunctionContext
import Itasca.Runtime.Store.Invariant.ErrorPost
import Itasca.Runtime.Store.Initialization.SegmentExtension
import Itasca.Runtime.Store.Invariant.OwnedInitializerErrors
import Itasca.Runtime.SourceMachine.Measure
import Itasca.Runtime.SourceMachine.Float.Results
import Itasca.Runtime.SourceMachine.Stateful.Signature
import Itasca.Module.Soundness
import Itasca.Profile.BinaryUnique
import Itasca.Runtime.Compiler.Local.Source.SourceSegmentPrograms
import Itasca.Runtime.Store.Invariant.PrecommitError
import Itasca.Runtime.Store.Initialization.SegmentInitializePreservation
import Itasca.Runtime.Interp.Relations.StackPreservation
import Itasca.Runtime.Store.Invariant.FunctionStaging
import Itasca.Runtime.Integration.Execution.Ownership.Publication

/-!
Sections, each formerly its own module: CertifiedStore, CodeInterpretation, SegmentInitialization, FrameTypeBounds, ReferenceShape.
-/

/-! ## CertifiedStore -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std

/-- Common static store certificate indexed by source syntax and concrete
function emission. Execution semantics remain separate checked theorems. -/
structure CertifiedSupportedStore
 {M : Type} (view : M → Slice U8)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M) : Prop where
  shape : Store.Shape view store
  storeSyntax : Store.StoreSyntax code store
  typed : Interp.CoreFunctionsTyped view code store
  supported : SourceMachine.FunctionsSupported (Store.decodeStore view code store)
  compiled : Interp.Machine.CompiledFunctions code store
  segmentBounds : Store.SegmentBounds store

theorem CertifiedSupportedStore.functions_typed {M view code store}
    (certified : @CertifiedSupportedStore M view code store) :
    SourceMachine.FunctionsTyped (Store.decodeStore view code store) := certified.typed.functions_typed

theorem CertifiedSupportedStore.contents_typed {M view code store}
    (certified : @CertifiedSupportedStore M view code store) :
    SourceMachine.StoreContentsTyped (Store.decodeStore view code store) :=
  Store.decode_store_contents_typed view code store certified.shape certified.storeSyntax certified.segmentBounds

/-- Exact checked mutation footprints preserve the common static certificate,
including operations that drop segments or grow mutable objects. -/
theorem CertifiedSupportedStore.update {M view code before after}
    (certified : @CertifiedSupportedStore M view code before)
    (mutation : CumulativeStoreMutation view code before after) :
    CertifiedSupportedStore view code after := by
  have syntaxAfter : Store.StoreSyntax code after := by
    simpa only [Store.StoreSyntax,mutation.metadata.instances] using certified.storeSyntax
  have decodedFunctions : (Store.decodeStore view code after).FUNCS =
      (Store.decodeStore view code before).FUNCS := by
    have decodeFunction : Store.decodeFunction code after = Store.decodeFunction code before := by
      funext function
      simp only [Store.decodeFunction,Store.decodeInstance,mutation.metadata.types,mutation.metadata.instances]
    simp only [Store.decodeStore,mutation.metadata.functions,decodeFunction]
  refine ⟨mutation.shape,syntaxAfter,
    Store.core_functions_typed_metadata mutation.metadata.functions mutation.metadata.types mutation.metadata.instances
      mutation.extension certified.typed,certified.supported.same decodedFunctions,?_,mutation.segmentBounds⟩
  simpa only [Interp.Machine.CompiledFunctions,Interp.Machine.FunctionCompiled,Interp.FunctionTable,
    Store.decodeInstance,mutation.metadata.identity,mutation.metadata.functions,mutation.metadata.types,
    mutation.metadata.instances] using certified.compiled

end Itasca.Runtime.Integration

end

/-! ## CodeInterpretation -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std

/-- Reassigning ghost source code at unused instance keys preserves the full
static store certificate. Actual installed functions keep their exact source. -/
theorem CertifiedSupportedStore.change_code {M : Type} {view : M → Slice U8}
    {before after : Store.CodeInterpretation} {store : runtime.store.Store M}
    (certified : CertifiedSupportedStore view before store)
    (agrees : Store.CodeAgreesOn store before after) : CertifiedSupportedStore view after store := by
  refine ⟨certified.shape, ?_, ?_, ?_, ?compiled, certified.segmentBounds⟩
  · intro index inst found
    have priorSyntax := certified.storeSyntax index inst found
    refine ⟨priorSyntax.exportNames, ?_⟩
    intro function bound
    rw [agrees index inst found function]
    exact priorSyntax.functionCodes function bound
  · exact Store.core_functions_typed_code_agrees agrees certified.typed
  · rw [Store.decode_store_code_agrees view agrees]
    exact certified.supported
  case compiled =>
    intro function present instanceIndex functionIndex defined
    obtain ⟨inst,code,signature,declared,body,epilogue,found,functionFound,signatureFound,source,table,types,certificate⟩ :=
      certified.compiled function present instanceIndex functionIndex defined
    exact ⟨inst,code,signature,declared,body,epilogue,found,functionFound,signatureFound,
      (agrees instanceIndex.val inst found functionIndex.val).trans source,table,types,certificate⟩

end Itasca.Runtime.Integration

end

/-! ## SegmentInitialization -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std

/-- Segment writes and drops preserve the complete static cumulative
certificate, including the source typing of every existing function. -/
theorem CertifiedSupportedStore.segments {M : Type} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {before after : runtime.store.Store M}
    (certified : CertifiedSupportedStore view code before)
    (metadata : Store.SegmentObjectMetadata view before after) (shape : Store.Shape view after) :
    CertifiedSupportedStore view code after ∧
      Extend_store (Store.decodeStore view code before) (Store.decodeStore view code after) := by
  have syntaxAfter := certified.storeSyntax.instances_eq metadata.space.instances
  have extension := metadata.extends code
    (Store.decode_store_wf view code before certified.shape certified.storeSyntax)
    (Store.decode_store_wf view code after shape syntaxAfter)
  refine ⟨⟨shape, syntaxAfter, Store.core_functions_typed_metadata metadata.space.functions metadata.space.signatures metadata.space.instances extension certified.typed,
    ?supported, ?compiled,
    metadata.segment_bounds certified.segmentBounds⟩, extension⟩
  case supported =>
    apply certified.supported.same
    simp only [Store.decodeStore,metadata.space.functions]
    congr 1
    funext function
    simp only [Store.decodeFunction,Store.decodeInstance,metadata.space.signatures,metadata.space.instances]
  case compiled =>
    simpa only [Interp.Machine.CompiledFunctions,Interp.Machine.FunctionCompiled,
      Interp.FunctionTable,Store.decodeInstance,metadata.space.identity,metadata.space.functions,
      metadata.space.signatures,metadata.space.instances] using certified.compiled

/-- Actual initialization of a successfully compiled module preserves all cumulative
certificates and extends the decoded store on every normal outcome, including
traps after earlier writes. -/
theorem initialize_segments_certified_supported {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex : Usize)
    (inst : runtime.store.ModuleInst) (bytes : Slice U8)
    (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes limits = .ok (.Ok inst.module))
    (found : store.instances.val[instIndex.val]? = some inst)
    (code : Store.CodeInterpretation) (certified : CertifiedSupportedStore view code store)
    (imports : Store.InitializerImports store inst) (bindings : Store.InitializerBindings store inst)
    (types : Store.SegmentTypeBindings store inst) :
    runtime.interp.initialize_segments memory hooks floats allocator store platform instIndex
      ⦃ out => CertifiedSupportedStore view code out.2.1 ∧
        Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.1) ∧
        Store.SegmentObjectMetadata view store out.2.1 ∧ out.2.2 = platform ⦄ := by
  have shaped := Store.initialize_segments_compiled_shape memory hooks floats allocator view laws law
    store platform instIndex inst bytes limits accepted found certified.shape imports bindings types
  have normal := Store.initialize_segments_compiled memory hooks floats allocator view laws law
    store platform instIndex inst bytes limits accepted found
    (certified.shape.instances inst (List.mem_of_getElem? found)) imports bindings
  obtain ⟨out, run, metadata⟩ := WP.spec_imp_exists
    (Store.initialize_segments_compiled_object_metadata memory hooks floats allocator view laws law
      store platform instIndex inst bytes limits accepted found certified.shape imports bindings)
  rw [run, WP.spec_ok] at shaped normal ⊢
  have retained := certified.segments metadata shaped.1
  exact ⟨retained.1, retained.2, metadata, normal.2⟩
end Itasca.Runtime.Integration

end

/-! ## FrameTypeBounds -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem frame_type_bounds_of_shape {M : Type} {view : M → Slice U8}
    {store : runtime.store.Store M} (shape : Store.Shape view store) : FrameTypeBounds store := by
  intro inst member index present
  exact (shape.instances inst member).2.2.2.2.2.2.2.1 index present

end Itasca.Runtime.Interp

end

/-! ## ReferenceShape -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Per-kind source ownership of the exact decoded operand establishes the
runtime table reference invariant, including its full-width address word. -/
theorem owned_reference_shape {M : Type} (store : runtime.store.Store M)
    (type : Itasca.wasm_types.ElemType) (word : U64)
    (owned : SourceMachine.Ownership.ValueOwned (ownershipBounds store) (val_ref (decodeRef type word))) :
    ReferenceShape store type word := by
  cases type <;> unfold ReferenceShape
  all_goals
    by_cases zero : word.val = 0
    · exact Or.inl zero
    · exact Or.inr (by simpa only [decodeRef,if_neg zero,val_ref,SourceMachine.Ownership.ValueOwned,ownershipBounds] using owned)
end Itasca.Runtime.Store

end
