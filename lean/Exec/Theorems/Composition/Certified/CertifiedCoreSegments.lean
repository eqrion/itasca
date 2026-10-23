import Exec.Theorems.Composition.Certified.CertifiedCore
import Exec.Store.Initialization.SegmentExtension
import Exec.Store.Invariant.SourceSyntax
import Exec.Store.Invariant.SourceCore
import Exec.Store.Invariant.CoreFunctionTables
import Exec.Store.Invariant.CoreTypingExtension
import Exec.Store.Initialization.SegmentInitializeMetadata
import Exec.Store.Initialization.SegmentInitializeShape
namespace Exec.Theorems
open Aeneas Aeneas.Std

/-- Segment writes and drops preserve the complete static integer-slice
certificate, including the source typing of every existing function. -/
theorem CertifiedCoreStore.segments {M : Type} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {before after : runtime.store.Store M}
    (certified : CertifiedCoreStore view code before)
    (metadata : Store.SegmentObjectMetadata view before after) (shape : Store.Shape view after) :
    CertifiedCoreStore view code after ∧
      Extend_store (Store.decodeStore view code before) (Store.decodeStore view code after) := by
  have syntaxAfter := certified.storeSyntax.instances_eq metadata.space.instances
  have extension := metadata.extends code
    (Store.decodeStore_wf view code before certified.shape certified.storeSyntax)
    (Store.decodeStore_wf view code after shape syntaxAfter)
  exact ⟨⟨shape, syntaxAfter, Store.core_functions_typed_metadata metadata.space.functions metadata.space.signatures metadata.space.instances extension certified.typed,
    metadata.space.core view code certified.core, Store.core_compiled_functions_metadata code metadata.space.identity metadata.space.functions metadata.space.signatures metadata.space.instances certified.compiled,
    metadata.segment_bounds certified.segmentBounds⟩, extension⟩

/-- Actual initialization of a successfully compiled module preserves all slice
certificates and extends the decoded store on every normal outcome, including
traps after earlier writes. -/
theorem initialize_segments_certified_core {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex : Usize)
    (inst : runtime.store.ModuleInst) (bytes : Slice U8) (profile : Itasca.ValidationProfile)
    (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok inst.module))
    (found : store.instances.val[instIndex.val]? = some inst)
    (code : Store.CodeInterpretation) (certified : CertifiedCoreStore view code store)
    (imports : Store.InitializerImports store inst) (bindings : Store.InitializerBindings store inst)
    (types : Store.SegmentTypeBindings store inst) :
    runtime.interp.initialize_segments memory hooks floats allocator store platform instIndex
      ⦃ out => CertifiedCoreStore view code out.2.1 ∧
        Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.1) ∧
        Store.SegmentObjectMetadata view store out.2.1 ∧ out.2.2 = platform ⦄ := by
  have shaped := Store.initialize_segments_compiled_shape memory hooks floats allocator view laws law
    store platform instIndex inst bytes profile limits accepted found certified.shape imports bindings types
  have normal := Store.initialize_segments_compiled memory hooks floats allocator view laws law
    store platform instIndex inst bytes profile limits accepted found
    (certified.shape.instances inst (List.mem_of_getElem? found)) imports bindings
  obtain ⟨out, run, metadata⟩ := WP.spec_imp_exists
    (Store.initialize_segments_compiled_object_metadata memory hooks floats allocator view laws law
      store platform instIndex inst bytes profile limits accepted found certified.shape imports bindings)
  rw [run, WP.spec_ok] at shaped normal ⊢
  have retained := certified.segments metadata shaped.1
  exact ⟨retained.1, retained.2, metadata, normal.2⟩
end Exec.Theorems
