import Itasca.Generated.FunsCompiler

/-! Exact equations for callbacks that only marshal operands into the opcode
dispatcher. Consumer proofs share these equations with no allocator premise. -/

namespace Itasca
open Aeneas Aeneas.Std

theorem runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_call.eq
  {A : Type} (platformAllocInst : runtime.platform.Alloc A)
  (self : runtime.compiler.FunctionCompiler A) (st : code.OpIterState)
  (index : Std.U32) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_call platformAllocInst self st index =
    (do
      runtime.compiler.lower.FunctionCompiler.op platformAllocInst self st 16#u16
        index 0#u32 0#u128) := rfl

theorem runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_get.eq
  {A : Type} (platformAllocInst : runtime.platform.Alloc A)
  (self : runtime.compiler.FunctionCompiler A) (st : code.OpIterState)
  (index : Std.U32) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_get platformAllocInst self st index =
    (do
      runtime.compiler.lower.FunctionCompiler.op platformAllocInst self st 32#u16
        index 0#u32 0#u128) := rfl

theorem runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_set.eq
  {A : Type} (platformAllocInst : runtime.platform.Alloc A)
  (self : runtime.compiler.FunctionCompiler A) (st : code.OpIterState)
  (index : Std.U32) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_set platformAllocInst self st index =
    (do
      runtime.compiler.lower.FunctionCompiler.op platformAllocInst self st 33#u16
        index 0#u32 0#u128) := rfl

theorem runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_tee.eq
  {A : Type} (platformAllocInst : runtime.platform.Alloc A)
  (self : runtime.compiler.FunctionCompiler A) (st : code.OpIterState)
  (index : Std.U32) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_local_tee platformAllocInst self st index =
    (do
      runtime.compiler.lower.FunctionCompiler.op platformAllocInst self st 34#u16
        index 0#u32 0#u128) := rfl

theorem runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_const.eq
  {A : Type} (platformAllocInst : runtime.platform.Alloc A)
  (self : runtime.compiler.FunctionCompiler A) (st : code.OpIterState)
  (v : Std.I32) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_const platformAllocInst self st v =
    (do
      let i ← lift (IScalar.hcast .U32 v)
      let i1 ← lift (UScalar.cast .U128 i)
      runtime.compiler.lower.FunctionCompiler.op platformAllocInst self st 65#u16
        0#u32 0#u32 i1) := rfl

theorem runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_const.eq
  {A : Type} (platformAllocInst : runtime.platform.Alloc A)
  (self : runtime.compiler.FunctionCompiler A) (st : code.OpIterState)
  (v : Std.I64) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_const platformAllocInst self st v =
    (do
      let i ← lift (IScalar.hcast .U64 v)
      let i1 ← lift (UScalar.cast .U128 i)
      runtime.compiler.lower.FunctionCompiler.op platformAllocInst self st 66#u16
        0#u32 0#u32 i1) := rfl

theorem runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f32_const.eq
  {A : Type} (platformAllocInst : runtime.platform.Alloc A)
  (self : runtime.compiler.FunctionCompiler A) (st : code.OpIterState)
  (bits : Std.U32) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f32_const platformAllocInst self st bits =
    (do
      let i ← lift (UScalar.cast .U128 bits)
      runtime.compiler.lower.FunctionCompiler.op platformAllocInst self st 67#u16
        0#u32 0#u32 i) := rfl

theorem runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f64_const.eq
  {A : Type} (platformAllocInst : runtime.platform.Alloc A)
  (self : runtime.compiler.FunctionCompiler A) (st : code.OpIterState)
  (bits : Std.U64) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f64_const platformAllocInst self st bits =
    (do
      let i ← lift (UScalar.cast .U128 bits)
      runtime.compiler.lower.FunctionCompiler.op platformAllocInst self st 68#u16
        0#u32 0#u32 i) := rfl

theorem runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_ref_null.eq
  {A : Type} (platformAllocInst : runtime.platform.Alloc A)
  (self : runtime.compiler.FunctionCompiler A) (st : code.OpIterState)
  (ty : wasm_types.ElemType) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_ref_null platformAllocInst self st ty =
    (do
      let b ←
        match ty with
        | wasm_types.ElemType.FuncRef => .ok true
        | wasm_types.ElemType.ExternRef => .ok false
      let reference_type ← if b then .ok 0#u32 else .ok 1#u32
      runtime.compiler.lower.FunctionCompiler.op platformAllocInst self st 208#u16
        reference_type 0#u32 0#u128) := rfl

theorem runtime.compiler.visitor_result.eq
  (result : core.result.Result Unit error.VisitError) :
    runtime.compiler.visitor_result result = (do
      match result with
      | .Ok _ => .ok (core.result.Result.Ok ())
      | .Err err => .ok (core.result.Result.Err (error.Error.Visitor err))) := rfl

/-- Projection equation for the `on_drop` callback on the compiler visitor. -/
theorem runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.project_on_drop.eq {A : Type}
    (platformAllocInst : runtime.platform.Alloc A) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor platformAllocInst).on_drop =
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_drop platformAllocInst := rfl

/-- Projection equation for the `on_f32_const` callback on the compiler visitor. -/
theorem runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.project_on_f32_const.eq {A : Type}
    (platformAllocInst : runtime.platform.Alloc A) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor platformAllocInst).on_f32_const =
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f32_const platformAllocInst := rfl

/-- Projection equation for the `on_f64_const` callback on the compiler visitor. -/
theorem runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.project_on_f64_const.eq {A : Type}
    (platformAllocInst : runtime.platform.Alloc A) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor platformAllocInst).on_f64_const =
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f64_const platformAllocInst := rfl

/-- Projection equation for the `on_global_get` callback on the compiler visitor. -/
theorem runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.project_on_global_get.eq {A : Type}
    (platformAllocInst : runtime.platform.Alloc A) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor platformAllocInst).on_global_get =
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_global_get platformAllocInst := rfl

/-- Projection equation for the `on_global_set` callback on the compiler visitor. -/
theorem runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.project_on_global_set.eq {A : Type}
    (platformAllocInst : runtime.platform.Alloc A) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor platformAllocInst).on_global_set =
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_global_set platformAllocInst := rfl

/-- Projection equation for the `on_i32_const` callback on the compiler visitor. -/
theorem runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.project_on_i32_const.eq {A : Type}
    (platformAllocInst : runtime.platform.Alloc A) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor platformAllocInst).on_i32_const =
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_const platformAllocInst := rfl

/-- Projection equation for the `on_i64_const` callback on the compiler visitor. -/
theorem runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.project_on_i64_const.eq {A : Type}
    (platformAllocInst : runtime.platform.Alloc A) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor platformAllocInst).on_i64_const =
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_const platformAllocInst := rfl

/-- Projection equation for the `on_nop` callback on the compiler visitor. -/
theorem runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.project_on_nop.eq {A : Type}
    (platformAllocInst : runtime.platform.Alloc A) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor platformAllocInst).on_nop =
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_nop platformAllocInst := rfl

/-- Projection equation for the `on_ref_null` callback on the compiler visitor. -/
theorem runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.project_on_ref_null.eq {A : Type}
    (platformAllocInst : runtime.platform.Alloc A) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor platformAllocInst).on_ref_null =
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_ref_null platformAllocInst := rfl

/-- Projection equation for the `on_select` callback on the compiler visitor. -/
theorem runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.project_on_select.eq {A : Type}
    (platformAllocInst : runtime.platform.Alloc A) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor platformAllocInst).on_select =
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_select platformAllocInst := rfl

/-- Projection equation for the `on_simd` callback on the compiler visitor. -/
theorem runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.project_on_simd.eq {A : Type}
    (platformAllocInst : runtime.platform.Alloc A) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor platformAllocInst).on_simd =
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_simd platformAllocInst := rfl

/-- Projection equation for the `on_simd_const` callback on the compiler visitor. -/
theorem runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.project_on_simd_const.eq {A : Type}
    (platformAllocInst : runtime.platform.Alloc A) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor platformAllocInst).on_simd_const =
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_simd_const platformAllocInst := rfl

/-- Projection equation for the `on_simd_lane` callback on the compiler visitor. -/
theorem runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.project_on_simd_lane.eq {A : Type}
    (platformAllocInst : runtime.platform.Alloc A) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor platformAllocInst).on_simd_lane =
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_simd_lane platformAllocInst := rfl

/-- Projection equation for the `on_simd_memory` callback on the compiler visitor. -/
theorem runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.project_on_simd_memory.eq {A : Type}
    (platformAllocInst : runtime.platform.Alloc A) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor platformAllocInst).on_simd_memory =
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_simd_memory platformAllocInst := rfl

/-- Projection equation for the `on_simd_memory_lane` callback on the compiler visitor. -/
theorem runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.project_on_simd_memory_lane.eq {A : Type}
    (platformAllocInst : runtime.platform.Alloc A) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor platformAllocInst).on_simd_memory_lane =
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_simd_memory_lane platformAllocInst := rfl

/-- Projection equation for the `on_simd_shuffle` callback on the compiler visitor. -/
theorem runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.project_on_simd_shuffle.eq {A : Type}
    (platformAllocInst : runtime.platform.Alloc A) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor platformAllocInst).on_simd_shuffle =
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_simd_shuffle platformAllocInst := rfl

/-- Projection equation for `metadataModuleVisitorInst` on the streaming visitor. -/
theorem runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.project_metadataModuleVisitorInst.eq {A : Type}
    (platformAllocInst : runtime.platform.Alloc A) :
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor platformAllocInst).metadataModuleVisitorInst =
      runtime.compiler.CompileScheduler.Insts.ItascaMetadataModuleVisitor platformAllocInst := rfl

/-- Projection equation for `code_end` on the streaming visitor. -/
theorem runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.project_code_end.eq {A : Type}
    (platformAllocInst : runtime.platform.Alloc A) :
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor platformAllocInst).code_end =
      runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.code_end platformAllocInst := rfl

/-- Projection equation for `tail_ready` on the streaming visitor. -/
theorem runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.project_tail_ready.eq {A : Type}
    (platformAllocInst : runtime.platform.Alloc A) :
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor platformAllocInst).tail_ready =
      runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.tail_ready platformAllocInst := rfl


/-- Projection equation for `custom_region` on the streaming visitor. -/
theorem runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.project_custom_region.eq {A : Type}
    (platformAllocInst : runtime.platform.Alloc A) :
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor platformAllocInst).custom_region =
      runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.custom_region platformAllocInst := rfl

/-- Projection equation for `on_custom_section` on the metadata visitor. -/
theorem runtime.compiler.CompileScheduler.Insts.ItascaMetadataModuleVisitor.project_on_custom_section.eq {A : Type}
    (platformAllocInst : runtime.platform.Alloc A) :
    (runtime.compiler.CompileScheduler.Insts.ItascaMetadataModuleVisitor platformAllocInst).on_custom_section =
      runtime.compiler.CompileScheduler.Insts.ItascaMetadataModuleVisitor.on_custom_section platformAllocInst := rfl

/-- The `tail_ready` callback records the supplied tail and succeeds. -/
theorem runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.tail_ready.eq {A : Type}
    (platformAllocInst : runtime.platform.Alloc A)
    (self : runtime.compiler.CompileScheduler A) (tail : metadata.Tail) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.tail_ready platformAllocInst self tail =
      .ok (.Ok (), {self with tail := some tail}) := rfl

/-- The `code_end` callback succeeds without changing the scheduler. -/
theorem runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.code_end.eq {A : Type}
    (platformAllocInst : runtime.platform.Alloc A)
    (self : runtime.compiler.CompileScheduler A) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.code_end platformAllocInst self =
      .ok (.Ok (), self) := rfl

/-- The `custom_region` callback succeeds without changing the scheduler. -/
theorem runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.custom_region.eq {A : Type}
    (platformAllocInst : runtime.platform.Alloc A)
    (self : runtime.compiler.CompileScheduler A) (region : stream.Region) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.custom_region platformAllocInst self region =
      .ok self := rfl

/-- The metadata `on_custom_section` callback succeeds without changing the scheduler. -/
theorem runtime.compiler.CompileScheduler.Insts.ItascaMetadataModuleVisitor.on_custom_section.eq {A : Type}
    (platformAllocInst : runtime.platform.Alloc A)
    (self : runtime.compiler.CompileScheduler A) (customSection : wasm_types.CustomSection) :
    runtime.compiler.CompileScheduler.Insts.ItascaMetadataModuleVisitor.on_custom_section platformAllocInst self customSection =
      .ok (.Ok (), self) := rfl

/-- Polling delegates to the queue pop and only replaces the completed queue. -/
theorem runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.poll_code_batch.eq {A : Type}
    (ops : runtime.platform.Alloc A) (self : runtime.compiler.CompileScheduler A) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.poll_code_batch ops self = (do
      let (entry, completed) ← alloc.vec.Vec.pop Global self.completed
      let result ← core.option.Option.ok_or entry error.Error.Host
      .ok (result, {self with completed})) := rfl

end Itasca
