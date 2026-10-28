import Itasca.Runtime.Code.Local.Publication.ScalarMapPublication
import Itasca.Visitor.Events

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-- Ordinary scalar visitor forms; numeric, memory, SIMD and control events
have their own argument-indexed publication adapters. -/
inductive ScalarPublicationAction : Action → Prop where
  | nop  : ScalarPublicationAction (.nop )
  | call (index : U32) : ScalarPublicationAction (.call index)
  | call_indirect (ty table : U32) : ScalarPublicationAction (.call_indirect ty table)
  | drop (ty : code.StackType) : ScalarPublicationAction (.drop ty)
  | select (ty : code.StackType) : ScalarPublicationAction (.select ty)
  | select_typed (ty : types.ValueType) : ScalarPublicationAction (.select_typed ty)
  | local_get (index : U32) : ScalarPublicationAction (.local_get index)
  | local_set (index : U32) : ScalarPublicationAction (.local_set index)
  | local_tee (index : U32) : ScalarPublicationAction (.local_tee index)
  | global_get (index : U32) : ScalarPublicationAction (.global_get index)
  | global_set (index : U32) : ScalarPublicationAction (.global_set index)
  | table_get (index : U32) : ScalarPublicationAction (.table_get index)
  | table_set (index : U32) : ScalarPublicationAction (.table_set index)
  | ref_func (index : U32) : ScalarPublicationAction (.ref_func index)
  | memory_init (index : U32) : ScalarPublicationAction (.memory_init index)
  | data_drop (index : U32) : ScalarPublicationAction (.data_drop index)
  | elem_drop (index : U32) : ScalarPublicationAction (.elem_drop index)
  | table_grow (index : U32) : ScalarPublicationAction (.table_grow index)
  | table_size (index : U32) : ScalarPublicationAction (.table_size index)
  | table_fill (index : U32) : ScalarPublicationAction (.table_fill index)
  | memory_size  : ScalarPublicationAction (.memory_size )
  | memory_grow  : ScalarPublicationAction (.memory_grow )
  | ref_is_null  : ScalarPublicationAction (.ref_is_null )
  | memory_copy  : ScalarPublicationAction (.memory_copy )
  | memory_fill  : ScalarPublicationAction (.memory_fill )
  | i32_const (value : I32) : ScalarPublicationAction (.i32_const value)
  | i64_const (value : I64) : ScalarPublicationAction (.i64_const value)
  | f32_const (value : U32) : ScalarPublicationAction (.f32_const value)
  | f64_const (value : U64) : ScalarPublicationAction (.f64_const value)
  | table_init (first second : U32) : ScalarPublicationAction (.table_init first second)
  | table_copy (first second : U32) : ScalarPublicationAction (.table_copy first second)
  | ref_null (ty : types.ElemType) : ScalarPublicationAction (.ref_null ty)

/-- Scalar event dispatch preserves every immediate, including signed and
floating-point constant bits and both table instruction indices. -/
theorem scalar_hook_publication_dispatch {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : code.OpIterState)
    {action : Action} (supported : ScalarPublicationAction action) :
    ∃ (opcode : U16) (a b : U32) (bits : U128), opcode ∈ sourceCoordinateScalarOpcodes ∧
      invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler (.op state action) =
        runtime.compiler.lower.FunctionCompiler.op ops compiler state opcode a b bits := by
  cases supported with
  | nop  =>
    exact ⟨1#u16,0#u32,0#u32,0#u128,by decide,rfl⟩
  | call index =>
    exact ⟨16#u16,index,0#u32,0#u128,by decide,rfl⟩
  | call_indirect ty table =>
    exact ⟨17#u16,ty,table,0#u128,by decide,rfl⟩
  | drop ty =>
    exact ⟨26#u16,0#u32,0#u32,0#u128,by decide,rfl⟩
  | select ty =>
    exact ⟨27#u16,0#u32,0#u32,0#u128,by decide,rfl⟩
  | select_typed ty =>
    exact ⟨28#u16,0#u32,0#u32,0#u128,by decide,rfl⟩
  | local_get index =>
    exact ⟨32#u16,index,0#u32,0#u128,by decide,rfl⟩
  | local_set index =>
    exact ⟨33#u16,index,0#u32,0#u128,by decide,rfl⟩
  | local_tee index =>
    exact ⟨34#u16,index,0#u32,0#u128,by decide,rfl⟩
  | global_get index =>
    exact ⟨35#u16,index,0#u32,0#u128,by decide,rfl⟩
  | global_set index =>
    exact ⟨36#u16,index,0#u32,0#u128,by decide,rfl⟩
  | table_get index =>
    exact ⟨37#u16,index,0#u32,0#u128,by decide,rfl⟩
  | table_set index =>
    exact ⟨38#u16,index,0#u32,0#u128,by decide,rfl⟩
  | ref_func index =>
    exact ⟨210#u16,index,0#u32,0#u128,by decide,rfl⟩
  | memory_init index =>
    exact ⟨264#u16,index,0#u32,0#u128,by decide,rfl⟩
  | data_drop index =>
    exact ⟨265#u16,index,0#u32,0#u128,by decide,rfl⟩
  | elem_drop index =>
    exact ⟨269#u16,index,0#u32,0#u128,by decide,rfl⟩
  | table_grow index =>
    exact ⟨271#u16,index,0#u32,0#u128,by decide,rfl⟩
  | table_size index =>
    exact ⟨272#u16,index,0#u32,0#u128,by decide,rfl⟩
  | table_fill index =>
    exact ⟨273#u16,index,0#u32,0#u128,by decide,rfl⟩
  | memory_size  =>
    exact ⟨63#u16,0#u32,0#u32,0#u128,by decide,rfl⟩
  | memory_grow  =>
    exact ⟨64#u16,0#u32,0#u32,0#u128,by decide,rfl⟩
  | ref_is_null  =>
    exact ⟨209#u16,0#u32,0#u32,0#u128,by decide,rfl⟩
  | memory_copy  =>
    exact ⟨266#u16,0#u32,0#u32,0#u128,by decide,rfl⟩
  | memory_fill  =>
    exact ⟨267#u16,0#u32,0#u32,0#u128,by decide,rfl⟩
  | i32_const value =>
    exact ⟨65#u16,0#u32,0#u32,UScalar.cast .U128 (IScalar.hcast .U32 value),by decide,by simp only [invoke,runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor,
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_const,lift,bind_ok]⟩
  | i64_const value =>
    exact ⟨66#u16,0#u32,0#u32,UScalar.cast .U128 (IScalar.hcast .U64 value),by decide,by simp only [invoke,runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor,
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_const,lift,bind_ok]⟩
  | f32_const value =>
    exact ⟨67#u16,0#u32,0#u32,UScalar.cast .U128 value,by decide,by simp only [invoke,runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor,
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f32_const,lift,bind_ok]⟩
  | f64_const value =>
    exact ⟨68#u16,0#u32,0#u32,UScalar.cast .U128 value,by decide,by simp only [invoke,runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor,
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f64_const,lift,bind_ok]⟩
  | table_init first second =>
    exact ⟨268#u16,first,second,0#u128,by decide,rfl⟩
  | table_copy first second =>
    exact ⟨270#u16,first,second,0#u128,by decide,rfl⟩
  | ref_null ty =>
    cases ty
    · exact ⟨208#u16,0#u32,0#u32,0#u128,by decide,by simp only [invoke,runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor,
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_ref_null,bind_ok,ite_true]⟩
    · exact ⟨208#u16,1#u32,0#u32,0#u128,by decide,by simp only [invoke,runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor,
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_ref_null,bind_ok,Bool.false_eq_true,ite_false]⟩

/-- Every actual ordinary scalar event retains both publication invariants. -/
theorem compiler_scalar_hook_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : code.OpIterState) {action : Action} (supported : ScalarPublicationAction action)
    (coordinates : SourceCoordinates before) (maps : ControlMapPublication before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before (.op state action) =
      .ok (.Ok (),after)) : SourceCoordinates after ∧ ControlMapPublication after := by
  obtain ⟨opcode,a,b,bits,member,dispatch⟩ := scalar_hook_publication_dispatch ops before state supported
  rw [dispatch] at called
  exact ⟨compiler_scalar_source_coordinates ops law before after state opcode a b bits member
      coordinates inside forward called,
    compiler_scalar_op_map_publication ops law before after state opcode a b bits member maps forward called⟩

end Itasca.Runtime.Code
