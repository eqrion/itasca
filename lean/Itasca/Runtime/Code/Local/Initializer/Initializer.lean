import Itasca.Runtime.Code.Local.Relations.Common.LayoutProofs

/-! Syntactic certificates for synthetic constant-expression functions. The
certificate records emitted instructions and embedded vector bits; source
constant-expression typing and runtime reference resolution are separate facts. -/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

def initializerWidth : Itasca.types.ValueType → U32
  | .V128 => 2#u32
  | _ => 1#u32

theorem compiler_width_eq (ty : Itasca.types.ValueType) :
    runtime.value.width ty = .ok (initializerWidth ty) := by
  cases ty <;> rfl

def initializerBits (lo hi : U64) : U128 :=
  ⟨(UScalar.cast .U128 lo).bv ||| ((UScalar.cast .U128 hi).bv <<< 64)⟩

inductive ConstantInstruction (function : runtime.bytecode.CompiledFunction)
    (dst : U32) : Itasca.types.ConstExpr → Itasca.types.ValueType → runtime.bytecode.Instr → Prop where
  | i32 (value : I32) (ty) : ConstantInstruction function dst (.I32 value) ty
      (.Const32 dst (IScalar.hcast .U32 value))
  | i64 (value : I64) (ty) : ConstantInstruction function dst (.I64 value) ty
      (.Const64 dst (IScalar.hcast .U64 value))
  | f32 (bits : U32) (ty) : ConstantInstruction function dst (.F32 bits) ty (.Const32 dst bits)
  | f64 (bits : U64) (ty) : ConstantInstruction function dst (.F64 bits) ty (.Const64 dst bits)
  | v128 (lo hi : U64) (ty) (pool : U32)
      (embedded : function.v128_pool.val[pool.val]? = some (initializerBits lo hi)) :
      ConstantInstruction function dst (.V128 lo hi) ty (.ConstV128 dst pool)
  | refNull (ty) (elem) : ConstantInstruction function dst (.RefNull elem) ty (.RefNull dst)
  | refFunc (ty) (index) : ConstantInstruction function dst (.RefFunc index) ty (.RefFunc dst index)
  | global (ty) (index) (scalar : ty ≠ .V128) :
      ConstantInstruction function dst (.GlobalGet index) ty (.GlobalGet dst index)
  | globalVector (index) :
      ConstantInstruction function dst (.GlobalGet index) .V128 (.GlobalGet2 dst index)

abbrev InitialInstruction (function : runtime.bytecode.CompiledFunction)
    (expr : Itasca.types.ConstExpr) (ty : Itasca.types.ValueType) (instruction : runtime.bytecode.Instr) :=
  ConstantInstruction function 0#u32 expr ty instruction

structure InitializerCode (function : runtime.bytecode.CompiledFunction)
    (expr : Itasca.types.ConstExpr) (ty : Itasca.types.ValueType) : Prop where
  code : ∃ instruction, InitialInstruction function expr ty instruction ∧
    function.code.val = [instruction, .Return 0#u32 (initializerWidth ty)]
  capacity : function.slot_count = initializerWidth ty
  localSlots : function.local_slots = 0#u32
  paramSlots : function.param_slots = 0#u32
  locals : function.locals.val = []

theorem ConstantInstruction.change_code {before after : runtime.bytecode.CompiledFunction}
    {dst expr ty instruction} (h : ConstantInstruction before dst expr ty instruction)
    (pool : after.v128_pool = before.v128_pool) : ConstantInstruction after dst expr ty instruction := by
  cases h <;> constructor <;> simp_all [pool]

end Itasca.Runtime.Code
