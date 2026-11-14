import Itasca.Runtime.Compiler.Local.Relations.Layout.LayoutProofs
import Itasca.Generated.FunsCompiler

/-! Executable-module view equations and syntactic certificates for synthetic
constant-expression functions. The certificate records emitted instructions
and embedded vector bits; source constant-expression typing and runtime
reference resolution are separate facts. -/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- The executable module exposes its retained validated environment. -/
theorem _root_.Itasca.runtime.compiler.ExecutableModule.env.eq
    (module : runtime.compiler.ExecutableModule) :
    runtime.compiler.ExecutableModule.env module = .ok module.module.env := by
  rfl

/-- The executable module exposes its retained validated tail. -/
theorem _root_.Itasca.runtime.compiler.ExecutableModule.tail.eq
    (module : runtime.compiler.ExecutableModule) :
    runtime.compiler.ExecutableModule.tail module = .ok module.module.tail := by
  rfl

@[step] theorem _root_.Itasca.runtime.compiler.ExecutableModule.env.spec
    (module : runtime.compiler.ExecutableModule) :
    runtime.compiler.ExecutableModule.env module ⦃ env => env = module.module.env ⦄ := by
  rw [runtime.compiler.ExecutableModule.env.eq]
  simp only [WP.spec_ok]

def initializerBits (lo hi : U64) : U128 :=
  ⟨(UScalar.cast .U128 lo).bv ||| ((UScalar.cast .U128 hi).bv <<< 64)⟩

inductive ConstantInstruction (function : runtime.bytecode.CompiledFunction)
    (dst : U32) : Itasca.wasm_types.ConstExpr → Itasca.wasm_types.ValueType → runtime.bytecode.Instr → Prop where
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
    (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType) (instruction : runtime.bytecode.Instr) :=
  ConstantInstruction function 0#u32 expr ty instruction

structure InitializerCode (function : runtime.bytecode.CompiledFunction)
    (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType) : Prop where
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

end Itasca.Runtime.Compiler
