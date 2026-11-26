import Itasca.Runtime.Compiler.Local.Definitions
import Itasca.Runtime.Compiler.Local.Relations.Layout.LayoutProofs
import Itasca.Generated.Funs

/-! Executable-module view equations and syntactic certificates for synthetic
constant-expression functions. The certificate records emitted instructions
and embedded vector bits; source constant-expression typing and runtime
reference resolution are separate facts. -/

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Exact initial compiler state before parameters and locals are registered. -/
theorem _root_.Itasca.runtime.compiler.FunctionCompiler.new.eq
  {A : Type} (platformAllocInst : runtime.platform.Alloc A)
  (signatures : Slice runtime.compiler.Signature)
  (func_param_slots : Slice Std.U32) (budget : runtime.compiler.Budget A)
  (batch_start : Std.Usize) :
    runtime.compiler.FunctionCompiler.new platformAllocInst signatures func_param_slots budget batch_start =
    .ok
    {
      signatures,
      func_param_slots,
      budget,
      batch_start,
      function :=
        {
          locals := (alloc.vec.Vec.new wasm_types.ValueType),
          local_slots := 0#u32,
          param_slots := 0#u32,
          slot_count := 0#u32,
          max_stack := 0#usize,
          code := (alloc.vec.Vec.new runtime.bytecode.Instr),
          jump_tables := (alloc.vec.Vec.new Std.U32),
          v128_pool := (alloc.vec.Vec.new Std.U128),
          indirect := (alloc.vec.Vec.new (Std.U32 × Std.U32)),
          simd := (alloc.vec.Vec.new runtime.bytecode.SimdImmediate),
          source_offsets := (alloc.vec.Vec.new Std.Usize),
          controls := (alloc.vec.Vec.new runtime.compiler.ControlMap),
          type_index := 0#u32,
          body_start := 0#usize,
          body_end := 0#usize
        },
      frames := (alloc.vec.Vec.new runtime.compiler.Frame),
      reachable := true,
      next_source := 0#usize,
      before := (alloc.vec.Vec.new Std.U32),
      height := 0#u32,
      local_offsets := (alloc.vec.Vec.new Std.U32),
      table_depths := (alloc.vec.Vec.new Std.U32)
    } := rfl

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

theorem ConstantInstruction.change_code {before after : runtime.bytecode.CompiledFunction}
    {dst expr ty instruction} (h : ConstantInstruction before dst expr ty instruction)
    (pool : after.v128_pool = before.v128_pool) : ConstantInstruction after dst expr ty instruction := by
  cases h <;> constructor <;> simp_all [pool]

end Itasca.Compiler

namespace Itasca.Compiler
open Aeneas Aeneas.Std

theorem initializer_slice_index {T : Type} (values : Slice T) (index : Usize) (value : T)
    (found : values.val[index.val]? = some value) : Slice.index_usize values index = .ok value := by
  have bound : index.val < values.length := (List.getElem?_eq_some_iff.mp found).1
  have spec : Slice.index_usize values index ⦃ out => out = value ⦄ := by
    step as ⟨out, hout⟩
    have read := List.getElem?_eq_getElem bound
    rw [found] at read
    exact hout.trans (Option.some.inj read).symm
  obtain ⟨out, call, rfl⟩ := WP.spec_imp_exists spec
  exact call

theorem initializer_vec_index {T : Type} (values : alloc.vec.Vec T) (index : Usize) (value : T)
    (found : values.val[index.val]? = some value) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice T) values index = .ok value :=
  initializer_slice_index values.slice index value found

end Itasca.Compiler

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Combined retained-vector size, used only to account for append headroom. -/
def initializerSize (m : runtime.compiler.ExecutableModule) : Nat :=
  m.functions.val.length + m.global_initializers.val.length +
  m.element_initializers.val.length + m.element_offsets.val.length + m.data_offsets.val.length

end Itasca.Compiler

namespace Itasca.Compiler
open Aeneas Aeneas.Std

@[step] theorem initializer_push_total {A T : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget : runtime.compiler.Budget A)
    (values : alloc.vec.Vec T) (value : T) (fits : values.val.length < Usize.max) :
    runtime.compiler.Budget.push ops budget values value ⦃ out =>
      out.2.2.val.length ≤ values.val.length + 1 ⦄ := by
  apply WP.spec_mono (budget_push ops law budget values value fits)
  rintro ⟨status, nextBudget, next⟩ (⟨_, _, h⟩ | ⟨_, h, _⟩)
  · simp [h]
  · change next = values at h
    simp [h]

end Itasca.Compiler
