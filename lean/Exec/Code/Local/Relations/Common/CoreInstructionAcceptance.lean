import Exec.Code.Local.Relations.Common.SlotCheckAcceptance

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- Numerical publication obligations for non-projected bytecode forms.
Global/function indices are checked by execution against its environment; the
local bytecode checker checks slots and its own function-local table indices. -/
inductive CoreInstructionBounds (function : runtime.bytecode.CompiledFunction) : runtime.bytecode.Instr → Prop
  | copy {dst src : U32} (slot0 : dst.val+1 ≤ function.slot_count.val) (slot1 : src.val+1 ≤ function.slot_count.val) : CoreInstructionBounds function (.Copy dst src)
  | copy2 {dst src : U32} (slot0 : dst.val+2 ≤ function.slot_count.val) (slot1 : src.val+2 ≤ function.slot_count.val) : CoreInstructionBounds function (.Copy2 dst src)
  | copyN {dst src count : U32} (slot0 : dst.val+count.val ≤ function.slot_count.val) (slot1 : src.val+count.val ≤ function.slot_count.val) (bound0 : dst.val ≤ src.val) : CoreInstructionBounds function (.CopyN dst src count)
  | const32 {dst value : U32} (slot0 : dst.val+1 ≤ function.slot_count.val) : CoreInstructionBounds function (.Const32 dst value)
  | const64 {dst : U32} {value64 : U64} (slot0 : dst.val+1 ≤ function.slot_count.val) : CoreInstructionBounds function (.Const64 dst value64)
  | constV128 {dst entry : U32} (slot0 : dst.val+2 ≤ function.slot_count.val) (bound0 : entry.val < function.v128_pool.length) : CoreInstructionBounds function (.ConstV128 dst entry)
  | jump {target : U32} (bound0 : target.val < function.code.length) : CoreInstructionBounds function (.Jump target)
  | jumpIfZero {cond target : U32} (slot0 : cond.val+1 ≤ function.slot_count.val) (bound0 : target.val < function.code.length) : CoreInstructionBounds function (.JumpIfZero cond target)
  | jumpIfNonZero {cond target : U32} (slot0 : cond.val+1 ≤ function.slot_count.val) (bound0 : target.val < function.code.length) : CoreInstructionBounds function (.JumpIfNonZero cond target)
  | jumpTable {index start count : U32} (slot0 : index.val+1 ≤ function.slot_count.val) (bound0 : 0 < count.val) (bound1 : start.val+count.val ≤ function.jump_tables.length) : CoreInstructionBounds function (.JumpTable index start count)
  | loopHead : CoreInstructionBounds function (.LoopHead)
  | call {index base : U32} (slot0 : base.val+0 ≤ function.slot_count.val) : CoreInstructionBounds function (.Call index base)
  | callIndirect {entry index base : U32} (slot0 : base.val+0 ≤ function.slot_count.val) (slot1 : index.val+1 ≤ function.slot_count.val) (bound0 : entry.val < function.indirect.length) : CoreInstructionBounds function (.CallIndirect entry index base)
  | return_ {src count : U32} (slot0 : src.val+count.val ≤ function.slot_count.val) : CoreInstructionBounds function (.Return src count)
  | unreachable : CoreInstructionBounds function (.Unreachable)
  | select {left right cond : U32} (slot0 : left.val+1 ≤ function.slot_count.val) (slot1 : right.val+1 ≤ function.slot_count.val) (slot2 : cond.val+1 ≤ function.slot_count.val) : CoreInstructionBounds function (.Select left right cond)
  | select2 {left right cond : U32} (slot0 : left.val+2 ≤ function.slot_count.val) (slot1 : right.val+2 ≤ function.slot_count.val) (slot2 : cond.val+1 ≤ function.slot_count.val) : CoreInstructionBounds function (.Select2 left right cond)
  | globalGet {dst index : U32} (slot0 : dst.val+1 ≤ function.slot_count.val) : CoreInstructionBounds function (.GlobalGet dst index)
  | globalGet2 {dst index : U32} (slot0 : dst.val+2 ≤ function.slot_count.val) : CoreInstructionBounds function (.GlobalGet2 dst index)
  | globalSet {src index : U32} (slot0 : src.val+1 ≤ function.slot_count.val) : CoreInstructionBounds function (.GlobalSet src index)
  | globalSet2 {src index : U32} (slot0 : src.val+2 ≤ function.slot_count.val) : CoreInstructionBounds function (.GlobalSet2 src index)
  | memorySize {dst : U32} (slot0 : dst.val+1 ≤ function.slot_count.val) : CoreInstructionBounds function (.MemorySize dst)
  | memoryGrow {dst : U32} (slot0 : dst.val+1 ≤ function.slot_count.val) : CoreInstructionBounds function (.MemoryGrow dst)
  | memoryFill {dst : U32} (slot0 : dst.val+3 ≤ function.slot_count.val) : CoreInstructionBounds function (.MemoryFill dst)
  | memoryCopy {dst : U32} (slot0 : dst.val+3 ≤ function.slot_count.val) : CoreInstructionBounds function (.MemoryCopy dst)
  | memoryInit {dst index : U32} (slot0 : dst.val+3 ≤ function.slot_count.val) : CoreInstructionBounds function (.MemoryInit dst index)
  | dataDrop {index : U32} : CoreInstructionBounds function (.DataDrop index)
  | tableGet {dst index table : U32} (slot0 : dst.val+1 ≤ function.slot_count.val) (slot1 : index.val+1 ≤ function.slot_count.val) : CoreInstructionBounds function (.TableGet dst index table)
  | tableSet {index value table : U32} (slot0 : index.val+1 ≤ function.slot_count.val) (slot1 : value.val+1 ≤ function.slot_count.val) : CoreInstructionBounds function (.TableSet index value table)
  | tableSize {dst table : U32} (slot0 : dst.val+1 ≤ function.slot_count.val) : CoreInstructionBounds function (.TableSize dst table)
  | tableGrow {dst table : U32} (slot0 : dst.val+2 ≤ function.slot_count.val) : CoreInstructionBounds function (.TableGrow dst table)
  | tableFill {dst table : U32} (slot0 : dst.val+3 ≤ function.slot_count.val) : CoreInstructionBounds function (.TableFill dst table)
  | tableCopy {dst entry : U32} (slot0 : dst.val+3 ≤ function.slot_count.val) (bound0 : entry.val < function.indirect.length) : CoreInstructionBounds function (.TableCopy dst entry)
  | tableInit {dst entry : U32} (slot0 : dst.val+3 ≤ function.slot_count.val) (bound0 : entry.val < function.indirect.length) : CoreInstructionBounds function (.TableInit dst entry)
  | elemDrop {index : U32} : CoreInstructionBounds function (.ElemDrop index)
  | refNull {dst : U32} (slot0 : dst.val+1 ≤ function.slot_count.val) : CoreInstructionBounds function (.RefNull dst)
  | refIsNull {dst input : U32} (slot0 : dst.val+1 ≤ function.slot_count.val) (slot1 : input.val+1 ≤ function.slot_count.val) : CoreInstructionBounds function (.RefIsNull dst input)
  | refFunc {dst index : U32} (slot0 : dst.val+1 ≤ function.slot_count.val) : CoreInstructionBounds function (.RefFunc dst index)

private theorem checked_difference_accepts (length start count : Usize)
    (inside : start.val+count.val ≤ length.val) :
    (do let remaining ← length-start; Result.ok (decide (count ≤ remaining))) = .ok true := by
  have checked : (do let remaining ← length-start; Result.ok (decide (count ≤ remaining))) ⦃ result => result = true ⦄ := by
    step as ⟨remaining,difference⟩
    simp only [WP.spec_ok,decide_eq_true_eq]
    scalar_tac
  obtain ⟨result,called,rfl⟩ := WP.spec_imp_exists checked
  exact called

/-- Every core form satisfies the actual checker from its arithmetic bounds. -/
theorem CoreInstructionBounds.accepts {function : runtime.bytecode.CompiledFunction}
    {instruction : runtime.bytecode.Instr} (bounds : CoreInstructionBounds function instruction) :
    runtime.bytecode.CompiledFunction.instruction_valid function instruction = .ok true := by
  cases bounds
  all_goals simp only [runtime.bytecode.CompiledFunction.instruction_valid,
    runtime.bytecode.Instr.scalar,runtime.bytecode.Instr.load,runtime.bytecode.Instr.store,
    runtime.bytecode.Instr.simd,runtime.bytecode.CompiledFunction.other_valid,bind_ok]
  all_goals repeat' first
    | rw [slots_fit_accepts _ _ _ (by scalar_tac)]
    | simp only [bind_ok,ite_true,lift]
  all_goals try split_ifs
  all_goals try simp_all only [Result.ok.injEq,decide_eq_true_eq,bind_ok]
  all_goals first | rfl | scalar_tac | (apply checked_difference_accepts; scalar_tac)

end Itasca.Runtime.Code
