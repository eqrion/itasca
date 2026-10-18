import Exec.Interp.StructuredMachine.BranchTablePoint
import Exec.Code.Local.Relations.Table.BranchTable
import Exec.Interp.Control.BrTableSource
import Exec.Interp.StructuredMachine.Point
import Exec.Abs.BrTableInvariants
namespace Exec.Interp.StructuredMachine
open Aeneas Aeneas.Std
variable {emission : FunctionEmission}

/-- The side-table certificate selects an ordinary structured BR point. No
per-target execution assumption is retained: every target is an exact emitted
branch fragment with the existing scope continuation evidence. -/
theorem step_brTable_point {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
    (selector start len : U32) (value : Nat)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr) (depths : List labelidx) (fallback : labelidx) (front : List val)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (frameLookup : exec.frames.val[frameIndex.val]? = some raw)
    (instanceLookup : store.instances.val[raw.instance.val]? = some inst)
    (functionLookup : inst.module.functions.val[raw.function.val]? = some compiled)
    (last : frameIndex.val+1 = exec.frames.length) (pcBound : raw.pc.val < U32.max)
    (bound : value < 2^32)
    (table : Code.BranchTableCode (Code.CompilerTables.ofFunction compiled) C.LOCALS targets
      (front.map Code.valueType) compiled.code.val depths fallback raw.pc.val next selector start len)
    (bindings : Abs.ModuleBindings s f.module C) (locals : C.LOCALS = f.locals.map Code.valueType)
    (labels : LabelsMatch (front ++ [Abs.integerVal .I32 value]) f.labels targets)
    (continuations : Code.StructuredCodeWithTables.Targets (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS compiled.code.val compiled.jump_tables.val targets)
    (normals : Code.StructuredCodeWithTables.Normals (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS compiled.code.val compiled.jump_tables.val targets)
    (aligned : Code.ExitAligned targets next) (root : Code.RootAligned compiled.code.val f.resultTypes targets next output)
    (typed : Abs.CoreTyped ⟨s,ambient,{f with code := .BR_TABLE depths fallback::after,vals := front ++ [Abs.integerVal .I32 value]}::rest,[]⟩)
    (slots : FrameSlots exec raw {f with vals := front ++ [Abs.integerVal .I32 value]}) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      ∃ target, out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      out.2.1 = {exec with frames := exec.frames.set frameIndex {raw with pc := target}} ∧
      FrameSlots out.2.1 {raw with pc := target} {f with code := .BR (Abs.BrTable.select depths fallback value)::after,vals := front} ∧
      FramePoint emission s {raw with pc := target} {f with code := .BR (Abs.BrTable.select depths fallback value)::after,vals := front}
        compiled C targets next output ∧
      Abs.CoreTyped ⟨s,ambient,{f with code := .BR (Abs.BrTable.select depths fallback value)::after,vals := front}::rest,[]⟩ ∧
      Abs.NextSim ⟨s,ambient,{f with code := .BR_TABLE depths fallback::after,vals := front ++ [Abs.integerVal .I32 value]}::rest,[]⟩
        ⟨s,ambient,{f with code := .BR (Abs.BrTable.select depths fallback value)::after,vals := front}::rest,[]⟩ ⦄ := by
  obtain ⟨target,lookup,entry⟩ := table.selected value
  have frameTyped : Abs.FrameTyped s {f with code := .BR_TABLE depths fallback::after,vals := front ++ [Abs.integerVal .I32 value]} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  have heights : ∀ label ∈ f.labels, label.height ≤ front.length := by
    obtain ⟨C,first,operands,ins,outs,bindings,locals,head,split,operandTypes,firstWf,bounds⟩ :=
      Abs.frame_typed_operands_bounds (f := {f with vals := front ++ [Abs.integerVal .I32 value]}) frameTyped
    cases head with
    | br_table =>
      have sizes := congrArg List.length split
      have operandSizes := operandTypes.length_eq
      simp only [List.length_append,List.length_singleton] at sizes operandSizes
      intro label member
      have small := bounds label member
      omega
  have reducedLabels : LabelsMatch front f.labels targets := by
    simpa only [List.append_nil] using labels.replace_suffix (after := []) heights
  have point : FramePoint emission s {raw with pc := target}
      {f with code := .BR (Abs.BrTable.select depths fallback value)::after,vals := front} compiled C targets next output := by
    exact ⟨bindings,locals,reducedLabels,
      ⟨entry.structured_indexed (emission compiled C) C.TYPES C.FUNCS f.resultTypes compiled.jump_tables.val after output,
        continuations,normals,aligned,root⟩⟩
  apply WP.spec_mono (step_brTable_refines memory hooks floats allocator exec store platform frameIndex raw inst compiled
    selector start len target value s ambient f rest after depths fallback front frameLookup instanceLookup functionLookup
    last pcBound table.instruction bound table.length table.arithmetic
    (by simpa only [table.length,Nat.add_sub_cancel,Code.CompilerTables.ofFunction] using lookup)
    (by simpa only [locals,List.map_append,Code.slots_append] using table.selectorSlot) typed.typed slots)
  rintro out ⟨success,exactState,sameStore,samePlatform,outputSlots,afterTyped,simulation⟩
  exact ⟨target,success,sameStore,samePlatform,exactState,outputSlots,point,⟨afterTyped,typed.contents⟩,simulation⟩
end Exec.Interp.StructuredMachine
