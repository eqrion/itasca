import Itasca.Runtime.Interp.Machine.Point
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTable
import Itasca.Runtime.Interp.Control.BrTableSource
import Itasca.Runtime.SourceMachine.BrTableTransition
import Itasca.Runtime.Interp.Machine.Progress.SupportedAdvance

/-!
Branch-table lookup and execution. The resulting argument is consumed by complete machine advance while preserving its source grammar and store premises.
-/

/-! ## Branch Table Point -/

section

namespace Itasca.Runtime.Interp.Machine
open Aeneas.Std

theorem branch_table_point_head {emit types functions returns locals code jumpTables labels stack pc next output depths fallback after}
    (point : Compiler.StructuredCode.Point emit types functions returns locals code jumpTables labels stack
      (.BR_TABLE depths fallback::after) pc next output) :
    (∃ target : U32, pc<target.val ∧ code[pc]?=some (.Jump target) ∧
      Compiler.StructuredCode.Point emit types functions returns locals code jumpTables labels stack
        (.BR_TABLE depths fallback::after) target.val next output) ∨
    (∃ front selector start len, stack=front++[.I32] ∧
      Compiler.BranchTableLayout jumpTables locals labels front code depths fallback pc next selector start len) := by
  cases point.current with
  | linear head ordinary fragment rest => exact False.elim (ordinary depths fallback rfl)
  | skip forward fetched rest =>
    exact Or.inl ⟨_,forward,fetched,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | branchTable gate table bounds => exact Or.inr ⟨_,_,_,_,rfl,table⟩

end Itasca.Runtime.Interp.Machine
namespace Itasca.Runtime.Compiler
open Aeneas.Std

theorem BranchTableEntry.structured_indexed {locals labels stack code depth entry next}
    (entryCode : BranchTableEntry locals labels stack code depth entry next)
    (emission : List valtype → instr → List Bytecode → List valtype → Prop)
    (types functions : List functype) (returns : List valtype) (jumpTables : List U32)
    (after : List instr) (output : List valtype) :
    StructuredCode emission types functions returns locals code jumpTables labels stack
      (.BR depth :: after) entry.val next output := by
  obtain ⟨label,dst,src,count,fragmentEnd,lookup,live,layout,fragment,remaining,scope⟩ := entryCode
  cases depth with
  | mk_uN depth => exact .branch lookup live layout fragment remaining scope
end Itasca.Runtime.Compiler

end

/-! ## Branch Table -/

section

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std

/-- The side-table certificate selects an ordinary structured BR point. No
per-target execution assumption is retained: every target is an exact emitted
branch fragment with the existing scope continuation evidence. -/
theorem step_br_table_point {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (selector start len : U32) (value : Nat)
    (s : _root_.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (depths : List labelidx) (fallback : labelidx) (front : List val)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (frameLookup : exec.frames.val[frameIndex.val]? = some raw)
    (instanceLookup : store.instances.val[raw.instance.val]? = some inst)
    (functionLookup : inst.module.functions.val[raw.function.val]? = some compiled)
    (last : frameIndex.val+1 = exec.frames.length) (pcBound : raw.pc.val < U32.max)
    (bound : value < 2^32)
    (table : Compiler.BranchTableCode (Compiler.CompilerTables.ofFunction compiled) C.LOCALS targets
      (front.map Compiler.valueType) compiled.code.val depths fallback raw.pc.val next selector start len)
    (bindings : SourceMachine.ModuleBindings s f.module C) (locals : C.LOCALS = f.locals.map Compiler.valueType)
    (labels : LabelsMatch (front ++ [SourceMachine.integerVal .I32 value]) f.labels targets)
    (continuations : Compiler.StructuredCode.Targets (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS compiled.code.val compiled.jump_tables.val targets)
    (normals : Compiler.StructuredCode.Normals (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS compiled.code.val compiled.jump_tables.val targets)
    (aligned : Compiler.ExitAligned targets next) (root : Compiler.RootAligned compiled.code.val f.resultTypes targets next output)
    (typed : SourceMachine.CoreTyped ⟨s,ambient,{f with code := .BR_TABLE depths fallback::after,vals := front ++ [SourceMachine.integerVal .I32 value]}::rest,[]⟩)
    (slots : FrameSlots exec raw {f with vals := front ++ [SourceMachine.integerVal .I32 value]}) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      ∃ target, out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      out.2.1 = {exec with frames := exec.frames.set frameIndex {raw with pc := target}} ∧
      FrameSlots out.2.1 {raw with pc := target} {f with code := .BR (SourceMachine.BrTable.select depths fallback value)::after,vals := front} ∧
      FramePoint s {raw with pc := target} {f with code := .BR (SourceMachine.BrTable.select depths fallback value)::after,vals := front}
        compiled C targets next output ∧
      SourceMachine.CoreTyped ⟨s,ambient,{f with code := .BR (SourceMachine.BrTable.select depths fallback value)::after,vals := front}::rest,[]⟩ ∧
      SourceMachine.NextSim ⟨s,ambient,{f with code := .BR_TABLE depths fallback::after,vals := front ++ [SourceMachine.integerVal .I32 value]}::rest,[]⟩
        ⟨s,ambient,{f with code := .BR (SourceMachine.BrTable.select depths fallback value)::after,vals := front}::rest,[]⟩ ⦄ := by
  obtain ⟨target,lookup,entry⟩ := table.selected value
  have frameTyped : SourceMachine.FrameTyped s {f with code := .BR_TABLE depths fallback::after,vals := front ++ [SourceMachine.integerVal .I32 value]} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  have heights : ∀ label ∈ f.labels, label.height ≤ front.length := by
    obtain ⟨C,first,operands,ins,outs,bindings,locals,head,split,operandTypes,firstWf,bounds⟩ :=
      SourceMachine.frame_typed_operands_bounds (f := {f with vals := front ++ [SourceMachine.integerVal .I32 value]}) frameTyped
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
  have point : FramePoint s {raw with pc := target}
      {f with code := .BR (SourceMachine.BrTable.select depths fallback value)::after,vals := front} compiled C targets next output := by
    exact ⟨bindings,locals,reducedLabels,
      ⟨entry.structured_indexed (emission compiled C) C.TYPES C.FUNCS f.resultTypes compiled.jump_tables.val after output,
        continuations,normals,aligned,root⟩⟩
  apply WP.spec_mono (step_br_table_refines memory hooks floats allocator exec store platform frameIndex raw inst compiled
    selector start len target value s ambient f rest after depths fallback front frameLookup instanceLookup functionLookup
    last pcBound table.instruction bound table.length table.arithmetic
    (by simpa only [table.length,Nat.add_sub_cancel,Compiler.CompilerTables.ofFunction] using lookup)
    (by simpa only [locals,List.map_append,Compiler.slots_append] using table.selectorSlot) typed.typed slots)
  rintro out ⟨success,exactState,sameStore,samePlatform,outputSlots,afterTyped,simulation⟩
  exact ⟨target,success,sameStore,samePlatform,exactState,outputSlots,point,⟨afterTyped,typed.contents⟩,simulation⟩
end Itasca.Runtime.Interp.Machine

end

/-! ## Branch Table Execution -/

section

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std

/-- The actual table jump consumes its selector, then reuses the checked branch
fragment inside the same active and suspended machine. -/
theorem step_br_table_execution
 {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Compiler.LabelTarget)
    (next : Nat) (output : List valtype) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (depths : List labelidx) (fallback : labelidx) (front : List val) (value : Nat)
    (selector start len : U32) (expected : List valtype)
    (last : index.val+1=exec.frames.length) (hf : exec.frames.val[index.val]?=some raw)
    (hi : store.instances.val[raw.instance.val]?=some inst)
    (hc : inst.module.functions.val[raw.function.val]?=some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view code store) raw
      {f with code:=.BR_TABLE depths fallback::after} compiled C targets next output)
    (values : f.vals=front++[SourceMachine.integerVal .I32 value]) (bound : value<2^32)
    (table : Compiler.BranchTableCode (Compiler.CompilerTables.ofFunction compiled) C.LOCALS targets
      (front.map Compiler.valueType) compiled.code.val depths fallback raw.pc.val next selector start len)
    (machine : Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code:=.BR_TABLE depths fallback::after}::rest,[]⟩ expected raw.pc.val false) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1=.Ok () ∧ out.2.2.1=store ∧ out.2.2.2=platform ∧
      Advance view code store out.2.1 expected compiled.code.length raw.pc.val false
        ⟨Store.decodeStore view code store,ambient,{f with code:=.BR_TABLE depths fallback::after}::rest,[]⟩ ⦄ := by
  have transition : SourceMachine.BrTable.Transition
      ⟨Store.decodeStore view code store,ambient,{f with code:=.BR_TABLE depths fallback::after}::rest,[]⟩
      ⟨Store.decodeStore view code store,ambient,{f with code:=.BR (SourceMachine.BrTable.select depths fallback value)::after,vals:=front}::rest,[]⟩ := .next values bound
  apply WP.spec_mono (step_br_table_point memory hooks floats allocator exec store platform index raw inst compiled selector start len value
    (Store.decodeStore view code store) ambient f rest after depths fallback front C targets next output hf hi hc last
    (program.fetched_bound _ table.instruction) bound table point.bindings point.locals
    (by simpa only [←values] using point.labels) point.code.targets point.code.normal point.code.exit point.code.root
    (by simpa only [←values] using machine.typed) (by simpa only [←values] using slots))
  rintro out ⟨target,success,sameStore,samePlatform,effect,represented,retained,typed,simulation⟩
  refine ⟨success,sameStore,samePlatform,target.val,false,
    ⟨Store.decodeStore view code store,ambient,{f with code:=.BR (SourceMachine.BrTable.select depths fallback value)::after,vals:=front}::rest,[]⟩,?_,?_,?_,rfl,?_⟩
  · exact Execution.ordinary view code ambient {f with code:=.BR_TABLE depths fallback::after}
      {f with code:=.BR (SourceMachine.BrTable.select depths fallback value)::after,vals:=front} rest expected raw.pc.val false machine
      (.refl store) (Itasca.Runtime.Spec.extend_store_refl _ machine.typed.typed.store) raw index target last hf program (.ready retained)
      represented ⟨rfl,rfl,rfl,rfl⟩ (by rw [effect]) (by rw [effect]; exact .refl _ _) typed
      (transition.next_supported machine.core)
  · exact ConcreteSim.of_source _ _ _ _ _ (transition.correct machine.typed).2
  · exact fun _ owned => transition.next_owned owned
  · exact fun _ bounded => transition.next_bound bounded
end Itasca.Runtime.Interp.Machine

end
