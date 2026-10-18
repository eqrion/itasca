import Exec.Code.Local.Callbacks.Control.EnterIf
import Exec.Code.Local.Relations.Common.SuspendedPrefix
import Exec.Code.Local.Relations.Common.ResolvedPrefix
namespace Exec.Code
open Aeneas Aeneas.Std

/-- Starting a child leaves the saved parent's owned bytecode prefix intact,
even when entry appends a loop hook or condition guard. -/
theorem CodePrefix.suspend_after {types functions returns locals labels initial source start stack}
    {code : List Bytecode}
    (prior : CodePrefix types functions returns locals code labels initial source start code.length stack)
    (emitted : List Bytecode) :
    SuspendedPrefix types functions returns locals (code ++ emitted) labels initial source start code.length stack :=
  prior.suspend.extend emitted

/-- A new IF guard is its own pending group, separate from body branches. Its
future resolution touches only the newly appended guard. -/
theorem resolvedCode_open_guard (code : List Bytecode) (groups : List FixupTarget)
    (condition old target : U32) (site : Usize) (position : site.val = code.length)
    (inside : FixupsInside groups code.length) :
    resolvedCode (code ++ [.JumpIfZero condition old]) (⟨[site], target⟩ :: groups) =
      resolvedCode code groups ++ [.JumpIfZero condition target] := by
  have allInside : FixupsInside ([] ++ ⟨[], target⟩ :: groups) code.length := by
    intro group member pc atSite
    simp only [List.nil_append, List.mem_cons] at member
    rcases member with rfl | member
    · simp at atSite
    · exact inside group member pc atSite
  simpa [resolvedCode, patchCode, BranchKind.instruction] using
    resolvedCode_new_branch code [] [] groups ⟨[], target⟩ (.zero condition) old site
      (by simpa using position) allInside

/-- Opening IF suspends the parent before its guard and starts an empty child
body after that guard, uniformly for every eventual guard destination. -/
theorem CodePrefix.open_if {types functions returns locals labels initial source start stack}
    {code : List Bytecode} {groups : List FixupTarget}
    (prior : CodePrefix types functions returns locals (resolvedCode code groups)
      labels initial source start code.length (stack ++ [.I32]))
    (condition old target : U32) (site : Usize) (position : site.val = code.length)
    (inside : FixupsInside groups code.length) (child : LabelTarget) :
    SuspendedPrefix types functions returns locals
      (resolvedCode (code ++ [.JumpIfZero condition old]) (⟨[site], target⟩ :: groups))
      labels initial source start code.length (stack ++ [.I32]) ∧
    CodePrefix types functions returns locals
      (resolvedCode (code ++ [.JumpIfZero condition old]) (⟨[site], target⟩ :: groups))
      (child :: labels) stack [] (code.length + 1) (code.length + 1) stack := by
  rw [resolvedCode_open_guard code groups condition old target site position inside]
  refine ⟨?_, CodePrefix.empty _ _ _ _ _ _ _ _⟩
  have prior' : CodePrefix types functions returns locals (resolvedCode code groups)
      labels initial source start (resolvedCode code groups).length (stack ++ [.I32]) := by
    simpa only [resolvedCode_length] using prior
  simpa only [resolvedCode_length] using prior'.suspend_after [.JumpIfZero condition target]

@[step] theorem enter_if_prefix {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature) (pc : U32)
    (stack : List valtype) (layout : CompilerLayout compiler (stack ++ [.I32]))
    (codeFits : compiler.function.code.val.length < Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length < Usize.max)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt compiler.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (heightFits : compiler.function.local_slots.val +
      stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max)
    (sourceFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (position : pc.val = compiler.function.code.val.length + 1)
    (mapsFit : compiler.function.controls.val.length < Usize.max)
    (framesFit : compiler.frames.val.length < Usize.max)
    (reachable : compiler.reachable = true)
    (typeTable functions : List functype) (returns locals initial : List valtype)
    (labels : List LabelTarget) (groups : List FixupTarget) (priorSource : List instr) (start : Nat)
    (inside : FixupsInside groups compiler.function.code.val.length)
    (prefixCode : CodePrefix typeTable functions returns locals (resolvedCode compiler.function.code.val groups)
      labels initial priorSource start compiler.function.code.val.length (stack ++ [.I32])) :
    runtime.compiler.control.FunctionCompiler.enter ops compiler state .Then bt ⦃ out =>
      out.1 = .Ok () → out.2.reachable = true ∧
        ∃ condition height source,
          condition.val = slots (compilerLocals compiler) + slots stack ∧
          out.2.function.code.val = compiler.function.code.val ++ [.JumpIfZero condition core.num.U32.MAX] ∧
          height.val = compiler.function.local_slots.val + stackWords (state.vals.val.take ctrl.value_stack_base.val) ∧
          source.val = compiler.function.body_start.val + compiler.next_source.val ∧
          out.2.frames.val = compiler.frames.val ++
            [⟨alloc.vec.Vec.len compiler.function.controls, .Then, height, signature.param_slots,
              signature.result_slots, pc, some (alloc.vec.Vec.len compiler.function.code), true, false, alloc.vec.Vec.new Usize⟩] ∧
          out.2.function.controls.val = compiler.function.controls.val ++
            [⟨.Then, source, 0#usize, UScalar.cast .Usize pc, 0#usize,
              ctrl.value_stack_base, signature.params, signature.results⟩] ∧
          ∀ (target : U32) (child : LabelTarget),
            SuspendedPrefix typeTable functions returns locals
              (resolvedCode out.2.function.code.val (⟨[alloc.vec.Vec.len compiler.function.code], target⟩ :: groups))
              labels initial priorSource start compiler.function.code.val.length (stack ++ [.I32]) ∧
            CodePrefix typeTable functions returns locals
              (resolvedCode out.2.function.code.val (⟨[alloc.vec.Vec.len compiler.function.code], target⟩ :: groups))
              (child :: labels) stack [] pc.val pc.val stack ⦄ := by
  apply WP.spec_mono (enter_if ops law compiler state ctrl prior bt signature pc stack layout
    codeFits offsetsFit controls selected valuesFit heightFits sourceFits position mapsFit framesFit reachable)
  intro out effect accepted
  obtain ⟨live, condition, height, source, slot, code, hheight, hsource, frames, maps⟩ := effect accepted
  refine ⟨live, condition, height, source, slot, code, hheight, hsource, frames, maps, ?_⟩
  intro target child
  rw [code, position]
  exact prefixCode.open_if condition core.num.U32.MAX target
    (alloc.vec.Vec.len compiler.function.code) rfl inside child

@[step] theorem enter_block_prefix {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature) (pc : U32)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt compiler.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (heightFits : compiler.function.local_slots.val +
      stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max)
    (sourceFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (position : pc.val = compiler.function.code.val.length)
    (mapsFit : compiler.function.controls.val.length < Usize.max)
    (framesFit : compiler.frames.val.length < Usize.max)
    (reachable : compiler.reachable = true)
    (typeTable functions : List functype) (returns locals initial stack : List valtype)
    (labels : List LabelTarget) (groups : List FixupTarget) (priorSource : List instr) (start : Nat)
    (prefixCode : CodePrefix typeTable functions returns locals (resolvedCode compiler.function.code.val groups)
      labels initial priorSource start compiler.function.code.val.length stack) :
    runtime.compiler.control.FunctionCompiler.enter ops compiler state .Block bt ⦃ out =>
      out.1 = .Ok () → out.2.function.code = compiler.function.code ∧
        out.2.reachable = true ∧
        ∃ height source,
          height.val = compiler.function.local_slots.val + stackWords (state.vals.val.take ctrl.value_stack_base.val) ∧
          source.val = compiler.function.body_start.val + compiler.next_source.val ∧
          out.2.frames.val = compiler.frames.val ++
            [⟨alloc.vec.Vec.len compiler.function.controls, .Block, height, signature.param_slots,
              signature.result_slots, pc, none, true, false, alloc.vec.Vec.new Usize⟩] ∧
          out.2.function.controls.val = compiler.function.controls.val ++
            [⟨.Block, source, 0#usize, UScalar.cast .Usize pc, 0#usize,
              ctrl.value_stack_base, signature.params, signature.results⟩] ∧
          SuspendedPrefix typeTable functions returns locals (resolvedCode out.2.function.code.val groups)
            labels initial priorSource start pc.val stack ∧
          ∀ child : LabelTarget, CodePrefix typeTable functions returns locals (resolvedCode out.2.function.code.val groups)
            (child :: labels) stack [] pc.val pc.val stack ⦄ := by
  apply WP.spec_mono (enter_block ops law compiler state ctrl prior bt signature pc
    controls selected valuesFit heightFits sourceFits position mapsFit framesFit reachable)
  intro out effect accepted
  obtain ⟨code, live, height, source, hheight, hsource, frames, maps⟩ := effect accepted
  refine ⟨code, live, height, source, hheight, hsource, frames, maps, ?_, ?_⟩
  · have prior' : CodePrefix typeTable functions returns locals (resolvedCode compiler.function.code.val groups)
        labels initial priorSource start (resolvedCode compiler.function.code.val groups).length stack := by
      simpa only [resolvedCode_length] using prefixCode
    simpa only [code, position, resolvedCode_length] using prior'.suspend
  · intro child
    exact CodePrefix.empty _ _ _ _ _ _ _ _

@[step] theorem enter_loop_prefix {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature) (pc : U32)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt compiler.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (heightFits : compiler.function.local_slots.val +
      stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max)
    (sourceFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (position : pc.val = compiler.function.code.val.length)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length < Usize.max)
    (mapsFit : compiler.function.controls.val.length < Usize.max)
    (framesFit : compiler.frames.val.length < Usize.max)
    (reachable : compiler.reachable = true)
    (typeTable functions : List functype) (returns locals initial stack : List valtype)
    (labels : List LabelTarget) (groups : List FixupTarget) (priorSource : List instr) (start : Nat)
    (inside : FixupsInside groups compiler.function.code.val.length)
    (prefixCode : CodePrefix typeTable functions returns locals (resolvedCode compiler.function.code.val groups)
      labels initial priorSource start compiler.function.code.val.length stack) :
    runtime.compiler.control.FunctionCompiler.enter ops compiler state .Loop bt ⦃ out =>
      out.1 = .Ok () → out.2.function.code.val = compiler.function.code.val ++ [.LoopHead] ∧
        out.2.reachable = true ∧
        ∃ height source,
          height.val = compiler.function.local_slots.val + stackWords (state.vals.val.take ctrl.value_stack_base.val) ∧
          source.val = compiler.function.body_start.val + compiler.next_source.val ∧
          out.2.frames.val = compiler.frames.val ++
            [⟨alloc.vec.Vec.len compiler.function.controls, .Loop, height, signature.param_slots,
              signature.result_slots, pc, none, true, false, alloc.vec.Vec.new Usize⟩] ∧
          out.2.function.controls.val = compiler.function.controls.val ++
            [⟨.Loop, source, 0#usize, UScalar.cast .Usize pc, 0#usize,
              ctrl.value_stack_base, signature.params, signature.results⟩] ∧
          SuspendedPrefix typeTable functions returns locals (resolvedCode out.2.function.code.val groups)
            labels initial priorSource start pc.val stack ∧
          ∀ child : LabelTarget, CodePrefix typeTable functions returns locals (resolvedCode out.2.function.code.val groups)
            (child :: labels) stack [] (pc.val + 1) (pc.val + 1) stack ⦄ := by
  apply WP.spec_mono (enter_loop ops law compiler state ctrl prior bt signature pc
    controls selected valuesFit heightFits sourceFits position codeFits offsetsFit mapsFit framesFit reachable)
  intro out effect accepted
  obtain ⟨code, live, height, source, hheight, hsource, frames, maps⟩ := effect accepted
  refine ⟨code, live, height, source, hheight, hsource, frames, maps, ?_, ?_⟩
  · have prior' : CodePrefix typeTable functions returns locals (resolvedCode compiler.function.code.val groups)
        labels initial priorSource start (resolvedCode compiler.function.code.val groups).length stack := by
      simpa only [resolvedCode_length] using prefixCode
    rw [code, resolvedCode_append_code _ _ _ inside]
    simpa only [position, resolvedCode_length] using prior'.suspend_after [.LoopHead]
  · intro child
    exact CodePrefix.empty _ _ _ _ _ _ _ _

end Exec.Code
