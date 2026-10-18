import Exec.Code.Local.Callbacks.Table.CompilerTablePreservation
namespace Exec.Code
open Aeneas Aeneas.Std Itasca.ResultFacts

theorem compiler_emit_indirect {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (instruction : runtime.bytecode.Instr)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.emit ops before instruction = .ok (status, after)) :
    after.function.indirect = before.function.indirect  := by
  apply alloc.vec.Vec.ext
  exact congrArg CompilerTables.indirect (compiler_emit_tables ops before after instruction status accepted)

theorem compiler_copy_indirect {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (dst src count : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.copy ops before dst src count = .ok (status, after)) :
    after.function.indirect = before.function.indirect  := by
  apply alloc.vec.Vec.ext
  exact congrArg CompilerTables.indirect (compiler_copy_tables ops before after dst src count status accepted)

theorem compiler_pc_indirect {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A)
    (status : core.result.Result U32 Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.pc ops before = .ok (status, after)) :
    after.function.indirect = before.function.indirect  := by
  apply alloc.vec.Vec.ext
  exact congrArg CompilerTables.indirect (compiler_pc_tables ops before after status accepted)

theorem compiler_patch_indirect {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (pc : Usize) (target : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.patch ops before pc target = .ok (status, after)) :
    after.function.indirect = before.function.indirect  := by
  apply alloc.vec.Vec.ext
  exact congrArg CompilerTables.indirect (compiler_patch_tables ops before after pc target status accepted)

theorem compiler_observe_indirect {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.observe ops before state = .ok (status, after)) :
    after.function.indirect = before.function.indirect  := by
  apply alloc.vec.Vec.ext
  exact congrArg CompilerTables.indirect (compiler_observe_tables ops law before after state status accepted)

theorem compiler_finish_op_indirect {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (instruction : runtime.bytecode.Instr)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.lower.FunctionCompiler.finish_op ops before state instruction = .ok (status, after)) :
    after.function.indirect = before.function.indirect  := by
  apply alloc.vec.Vec.ext
  exact congrArg CompilerTables.indirect (compiler_finish_op_tables ops law before after state instruction status accepted)

theorem compiler_fixups_indirect {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (sites : alloc.vec.Vec Usize)
    (target : U32) (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (output : CompilerSnapshot A)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0
      ops before sites target index status = .ok output) :
    (snapshotCompiler output).function.indirect = before.function.indirect  := by
  apply alloc.vec.Vec.ext
  exact congrArg CompilerTables.indirect (compiler_fixups_tables ops before sites target index status output accepted)

theorem compiler_fixups_after_if_indirect {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (sites : alloc.vec.Vec Usize)
    (target : U32) (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (output : CompilerSnapshot A)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop1
      ops before sites target index status = .ok output) :
    (snapshotCompiler output).function.indirect = before.function.indirect  := by
  apply alloc.vec.Vec.ext
  exact congrArg CompilerTables.indirect (compiler_fixups_after_if_tables ops before sites target index status output accepted)

end Exec.Code
