import Itasca.Runtime.Compiler.Local.Callbacks.Function.CloseFunction
import Itasca.Runtime.Compiler.Local.Relations.Function.Function
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredLabelWiden
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredCodeAlgebra
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Appending the literal epilogue reconciles the root's separate normal and
branch flags with the retained function label. A zero-result dead body may
safely acquire a live empty epilogue, without changing its body evidence. -/
theorem structured_body_code_epilogue {jumpTables : List Aeneas.Std.U32} {emit types functions returns locals body code target normal branch}
    (relation : StructuredCode emit types functions returns locals code jumpTables
      [⟨[], returns, returns, target, target.val, [], [], normal, branch⟩]
      [] body 0 target.val returns)
    (position : target.val = code.length)
    (compiled : runtime.bytecode.CompiledFunction) (src count : U32)
    (width : count.val = slots returns)
    (emitted : compiled.code.val = code ++ [.Return src (if normal || branch then count else 0#u32)]) :
    StructuredCode emit types functions returns locals compiled.code.val jumpTables
      [functionRootLabel returns compiled target] [] body 0 target.val returns ∧
      compiled.code.val[target.val]? = some (.Return src (if normal || branch then count else 0#u32)) ∧
      compiled.code.val.length = target.val + 1 := by
  have found : compiled.code.val[target.val]? = some (.Return src (if normal || branch then count else 0#u32)) := by
    simp [emitted, position]
  have normalLive : normal = true → (functionRootLabel returns compiled target).normalLive = true := by
    intro live
    simp [functionRootLabel, found, live, width]
  have branchLive : branch = true → (functionRootLabel returns compiled target).branchLive = true := by
    intro live
    simp [functionRootLabel, found, live, width]
  refine ⟨?_, found, by simp [emitted, position]⟩
  have extended := relation.extend [.Return src (if normal || branch then count else 0#u32)]
  rw [← emitted] at extended
  apply extended.widenLabels
  exact .cons ⟨rfl, rfl, rfl, rfl, rfl, normalLive, branchLive⟩ .nil

/-- The actual final END constructs the retained body/epilogue relation from
the completed root prefix, after resolving every root branch. -/
@[step] theorem structured_close_function_body {jumpTables : List Aeneas.Std.U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (frame : runtime.compiler.Frame)
    (rest : alloc.vec.Vec runtime.compiler.Frame) (target : U32)
    (frames : compiler.frames.val = rest.val ++ [frame])
    (kind : frame.kind = .Body) (noIf : frame.if_pc = none)
    (position : target.val = compiler.function.code.val.length)
    (branches : BranchSites compiler.function.code.val frame.fixups.val)
    (mapFits : frame.map.val < compiler.function.controls.val.length)
    (coordinateFits : compiler.function.body_start.val + state.pos.val ≤ Usize.max)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (emitCoordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (types functions : List functype) (returns locals : List valtype) (body : List instr)
    (width : frame.results.val = slots returns)
    (bodyCode : StructuredCode emit types functions returns locals
      (patchCode compiler.function.code.val frame.fixups.val target) jumpTables
      [⟨[], returns, returns, target, target.val, [], [], compiler.reachable, frame.end_reachable⟩]
      [] body 0 target.val returns) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops compiler state .Block .Empty ⦃ out =>
      out.1 = .Ok () → out.2.frames = rest ∧
        StructuredCode emit types functions returns locals out.2.function.code.val jumpTables
          [functionRootLabel returns out.2.function target] [] body 0 target.val returns ∧
        (∃ count, out.2.function.code.val[target.val]? = some (.Return frame.height count)) ∧
        out.2.function.code.val.length = target.val + 1 ⦄ := by
  apply WP.spec_mono (close_function_effect ops law compiler state frame rest target frames kind noIf
    position branches mapFits coordinateFits codeFits sourceFits emitCoordinateFits)
  intro out effect accepted
  obtain ⟨popped, reachable, code, control⟩ := effect accepted
  have code' : out.2.function.code.val = patchCode compiler.function.code.val frame.fixups.val target ++
      [.Return frame.height (if compiler.reachable || frame.end_reachable then frame.results else 0#u32)] := by
    simpa [scopeExitLive, kind] using code
  obtain ⟨body', return', end'⟩ := structured_body_code_epilogue bodyCode
    (by simpa only [patchCode_length] using position) out.2.function frame.height frame.results width code'
  exact ⟨popped, body', ⟨_, return'⟩, end'⟩

end Itasca.Runtime.Code
