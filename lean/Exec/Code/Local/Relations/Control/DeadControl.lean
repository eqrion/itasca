import Exec.Code.Local.Relations.Common.LiveExits
import Exec.Code.Local.Relations.Common.Function
namespace Exec.Code
open Aeneas.Std

/-- A dead nonvoid function body needs no result-producing bytecode before its
zero-width synthetic epilogue. -/
theorem dead_nonvoid_body (compiled : runtime.bytecode.CompiledFunction)
    (code : compiled.code.val = [.Unreachable, .Return 0#u32 0#u32]) :
    CodeRel [] [] [.I32] [] compiled.code.val
      [functionRootLabel [.I32] compiled 1#u32] [] [.UNREACHABLE] 0 1 [.I32] ∧
    (functionRootLabel [.I32] compiled 1#u32).normalLive = false ∧
    (functionRootLabel [.I32] compiled 1#u32).branchLive = false := by
  refine ⟨.unreachable (by simp [code]) (by decide) (by simp [code]), ?_, ?_⟩ <;>
    simp [functionRootLabel, code, slots, width]

/-- A back edge keeps its loop target live even though the source suffix after
that loop has no emitted instructions. -/
theorem dead_loop_suffix :
    CodeRel [] [] [] [] [.LoopHead, .Jump 0#u32, .Return 0#u32 0#u32] [] []
      [.LOOP (._RESULT none) [.BR (.mk_uN 0)],
       .CONST .I32 (.mk_num__0 .I32 (.mk_uN 1)), .DROP]
      0 2 [] := by
  apply CodeRel.dead_loop (entry := 0#u32) (exit := 2) (front := [])
    (params := []) (results := []) .empty rfl
  · apply CodeRel.branch (depth := 0) (dst := 0#u32) (src := 0#u32)
      (count := 0#u32) (fragmentEnd := 2) rfl rfl
    · exact ⟨[], rfl, rfl, rfl, rfl⟩
    · exact ⟨[.LoopHead], [.Return 0#u32 0#u32], rfl, rfl, rfl⟩
    · decide
    · decide
  · decide
end Exec.Code
