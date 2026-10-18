import Exec.Interp.FloatCore.BranchInversion
import Exec.Interp.FloatCore.BranchPoint
import Exec.Interp.FloatCore.ControlInversion
import Exec.Interp.Relations.PrefixDispatch
namespace Exec.Interp
open Aeneas Aeneas.Std

theorem float_core_loop_fetch {s raw compiled C targets next output} {f : Abs.AFrame}
    (bt : blocktype) (body after : List instr)
    (point : FloatFramePoint s raw {f with code := .LOOP bt body::after} compiled C targets next output) :
    ∃ instruction, compiled.code.val[raw.pc.val]? = some instruction ∧ PrefixInstruction instruction := by
  rcases floatCoreCodeRel_loop_inv point.code.current with ⟨target,forward,fetch,tail⟩ | branch
  · exact ⟨_,fetch,.jump target⟩
  · obtain ⟨front,params,results,entry,exit,live,shape,atEntry,signature,fetch,bodyCode,continuation,bounds⟩ := branch
    exact ⟨.LoopHead,by simpa only [atEntry] using fetch,.loopHead⟩

theorem float_core_if_fetch {s raw compiled C targets next output} {f : Abs.AFrame}
    (bt : blocktype) (yes no after : List instr)
    (point : FloatFramePoint s raw {f with code := .IFELSE bt yes no::after} compiled C targets next output) :
    ∃ instruction, compiled.code.val[raw.pc.val]? = some instruction ∧ PrefixInstruction instruction := by
  rcases floatCoreCodeRel_if_inv point.code.current with ⟨target,forward,fetch,tail⟩ | branch
  · exact ⟨_,fetch,.jump target⟩
  · obtain ⟨front,params,results,cond,noEntry,yesExit,exit,yn,yb,nn,nb,shape,signature,condition,fetch,yesCode,skip,noCode,continuation,bounds⟩ := branch
    exact ⟨_,fetch,.jumpZero cond noEntry⟩

theorem float_core_transfer_prefix (dst src count : U32) : PrefixInstruction (Code.transferInstruction dst src count) := by
  unfold Code.transferInstruction
  split
  · exact .copy ..
  · split
    · exact .copy2 ..
    · exact .copyN ..

theorem float_core_branch_fetch {s raw compiled C targets next output} {f : Abs.AFrame}
    (depth : Nat) (after : List instr)
    (point : FloatFramePoint s raw {f with code := .BR (.mk_uN depth)::after} compiled C targets next output) :
    ∃ instruction, compiled.code.val[raw.pc.val]? = some instruction ∧ PrefixInstruction instruction := by
  rcases floatCoreCodeRel_branch_inv point.code.current with ⟨target,forward,fetch,tail⟩ | branch
  · exact ⟨_,fetch,.jump target⟩
  · obtain ⟨target,dst,src,count,finish,lookup,live,layout,fragment,remaining⟩ := branch
    by_cases noCopy : count = 0#u32 ∨ src = dst
    · refine ⟨.Jump target.target,?_,.jump _⟩
      simpa only [Nat.add_zero] using fragment.fetch (index := 0) (by simp only [Code.branchInstructions,if_pos noCopy,List.getElem?_cons_zero])
    · refine ⟨Code.transferInstruction dst src count,?_,float_core_transfer_prefix ..⟩
      simpa only [Nat.add_zero] using fragment.fetch (index := 0) (by simp only [Code.branchInstructions,if_neg noCopy,List.getElem?_cons_zero])

theorem float_core_branchIf_fetch {s raw compiled C targets next output} {f : Abs.AFrame}
    (depth : Nat) (after : List instr)
    (point : FloatFramePoint s raw {f with code := .BR_IF (.mk_uN depth)::after} compiled C targets next output) :
    ∃ instruction, compiled.code.val[raw.pc.val]? = some instruction ∧ PrefixInstruction instruction := by
  rcases floatCoreCodeRel_branchIf_inv point.code.current with ⟨target,forward,fetch,tail⟩ | branch
  · exact ⟨_,fetch,.jump target⟩
  · obtain ⟨before,target,dst,src,count,cond,resume,shape,lookup,live,layout,condition,fragment,continuation⟩ := branch
    by_cases noCopy : count = 0#u32 ∨ src = dst
    · refine ⟨.JumpIfNonZero cond target.target,?_,.jumpNonzero ..⟩
      simpa only [Nat.add_zero] using fragment.fetch (index := 0) (by simp only [Code.branchIfInstructions,if_pos noCopy,List.getElem?_cons_zero])
    · refine ⟨.JumpIfZero cond resume,?_,.jumpZero ..⟩
      simpa only [Nat.add_zero] using fragment.fetch (index := 0) (by simp only [Code.branchIfInstructions,if_neg noCopy,List.getElem?_cons_zero])
end Exec.Interp
