import Exec.Code.Local.Checking.PendingInstructionClose

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Patching the last frame and appending a checked epilogue discharges every
pending branch obligation. Earlier resolved end targets become strict because
the actual code vector grows. -/
theorem compiler_instruction_root_publish {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (held : CompilerInstructionPrefix before) (frame : runtime.compiler.Frame)
    (rest : alloc.vec.Vec runtime.compiler.Frame) (target : U32)
    (beforeFrames : before.frames.val = rest.val++[frame]) (afterFrames : after.frames = rest)
    (closed : rest.val = []) (growth : InstructionCheckExtends before.function after.function)
    (fragment : List runtime.bytecode.Instr)
    (code : after.function.code.val = patchCode before.function.code.val (frameInstructionSites frame) target++fragment)
    (nonempty : 0 < fragment.length) (inside : target.val < after.function.code.length)
    (fresh : ∀ instruction ∈ fragment,
      runtime.bytecode.CompiledFunction.instruction_valid after.function instruction = .ok true) :
    CheckedInstructionPrefix after.function := by
  have strict : before.function.code.length < after.function.code.length := by
    change before.function.code.val.length < after.function.code.val.length
    rw [code,List.length_append,patchCode_length]
    omega
  intro instruction member
  rw [code] at member
  rcases List.mem_append.mp member with old | new
  · obtain ⟨index,bound,found⟩ := List.getElem_of_mem old
    have fetched : (patchCode before.function.code.val (frameInstructionSites frame) target)[index]? = some instruction := by
      simp [List.getElem?_eq_getElem bound,found]
    rw [patchCode_get] at fetched
    split at fetched
    · cases original : before.function.code.val[index]? with
      | none => simp [original] at fetched
      | some prior =>
        have same : retarget prior target = instruction := by simpa [original] using fetched
        rw [← same]
        exact (held index prior original).retarget_accepts growth target inside
    · rename_i unchanged
      have old := held index instruction fetched
      have noOwner : PendingInstructionSite before index → False := by
        intro owned
        have remaining := pending_instruction_pop frame rest beforeFrames afterFrames index (by simpa using unchanged) owned
        obtain ⟨owner,member,_⟩ := remaining
        rw [afterFrames,closed] at member
        cases member
      have checked : OpenInstructionCheck before.function (fun _ => False) index instruction :=
        old.grow (.refl _) noOwner
      exact checked.publish growth strict
  · exact fresh instruction new

end Itasca.Runtime.Code
