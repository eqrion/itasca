import Itasca.Runtime.Code.Local.Source.SourceEntryChain
import Itasca.Runtime.Code.Local.Callbacks.Control.CloseScope
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Unentered frames cannot acquire live exits or forward-branch fixups. -/
def DormantFrame (frame : runtime.compiler.Frame) : Prop :=
  frame.entry_reachable = false → frame.end_reachable = false ∧ frame.fixups.val = []

def DormantFrames (frames : List runtime.compiler.Frame) : Prop :=
  ∀ frame ∈ frames, DormantFrame frame

theorem DormantFrame.entered {frame} (live : frame.entry_reachable = true) : DormantFrame frame := by
  simp [DormantFrame, live]

theorem DormantFrame.fresh {frame} (ends : frame.end_reachable = false) (fixups : frame.fixups.val = []) :
    DormantFrame frame := fun _ => ⟨ends, fixups⟩

theorem DormantFrames.push {frames} (clean : DormantFrames frames) (frame : runtime.compiler.Frame)
    (fresh : DormantFrame frame) : DormantFrames (frames ++ [frame]) := by
  intro other member
  simp only [List.mem_append, List.mem_singleton] at member
  rcases member with member | rfl
  · exact clean other member
  · exact fresh

theorem DormantFrames.pop {frames frame} (clean : DormantFrames (frames ++ [frame])) : DormantFrames frames :=
  fun other member => clean other (List.mem_append_left _ member)

theorem DormantFrames.record_branch {frames} (clean : DormantFrames frames)
    (index : Nat) (frame : runtime.compiler.Frame) (fixups : alloc.vec.Vec Usize)
    (entered : frame.entry_reachable = true) :
    DormantFrames (frames.set index {frame with fixups, end_reachable := true}) := by
  intro other member
  rcases List.mem_or_eq_of_mem_set member with old | rfl
  · exact clean other old
  · exact DormantFrame.entered entered

theorem DormantFrames.replace_last {frames frame} (clean : DormantFrames (frames ++ [frame]))
    (next : runtime.compiler.Frame) (fresh : DormantFrame next) : DormantFrames (frames ++ [next]) :=
  clean.pop.push next fresh

/-- The complete live prefix supplies the selected frame's entry liveness;
therefore adding a branch preserves dormant-frame cleanliness. -/
theorem ScopeFrameStack.record_branch_dormant {A : Type} {locals parents current}
    {compiler : runtime.compiler.FunctionCompiler A} (stack : ScopeFrameStack locals compiler parents current)
    (chain : SourceEntryChain parents current) (live : current.entered = true)
    (clean : DormantFrames compiler.frames.val) (index : Nat) (frame : runtime.compiler.Frame)
    (fixups : alloc.vec.Vec Usize) (found : compiler.frames.val[index]? = some frame) :
    DormantFrames (compiler.frames.val.set index {frame with fixups, end_reachable := true}) :=
  clean.record_branch index frame fixups (stack.frame_entered chain live frame (List.mem_of_getElem? found))
theorem ScopeFrameStack.dormant_initial {A : Type} {locals current}
    {compiler : runtime.compiler.FunctionCompiler A} (stack : ScopeFrameStack locals compiler [] current)
    (live : current.entered = true) : DormantFrames compiler.frames.val := by
  intro frame member
  exact DormantFrame.entered (stack.frame_entered (.root current live) live frame member)
end Itasca.Runtime.Code
