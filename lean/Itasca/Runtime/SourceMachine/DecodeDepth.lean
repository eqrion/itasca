import Itasca.Runtime.SourceMachine.Decode
import Itasca.Runtime.Spec.Depth

namespace Itasca.Runtime.SourceMachine

@[simp] theorem instr_depth_value (value : val) : Spec.instrDepth (admininstr_val value) = 0 := by
  cases value <;> rfl

@[simp] theorem instr_depth_source (instruction : instr) :
    Spec.instrDepth (admininstr_instr instruction) = 0 := by
  cases instruction <;> rfl

@[simp] theorem instrs_depth_values (values : List val) : Spec.instrsDepth (SpecExt.vals values) = 0 := by
  induction values with
  | nil => rfl
  | cons value rest ih => simpa only [SpecExt.vals, List.map_cons, Spec.instrsDepth, instr_depth_value, Nat.zero_max] using ih

@[simp] theorem instrs_depth_source (instructions : List instr) :
    Spec.instrsDepth (instructions.map admininstr_instr) = 0 := by
  induction instructions with
  | nil => rfl
  | cons instruction rest ih => simp [Spec.instrsDepth, ih]

/-- Label contexts do not introduce administrative function frames. -/
@[simp] theorem decode_labels_depth (labels : List Label) (values : List val) (code : List admininstr) :
    Spec.instrsDepth (decodeLabels labels values code) = Spec.instrsDepth code := by
  induction labels generalizing values code with
  | nil => simp [decodeLabels]
  | cons label rest ih => simp only [decodeLabels, ih, List.singleton_append, Spec.instrsDepth, Spec.instrDepth,
      Spec.instrs_depth_append, instrs_depth_values, instrs_depth_source, Nat.zero_max, Nat.max_zero]

/-- Each retained abstract function contributes exactly one FRAME_ node. -/
@[simp] theorem decode_frames_depth (frames : List AFrame) (inner : List admininstr) :
    Spec.instrsDepth (decodeFrames frames inner) = Spec.instrsDepth inner + frames.length := by
  induction frames generalizing inner with
  | nil => simp
  | cons f rest ih => simp [decodeFrames, ih, Spec.instrDepth, Nat.add_assoc, Nat.add_comm]

@[simp] theorem decode_depth (source : AState) :
    Spec.frameDepth (decode source) = source.frames.length := by
  simp [decode, Spec.frameDepth]

end Itasca.Runtime.SourceMachine
