import Exec.Code.Local.Control.Common.StructuredLabels
import Exec.Interp.Control.StructuredPoint
import Exec.Abs.Sim.Structured
import Exec.Abs.ControlSafety

namespace Exec.Interp
open Aeneas.Std

theorem blockSignature_resolves (m : moduleinst) (bt : blocktype) (params results : List valtype)
    (signature : Code.BlockSignature m.TYPES bt params results) :
    Abs.blockType m bt = some ⟨.mk_list params, .mk_list results⟩ := by
  cases signature with
  | empty => rfl
  | value ty => rfl
  | index i params results lookup => exact lookup

theorem block_source_step (s : store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (bt : blocktype) (body after : List instr) (front params results : List valtype)
    (signature : Code.BlockSignature f.module.TYPES bt params results)
    (shape : f.vals.map Code.valueType = front ++ params) :
    Abs.astep ⟨s, ambient, { f with code := .BLOCK bt body :: after } :: rest, []⟩ =
      .next ⟨s, ambient, { f with code := body, labels := ⟨results, results, [], front.length, after⟩ :: f.labels } :: rest, []⟩ := by
  have size : f.vals.length = front.length + params.length := by
    simpa only [List.length_map, List.length_append] using congrArg List.length shape
  have height : f.vals.length - params.length = front.length := by omega
  have args : (f.vals.drop (f.vals.length - params.length)).map Abs.valueType = params := by
    rw [show Abs.valueType = Code.valueType from (funext valueType_eq_abs).symm,
      List.map_drop, height, shape, List.drop_left]
  rw [height] at args
  have resolved := blockSignature_resolves f.module bt params results signature
  simp [Abs.astep, Abs.enterLabel, resolved, height, args, show params.length ≤ f.vals.length by omega, Abs.advance]

theorem LabelsMatch.enter {values : List val} {labels : List Abs.Label} {targets : List Code.LabelTarget}
    (outer : LabelsMatch values labels targets) (front params results branchTypes : List valtype)
    (branch : U32) (normalExit : Nat) (cont after : List instr) {normalLive branchLive : Bool}
    (shape : values.map Code.valueType = front ++ params) :
    LabelsMatch values (⟨branchTypes, results, cont, front.length, after⟩ :: labels)
      (⟨front, branchTypes, results, branch, normalExit, cont, after, normalLive, branchLive⟩ :: targets) := by
  refine ⟨by simp only [List.length_cons, outer.length], ?_⟩
  intro depth label lookup
  cases depth with
  | zero =>
    have same : label = ⟨branchTypes, results, cont, front.length, after⟩ := by simpa using lookup.symm
    subst label
    refine ⟨_, rfl, ⟨?_, rfl, rfl, rfl, rfl, rfl⟩⟩
    simp only [List.map_take, shape, List.take_left]
  | succ depth =>
    obtain ⟨target, found, matching⟩ := outer.atIndex depth label (by simpa using lookup)
    exact ⟨target, by simpa using found, matching⟩

/-- BLOCK creates a source label without consuming bytecode. Its two retained
continuations distinguish normal IF-arm completion from explicit branches. -/
theorem block_entry_point (exec : runtime.interp.Execution) (raw : runtime.interp.Frame)
    (compiled : runtime.bytecode.CompiledFunction) (functions : List functype)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (s : store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (bt : blocktype) (body after : List instr) (front params results : List valtype)
    (normalExit : Nat) (branchExit : U32) (normalLive branchLive : Bool)
    (typed : Abs.ATyped ⟨s, ambient, { f with code := .BLOCK bt body :: after } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (point : StructuredFramePoint raw { f with code := .BLOCK bt body :: after }
      compiled functions targets next output)
    (shape : f.vals.map Code.valueType = front ++ params)
    (signature : Code.BlockSignature f.module.TYPES bt params results)
    (bodyCode : Code.CodeRel f.module.TYPES functions f.resultTypes (f.locals.map Code.valueType)
      compiled.code.val (⟨front, results, results, branchExit, normalExit, [], after, normalLive, branchLive⟩ :: targets)
      (front ++ params) body raw.pc.val normalExit (front ++ results))
    (normal : normalLive = true → Code.CodeRel f.module.TYPES functions f.resultTypes (f.locals.map Code.valueType)
      compiled.code.val targets (front ++ results) after normalExit next output)
    (branch : branchLive = true → Code.CodeRel f.module.TYPES functions f.resultTypes (f.locals.map Code.valueType)
      compiled.code.val targets (front ++ results) after branchExit.val next output) :
    let g := { f with code := body, labels := ⟨results, results, [], front.length, after⟩ :: f.labels }
    FrameSlots exec raw g ∧
    StructuredFramePoint raw g compiled functions
      (⟨front, results, results, branchExit, normalExit, [], after, normalLive, branchLive⟩ :: targets) normalExit (front ++ results) ∧
    Abs.ATyped ⟨s, ambient, g :: rest, []⟩ ∧
    Abs.NextSim ⟨s, ambient, { f with code := .BLOCK bt body :: after } :: rest, []⟩
      ⟨s, ambient, g :: rest, []⟩ := by
  have step := block_source_step s ambient f rest bt body after front params results signature shape
  refine ⟨slots, ⟨point.labels.enter front params results results branchExit normalExit [] after shape, ?_⟩,
    Abs.block_preservation s ambient f rest after bt body _ typed step,
    Abs.typed_block_simulation s ambient f rest after bt body _ typed step⟩
  simpa only [shape] using Code.StructuredPoint.block_body bodyCode normal branch
    point.code.targets point.code.normal point.code.exit point.code.root

theorem loop_source_step (s : store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (bt : blocktype) (body after : List instr) (front params results : List valtype)
    (signature : Code.BlockSignature f.module.TYPES bt params results)
    (shape : f.vals.map Code.valueType = front ++ params) :
    Abs.astep ⟨s, ambient, { f with code := .LOOP bt body :: after } :: rest, []⟩ =
      .next ⟨s, ambient, { f with code := body, labels := ⟨params, results, [.LOOP bt body], front.length, after⟩ :: f.labels } :: rest, []⟩ := by
  have size : f.vals.length = front.length + params.length := by
    simpa only [List.length_map, List.length_append] using congrArg List.length shape
  have height : f.vals.length - params.length = front.length := by omega
  have args : (f.vals.drop (f.vals.length - params.length)).map Abs.valueType = params := by
    rw [show Abs.valueType = Code.valueType from (funext valueType_eq_abs).symm,
      List.map_drop, height, shape, List.drop_left]
  rw [height] at args
  have resolved := blockSignature_resolves f.module bt params results signature
  simp [Abs.astep, Abs.enterLabel, resolved, height, args, show params.length ≤ f.vals.length by omega, Abs.advance]


end Exec.Interp
