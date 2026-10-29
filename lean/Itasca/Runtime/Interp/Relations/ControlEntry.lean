import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels
import Itasca.Runtime.Interp.Control.StructuredPoint
import Itasca.Runtime.SourceMachine.Sim.Structured
import Itasca.Runtime.SourceMachine.ControlSafety

namespace Itasca.Runtime.Interp
open Aeneas.Std

theorem block_signature_resolves (m : moduleinst) (bt : blocktype) (params results : List valtype)
    (signature : Compiler.BlockSignature m.TYPES bt params results) :
    SourceMachine.blockType m bt = some ⟨.mk_list params, .mk_list results⟩ := by
  cases signature with
  | empty => rfl
  | value ty => rfl
  | index i params results lookup => exact lookup

theorem block_source_step (s : store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (bt : blocktype) (body after : List instr) (front params results : List valtype)
    (signature : Compiler.BlockSignature f.module.TYPES bt params results)
    (shape : f.vals.map Compiler.valueType = front ++ params) :
    SourceMachine.astep ⟨s, ambient, { f with code := .BLOCK bt body :: after } :: rest, []⟩ =
      .next ⟨s, ambient, { f with code := body, labels := ⟨results, results, [], front.length, after⟩ :: f.labels } :: rest, []⟩ := by
  have size : f.vals.length = front.length + params.length := by
    simpa only [List.length_map, List.length_append] using congrArg List.length shape
  have height : f.vals.length - params.length = front.length := by omega
  have args : (f.vals.drop (f.vals.length - params.length)).map SourceMachine.valueType = params := by
    rw [show SourceMachine.valueType = Compiler.valueType from (funext value_type_eq_abs).symm,
      List.map_drop, height, shape, List.drop_left]
  rw [height] at args
  have resolved := block_signature_resolves f.module bt params results signature
  simp [SourceMachine.astep, SourceMachine.enterLabel, resolved, height, args, show params.length ≤ f.vals.length by omega, SourceMachine.advance]

theorem LabelsMatch.enter {values : List val} {labels : List SourceMachine.Label} {targets : List Compiler.LabelTarget}
    (outer : LabelsMatch values labels targets) (front params results branchTypes : List valtype)
    (branch : U32) (normalExit : Nat) (cont after : List instr) {normalLive branchLive : Bool}
    (shape : values.map Compiler.valueType = front ++ params) :
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

theorem loop_source_step (s : store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (bt : blocktype) (body after : List instr) (front params results : List valtype)
    (signature : Compiler.BlockSignature f.module.TYPES bt params results)
    (shape : f.vals.map Compiler.valueType = front ++ params) :
    SourceMachine.astep ⟨s, ambient, { f with code := .LOOP bt body :: after } :: rest, []⟩ =
      .next ⟨s, ambient, { f with code := body, labels := ⟨params, results, [.LOOP bt body], front.length, after⟩ :: f.labels } :: rest, []⟩ := by
  have size : f.vals.length = front.length + params.length := by
    simpa only [List.length_map, List.length_append] using congrArg List.length shape
  have height : f.vals.length - params.length = front.length := by omega
  have args : (f.vals.drop (f.vals.length - params.length)).map SourceMachine.valueType = params := by
    rw [show SourceMachine.valueType = Compiler.valueType from (funext value_type_eq_abs).symm,
      List.map_drop, height, shape, List.drop_left]
  rw [height] at args
  have resolved := block_signature_resolves f.module bt params results signature
  simp [SourceMachine.astep, SourceMachine.enterLabel, resolved, height, args, show params.length ≤ f.vals.length by omega, SourceMachine.advance]

end Itasca.Runtime.Interp
