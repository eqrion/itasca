import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupAlgebra
import Itasca.Runtime.Compiler.Local.Callbacks.Observation.Frame
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlLayout

/-! Canonical control-entry contracts. Inversion preserves allocator-independent
observations; totality and availability distinguish ordinary errors from
successful publication. The publication suffix is proved once for each mode. -/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

inductive SignatureAt (signatures : Slice runtime.compiler.Signature) :
    Itasca.signature.BlockType → runtime.compiler.Signature → Prop where
  | empty : SignatureAt signatures .Empty ⟨0#usize, 0#usize, 0#u32, 0#u32⟩
  | value (ty : Itasca.wasm_types.ValueType) (word : U32)
      (width : word.val = Compiler.width (Itasca.Translate.valueType ty)) :
      SignatureAt signatures (.Value ty) ⟨0#usize, 1#usize, 0#u32, word⟩
  | index (i : U32) (signature : runtime.compiler.Signature)
      (found : signatures.val[i.val]? = some signature) :
      SignatureAt signatures (.TypeIndex i) signature

@[step] theorem block_signature (signatures : Slice runtime.compiler.Signature)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature)
    (selected : SignatureAt signatures bt signature) :
    runtime.compiler.control.block_signature signatures bt ⦃ out => out = signature ⦄ := by
  cases selected with
  | empty => simp [runtime.compiler.control.block_signature, WP.spec_ok]
  | value ty word width =>
    unfold runtime.compiler.control.block_signature
    step with compiler_width ty as ⟨out, hout⟩
    have same : out = word := by apply UScalar.eq_of_val_eq; omega
    simp [same]
  | index i signature found =>
    unfold runtime.compiler.control.block_signature
    have bound := (List.getElem?_eq_some_iff.mp found).1
    step as ⟨index, hindex⟩
    step as ⟨out, hout⟩
    simpa [List.getElem?_eq_getElem bound, hindex, hout] using found

@[step] theorem charge_control {A : Type} (ops : runtime.platform.Alloc A)
    (budget : runtime.compiler.Budget A) :
    runtime.compiler.Budget.charge ops budget .Controls ⦃ out => True ⦄ := by
  simp only [runtime.compiler.Budget.charge]
  split
  · simp [runtime.compiler.Budget.reject.eq, WP.spec_ok]
  · step

/-- Instructions emitted before publishing a control frame. -/
def enterPrefix (reachable : Bool) (kind : Itasca.code.LabelKind) (condition : U32) :
    List runtime.bytecode.Instr :=
  match reachable, kind with
  | true, .Then => [.JumpIfZero condition core.num.U32.MAX]
  | true, .Loop => [.LoopHead]
  | _, _ => []

/-- Only a live IF retains a conditional-branch fixup location. -/
def enterIfPc (reachable : Bool) (kind : Itasca.code.LabelKind) (pc : Usize) : Option Usize :=
  match reachable, kind with
  | true, .Then => some pc
  | _, _ => none

/-- IF enters after its guard; LOOP enters at its emitted loop hook. -/
def enterPcAdvance (reachable : Bool) (kind : Itasca.code.LabelKind) : Nat :=
  match reachable, kind with
  | true, .Then => 1
  | _, _ => 0

/-- Entry changes work buffers, control publication and high-water marks only. -/
def EnterFrame {A : Type} (before after : runtime.compiler.FunctionCompiler A) : Prop :=
  after = {before with
    budget := after.budget, before := after.before,
    height := after.height, next_source := after.next_source, frames := after.frames,
    function := {before.function with
      code := after.function.code,
      source_offsets := after.function.source_offsets, controls := after.function.controls,
      max_stack := after.function.max_stack, slot_count := after.function.slot_count}}

/-- Successful publication before the final operand observation. -/
structure EnterPublished {A : Type} (before middle : runtime.compiler.FunctionCompiler A)
    (kind : Itasca.code.LabelKind) (ctrl : Itasca.code.Ctrl)
    (signature : runtime.compiler.Signature)
    (height startPc condition : U32) (source : Usize) : Prop where
  frame : middle = {before with
    budget := middle.budget, frames := middle.frames,
    function := {before.function with
      code := middle.function.code,
      source_offsets := middle.function.source_offsets, controls := middle.function.controls}}
  code : middle.function.code.val =
    before.function.code.val ++ enterPrefix before.reachable kind condition
  sources : middle.function.source_offsets.val.map (fun word => word.val) =
    before.function.source_offsets.val.map (fun word => word.val) ++
      (enterPrefix before.reachable kind condition).map
        (fun _ => before.function.body_start.val + before.next_source.val)
  start : startPc.val = before.function.code.val.length + enterPcAdvance before.reachable kind
  controls : middle.function.controls.val = before.function.controls.val ++
    [⟨kind, source, 0#usize, UScalar.cast .Usize startPc, 0#usize,
      ctrl.value_stack_base, signature.params, signature.results⟩]
  frames : middle.frames.val = before.frames.val ++
    [⟨alloc.vec.Vec.len before.function.controls, kind, height, signature.param_slots,
      signature.result_slots, startPc,
      enterIfPc before.reachable kind (alloc.vec.Vec.len before.function.code),
      before.reachable, false, alloc.vec.Vec.new Usize⟩]
  limits : middle.budget.limits = before.budget.limits
  error : middle.budget.error = before.budget.error
  charged : middle.budget.controls.val = before.budget.controls.val + 1
  instructions : middle.budget.instructions.val = before.budget.instructions.val +
    (enterPrefix before.reachable kind condition).length
  branches : middle.budget.branches = before.budget.branches
  locals : middle.budget.locals = before.budget.locals

/-- The raw arithmetic and final observation remain available without allocator
laws; exact publication is conditional on allocator correctness. -/
def Entered {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType) : Prop :=
  ∃ prior ctrl signature height startPc condition source middle,
    state.ctrls.val = prior ++ [ctrl] ∧
    runtime.compiler.control.block_signature before.signatures bt = .ok signature ∧
    runtime.compiler.control.stack_height state.vals.deref ctrl.value_stack_base
      before.function.local_slots = .ok height ∧
    source.val = before.function.body_start.val + before.next_source.val ∧
    (before.reachable = true → kind = .Then →
      runtime.compiler.FunctionCompiler.operand ops before 1#usize = .ok (.Ok condition)) ∧
    (Platform.AllocCorrect ops → EnterPublished before middle kind ctrl signature height startPc condition source) ∧
    runtime.compiler.FunctionCompiler.observe ops middle state = .ok (.Ok (), after)

/-- Source control and signature evidence shared by totality and availability. -/
def EnterInputs {A : Type} (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType) : Prop :=
  ∃ prior ctrl signature,
    state.ctrls.val = prior ++ [ctrl] ∧ SignatureAt before.signatures bt signature ∧
    ctrl.value_stack_base.val ≤ state.vals.val.length

/-- Totality needs a representable height only for the actual final control. -/
def EnterTotalInputs {A : Type} (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType) : Prop :=
  ∃ prior ctrl signature,
    state.ctrls.val = prior ++ [ctrl] ∧ SignatureAt before.signatures bt signature ∧
    ctrl.value_stack_base.val ≤ state.vals.val.length ∧
    before.function.local_slots.val + stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max

/-- Checked arithmetic and append capacity required for a normal entry return.
Only live instruction-emitting prefixes need code and source-vector space. -/
structure EnterTotalBounds {A : Type} (before : runtime.compiler.FunctionCompiler A)
    (kind : Itasca.code.LabelKind) : Prop where
  pc : before.function.code.val.length ≤ U32.max
  thenPc : before.reachable = true → kind = .Then → before.function.code.val.length + 1 ≤ U32.max
  coordinate : before.function.body_start.val + before.next_source.val ≤ Usize.max
  maps : before.function.controls.val.length < Usize.max
  frames : before.frames.val.length < Usize.max
  emission : before.reachable = true → (kind = .Then ∨ kind = .Loop) →
    before.function.code.val.length < Usize.max ∧ before.function.source_offsets.val.length < Usize.max

/-- Numeric requirements for successful entry. Emission requirements apply only
when the selected live prefix emits an instruction. -/
structure EnterDemand {A : Type} (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind) (bound : Nat) : Prop where
  pc : before.function.code.length ≤ U32.max
  thenPc : before.reachable = true → kind = .Then → before.function.code.length + 1 ≤ U32.max
  coordinate : before.function.body_start.val + before.next_source.val ≤ Usize.max
  mapsCapacity : before.function.controls.length < Usize.max
  mapsReserve : before.function.controls.length + 1 ≤ bound
  framesCapacity : before.frames.length < Usize.max
  framesReserve : before.frames.length + 1 ≤ bound
  control : before.budget.controls.val < before.budget.limits.max_controls.val
  operands : state.vals.length ≤ bound
  slots : before.function.local_slots.val + 2 * state.vals.length ≤ U32.max
  emission : before.reachable = true → (kind = .Then ∨ kind = .Loop) →
    before.function.code.length < Usize.max ∧
    before.function.source_offsets.length < Usize.max ∧
    before.function.code.length + 1 ≤ bound ∧
    before.function.source_offsets.length + 1 ≤ bound ∧
    before.budget.instructions.val < before.budget.limits.max_instructions.val

/-- Number of instruction charges in the selected entry prefix. -/
def enterInstructionCharge (reachable : Bool) (kind : Itasca.code.LabelKind) : Nat :=
  match reachable, kind with
  | true, .Then | true, .Loop => 1
  | _, _ => 0

/-- Exact budget effect of successful entry, including the dormant case. -/
def EnterBudget {A : Type} (before after : runtime.compiler.FunctionCompiler A)
    (kind : Itasca.code.LabelKind) : Prop :=
  ∃ instructions controls,
    after.budget = {before.budget with instructions, controls} ∧
    instructions.val = before.budget.instructions.val +
      enterInstructionCharge before.reachable kind ∧
    controls.val = before.budget.controls.val + 1

/-- The successful prologue identifies the final source control without
assuming a previously supplied source-control decomposition. -/
theorem enter_last_control (state : Itasca.code.OpIterState) (index : Usize)
    (ctrl : Itasca.code.Ctrl)
    (subtracted : (alloc.vec.Vec.len state.ctrls - 1#usize : Result Usize) = .ok index)
    (read : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Itasca.code.Ctrl)
      state.ctrls index = .ok ctrl) :
    ∃ prior, state.ctrls.val = prior ++ [ctrl] := by
  have subSpec := UScalar.sub_equiv (alloc.vec.Vec.len state.ctrls) 1#usize
  simp only [subtracted] at subSpec
  have lengthEq : state.ctrls.val.length = index.val + 1 := by
    have arithmetic := subSpec.2.1
    scalar_tac
  have indexBound : index.val < state.ctrls.val.length := by omega
  have atIndex : state.ctrls.val[index.val]? = some ctrl := by
    have indexSpec : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Itasca.code.Ctrl)
        state.ctrls index ⦃ value => state.ctrls.val[index.val]? = some value ⦄ := by
      step as ⟨value, found⟩
      exact (List.getElem?_eq_some_iff.mpr ⟨indexBound, found.symm⟩)
    rw [read, WP.spec_ok] at indexSpec
    exact indexSpec
  exact ⟨state.ctrls.val.take index.val, by
    have split := List.take_append_drop index.val state.ctrls.val
    rw [List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.mp atIndex).1,
      (List.getElem?_eq_some_iff.mp atIndex).2] at split
    have dropNil : state.ctrls.val.drop (index.val + 1) = [] :=
      List.drop_eq_nil_iff.mpr (by omega)
    simpa only [dropNil] using split.symm⟩

/-- Exact effect of the optional instruction prefix, before publication. -/
def EnterEmissionPrefix {A : Type} (before middle : runtime.compiler.FunctionCompiler A)
    (kind : Itasca.code.LabelKind) (condition : U32) : Prop :=
  ∃ used code sources,
    middle = {before with
      budget := {before.budget with instructions := used},
      function := {before.function with code, source_offsets := sources}} ∧
    used.val = before.budget.instructions.val + enterInstructionCharge before.reachable kind ∧
    code.val = before.function.code.val ++ enterPrefix before.reachable kind condition ∧
    sources.val.map (fun word => word.val) = before.function.source_offsets.val.map (fun word => word.val) ++
      (enterPrefix before.reachable kind condition).map
        (fun _ => before.function.body_start.val + before.next_source.val)

/-- Logical evidence for the three successful publication operations. This is
an effect relation, not a second implementation of the extracted suffix. -/
def PublicationCalls {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A)
    (map : runtime.compiler.ControlMap) (frame : runtime.compiler.Frame) : Prop :=
  ∃ charged mapBudget finalBudget maps frames,
    runtime.compiler.Budget.charge ops before.budget .Controls = .ok (.Ok (), charged) ∧
    runtime.compiler.Budget.push ops charged before.function.controls map = .ok (.Ok (), mapBudget, maps) ∧
    runtime.compiler.Budget.push ops mapBudget before.frames frame = .ok (.Ok (), finalBudget, frames) ∧
    after = {before with
      budget := finalBudget, function := {before.function with controls := maps}, frames}

/-- Publication charges one control and appends exactly its map and frame. -/
def PublishedSuffix {A : Type} (before after : runtime.compiler.FunctionCompiler A)
    (map : runtime.compiler.ControlMap) (frame : runtime.compiler.Frame) : Prop :=
  ∃ used maps frames,
    after = {before with
      budget := {before.budget with controls := used},
      function := {before.function with controls := maps}, frames} ∧
    used.val = before.budget.controls.val + 1 ∧
    maps.val = before.function.controls.val ++ [map] ∧
    frames.val = before.frames.val ++ [frame]

theorem charge_control_exact {A : Type} (ops : runtime.platform.Alloc A)
    (budget : runtime.compiler.Budget A) :
    runtime.compiler.Budget.charge ops budget .Controls ⦃ (status, after) =>
      status = .Ok () → ∃ used, after = {budget with controls := used} ∧
        used.val = budget.controls.val + 1 ⦄ := by
  simp only [runtime.compiler.Budget.charge]
  split
  · simp only [runtime.compiler.Budget.reject.eq, bind_ok, WP.spec_ok, uncurry_apply_pair,
      reduceCtorEq, false_implies]
  · step as ⟨used, added⟩
    intro _
    exact ⟨used, rfl, added⟩

/-- Shared success reasoning for every entry prefix: combine the actual charge
and push calls once, without unfolding the entry body again. -/
theorem publication_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A)
    (map : runtime.compiler.ControlMap) (frame : runtime.compiler.Frame)
    (calls : PublicationCalls ops before after map frame) :
    PublishedSuffix before after map frame := by
  obtain ⟨charged, mapBudget, finalBudget, maps, frames, chargeRun, mapRun, frameRun, rfl⟩ := calls
  have chargedEffect := charge_control_exact ops before.budget
  rw [chargeRun, WP.spec_ok] at chargedEffect
  obtain ⟨used, rfl, added⟩ := chargedEffect rfl
  obtain ⟨rfl, mapsEq⟩ := budget_push_success ops law _ mapBudget _ maps map mapRun
  obtain ⟨rfl, framesEq⟩ := budget_push_success ops law _ finalBudget _ frames frame frameRun
  exact ⟨used, maps, frames, rfl, added, mapsEq, framesEq⟩

theorem EnterFrame.trans {A : Type} {before middle after : runtime.compiler.FunctionCompiler A}
    (first : EnterFrame before middle) (second : EnterFrame middle after) : EnterFrame before after := by
  unfold EnterFrame at first second ⊢
  rw [first] at second
  exact second

theorem EmitFrame.enter_frame {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (frame : EmitFrame before after) : EnterFrame before after := by
  unfold EmitFrame at frame
  unfold EnterFrame
  rw [frame]

theorem ObserveFrame.enter_frame {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (frame : ObserveFrame before after) : EnterFrame before after := by
  unfold ObserveFrame at frame
  unfold EnterFrame
  rw [frame]

/-- Compose the optional emission with the single shared publication effect. -/
theorem EnterEmissionPrefix.publish {A : Type} {before prefixed middle : runtime.compiler.FunctionCompiler A}
    {kind : Itasca.code.LabelKind} {ctrl : Itasca.code.Ctrl} {signature : runtime.compiler.Signature}
    {height startPc condition : U32} {source : Usize}
    (entryPrefix : EnterEmissionPrefix before prefixed kind condition)
    (position : startPc.val = before.function.code.val.length + enterPcAdvance before.reachable kind)
    (publication : PublishedSuffix prefixed middle
      ⟨kind, source, 0#usize, UScalar.cast .Usize startPc, 0#usize,
        ctrl.value_stack_base, signature.params, signature.results⟩
      ⟨alloc.vec.Vec.len before.function.controls, kind, height, signature.param_slots,
        signature.result_slots, startPc, enterIfPc before.reachable kind (alloc.vec.Vec.len before.function.code),
        before.reachable, false, alloc.vec.Vec.new Usize⟩) :
    EnterPublished before middle kind ctrl signature height startPc condition source := by
  obtain ⟨instructions, code, sources, rfl, chargedInstructions, codeEq, sourceEq⟩ := entryPrefix
  obtain ⟨controls, maps, frames, rfl, chargedControls, mapsEq, framesEq⟩ := publication
  refine ⟨rfl, codeEq, sourceEq, position, mapsEq, framesEq, rfl, rfl, chargedControls, ?_, rfl, rfl⟩
  convert chargedInstructions using 1
  cases before.reachable <;> cases kind <;> rfl

theorem EnterEmissionPrefix.none {A : Type} (before : runtime.compiler.FunctionCompiler A)
    (kind : Itasca.code.LabelKind) (condition : U32)
    (none : enterInstructionCharge before.reachable kind = 0) :
    EnterEmissionPrefix before before kind condition := by
  refine ⟨before.budget.instructions, before.function.code, before.function.source_offsets,
    rfl, ?_, ?_, ?_⟩
  · rw [none, Nat.add_zero]
  · have noCode : enterPrefix before.reachable kind condition = [] := by
      cases active : before.reachable <;> cases kind <;>
        simp only [active, enterInstructionCharge, enterPrefix, Nat.one_ne_zero] at none ⊢
    rw [noCode, List.append_nil]
  · have noCode : enterPrefix before.reachable kind condition = [] := by
      cases active : before.reachable <;> cases kind <;>
        simp only [active, enterInstructionCharge, enterPrefix, Nat.one_ne_zero] at none ⊢
    rw [noCode, List.map_nil, List.append_nil]

theorem EnterEmissionPrefix.then {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {condition : U32} (live : before.reachable = true)
    (emitted : EmittedExact before after (.JumpIfZero condition core.num.U32.MAX)) :
    EnterEmissionPrefix before after .Then condition := by
  obtain ⟨used, code, sources, rfl, charged, codeEq, sourceEq⟩ := emitted
  exact ⟨used, code, sources, rfl, by simpa only [live, enterInstructionCharge] using charged,
    by simpa only [live, enterPrefix] using codeEq,
    by simpa only [live, enterPrefix, List.map_cons, List.map_nil] using sourceEq⟩

theorem EnterEmissionPrefix.loop {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (condition : U32) (live : before.reachable = true)
    (emitted : EmittedExact before after .LoopHead) :
    EnterEmissionPrefix before after .Loop condition := by
  obtain ⟨used, code, sources, rfl, charged, codeEq, sourceEq⟩ := emitted
  exact ⟨used, code, sources, rfl, by simpa only [live, enterInstructionCharge] using charged,
    by simpa only [live, enterPrefix] using codeEq,
    by simpa only [live, enterPrefix, List.map_cons, List.map_nil] using sourceEq⟩

/-- Successful PC conversion returns the same compiler, with no allocator law. -/
theorem enter_pc_success {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (pc : U32)
    (called : runtime.compiler.FunctionCompiler.pc ops before = .ok (.Ok pc, after)) :
    after = before ∧ pc.val = before.function.code.val.length := by
  have effect := compiler_pc ops before
  rw [called, WP.spec_ok] at effect
  have position := effect.2.1 pc rfl
  have bounded : before.function.code.length ≤ U32.max := by scalar_tac
  have available := compiler_pc_available ops before bounded
  rw [called, WP.spec_ok] at available
  exact ⟨available.1, position⟩

/-- The shared suffix preserves the entry frame on every normal return and
records actual publication calls on success. -/
def PublicationOutcome {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (map : runtime.compiler.ControlMap) (frame : runtime.compiler.Frame)
    (status : core.result.Result Unit Itasca.error.VisitError) : Prop :=
  EnterFrame before after ∧
    (Platform.AllocCorrect ops → before.function.slot_count.val ≤ after.function.slot_count.val) ∧
    (status = .Ok () → ∃ middle, PublicationCalls ops before middle map frame ∧
      runtime.compiler.FunctionCompiler.observe ops middle state = .ok (.Ok (), after))

theorem publication_inv {A : Type} (ops : runtime.platform.Alloc A)
    (observeFrame : ∀ before after state status,
      runtime.compiler.FunctionCompiler.observe ops before state = .ok (status, after) →
      ObserveFrame before after)
    (observeMono : ∀ before after state status, Platform.AllocCorrect ops →
      runtime.compiler.FunctionCompiler.observe ops before state = .ok (status, after) →
      before.function.slot_count.val ≤ after.function.slot_count.val)
    (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (map : runtime.compiler.ControlMap) (frame : runtime.compiler.Frame)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (called : (do
      let (charged, budget) ← runtime.compiler.Budget.charge ops before.budget .Controls
      let flow ← core.result.Result.Insts.CoreOpsTry.branch charged
      match flow with
      | .Continue _ =>
        let (pushed, mapBudget, maps) ← runtime.compiler.Budget.push ops budget before.function.controls map
        let flow ← core.result.Result.Insts.CoreOpsTry.branch pushed
        match flow with
        | .Continue _ =>
          let (pushed, finalBudget, frames) ← runtime.compiler.Budget.push ops mapBudget before.frames frame
          let flow ← core.result.Result.Insts.CoreOpsTry.branch pushed
          match flow with
          | .Continue _ => runtime.compiler.FunctionCompiler.observe ops {before with budget := finalBudget, function := {before.function with controls := maps}, frames} state
          | .Break residual =>
            let rejected ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame Itasca.error.VisitError) residual
            Result.ok (rejected, {before with budget := finalBudget, function := {before.function with controls := maps}, frames})
        | .Break residual =>
          let rejected ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame Itasca.error.VisitError) residual
          Result.ok (rejected, {before with budget := mapBudget, function := {before.function with controls := maps}})
      | .Break residual =>
        let rejected ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame Itasca.error.VisitError) residual
        Result.ok (rejected, {before with budget})) = .ok (status, after)) :
    PublicationOutcome ops before after state map frame status := by
  obtain ⟨⟨charged, budget⟩, chargeRun, rest⟩ := bind_ok_inv _ _ _ called
  cases charged with
  | Err error =>
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
    obtain ⟨rfl, rfl⟩ := rest
    exact ⟨rfl, fun _ => Nat.le_refl _, fun rejected => by cases rejected⟩
  | Ok value =>
    cases value
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok, uncurry_apply_pair] at rest
    obtain ⟨⟨pushed, mapBudget, maps⟩, mapRun, next⟩ := bind_ok_inv _ _ _ rest
    clear rest
    rename' next => rest
    cases pushed with
    | Err error =>
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
      obtain ⟨rfl, rfl⟩ := rest
      exact ⟨rfl, fun _ => Nat.le_refl _, fun rejected => by cases rejected⟩
    | Ok value =>
      cases value
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok, uncurry_apply_pair] at rest
      obtain ⟨⟨pushed, finalBudget, frames⟩, frameRun, next⟩ := bind_ok_inv _ _ _ rest
      clear rest
      rename' next => rest
      cases pushed with
      | Err error =>
        simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
        obtain ⟨rfl, rfl⟩ := rest
        exact ⟨rfl, fun _ => Nat.le_refl _, fun rejected => by cases rejected⟩
      | Ok value =>
        cases value
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok, uncurry_apply_pair] at rest
        let middle := {before with budget := finalBudget, function := {before.function with controls := maps}, frames}
        have observedFrame := (observeFrame middle after state status rest).enter_frame
        have publishedFrame : EnterFrame before middle := rfl
        refine ⟨publishedFrame.trans observedFrame, ?_, ?_⟩
        · intro law
          exact observeMono middle after state status law rest
        · intro accepted
          subst status
          exact ⟨middle, ⟨budget, mapBudget, finalBudget, maps, frames, chargeRun, mapRun, frameRun, rfl⟩, rest⟩

/-- Facts established by a prefix before the common publication suffix. -/
structure EntryReady {A : Type} (ops : runtime.platform.Alloc A)
    (before prefixed : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType) where
  prior : List Itasca.code.Ctrl
  ctrl : Itasca.code.Ctrl
  signature : runtime.compiler.Signature
  height : U32
  startPc : U32
  condition : U32
  source : Usize
  controls : state.ctrls.val = prior ++ [ctrl]
  selected : runtime.compiler.control.block_signature before.signatures bt = .ok signature
  heightRun : runtime.compiler.control.stack_height state.vals.deref ctrl.value_stack_base
    before.function.local_slots = .ok height
  sourceEq : source.val = before.function.body_start.val + before.next_source.val
  operand : before.reachable = true → kind = .Then →
    runtime.compiler.FunctionCompiler.operand ops before 1#usize = .ok (.Ok condition)
  frame : EmitFrame before prefixed
  entryPrefix : Platform.AllocCorrect ops → EnterEmissionPrefix before prefixed kind condition
  position : Platform.AllocCorrect ops →
    startPc.val = before.function.code.val.length + enterPcAdvance before.reachable kind

def EntryReady.map {A : Type} {ops : runtime.platform.Alloc A}
    {before prefixed : runtime.compiler.FunctionCompiler A} {state : Itasca.code.OpIterState}
    {kind : Itasca.code.LabelKind} {bt : Itasca.signature.BlockType}
    (ready : EntryReady ops before prefixed state kind bt) : runtime.compiler.ControlMap :=
  ⟨kind, ready.source, 0#usize, UScalar.cast .Usize ready.startPc, 0#usize,
    ready.ctrl.value_stack_base, ready.signature.params, ready.signature.results⟩

def EntryReady.controlFrame {A : Type} {ops : runtime.platform.Alloc A}
    {before prefixed : runtime.compiler.FunctionCompiler A} {state : Itasca.code.OpIterState}
    {kind : Itasca.code.LabelKind} {bt : Itasca.signature.BlockType}
    (ready : EntryReady ops before prefixed state kind bt) : runtime.compiler.Frame :=
  ⟨alloc.vec.Vec.len before.function.controls, kind, ready.height, ready.signature.param_slots,
    ready.signature.result_slots, ready.startPc,
    enterIfPc before.reachable kind (alloc.vec.Vec.len before.function.code),
    before.reachable, false, alloc.vec.Vec.new Usize⟩

theorem EntryReady.finish {A : Type} {ops : runtime.platform.Alloc A}
    {before prefixed after : runtime.compiler.FunctionCompiler A} {state : Itasca.code.OpIterState}
    {kind : Itasca.code.LabelKind} {bt : Itasca.signature.BlockType}
    (ready : EntryReady ops before prefixed state kind bt)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (published : PublicationOutcome ops prefixed after state ready.map ready.controlFrame status) :
    EnterFrame before after ∧
      (Platform.AllocCorrect ops → before.function.slot_count.val ≤ after.function.slot_count.val) ∧
      (status = .Ok () → Entered ops before after state kind bt) := by
  refine ⟨ready.frame.enter_frame.trans published.1, ?_, ?_⟩
  · intro law
    have capacity := published.2.1 law
    have frame := ready.frame
    unfold EmitFrame at frame
    rw [frame] at capacity
    exact capacity
  · intro accepted
    obtain ⟨middle, calls, observed⟩ := published.2.2 accepted
    refine ⟨ready.prior, ready.ctrl, ready.signature, ready.height, ready.startPc,
      ready.condition, ready.source, middle, ready.controls, ready.selected,
      ready.heightRun, ready.sourceEq, ready.operand, ?_, observed⟩
    intro law
    exact (ready.entryPrefix law).publish (ready.position law)
      (publication_success ops law prefixed middle ready.map ready.controlFrame calls)

/-- An early Rust error needs only the unconditional prefix frame. -/
theorem enter_failed {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (error : Itasca.error.VisitError) (frame : EmitFrame before after) :
    EnterFrame before after ∧
      (Platform.AllocCorrect ops → before.function.slot_count.val ≤ after.function.slot_count.val) ∧
      (core.result.Result.Err error = (.Ok () : core.result.Result Unit Itasca.error.VisitError) →
        Entered ops before after state kind bt) := by
  refine ⟨frame.enter_frame, ?_, fun impossible => by cases impossible⟩
  intro _
  unfold EmitFrame at frame
  rw [frame]

theorem publication_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (kind : Itasca.code.LabelKind) (signature : runtime.compiler.Signature)
    (height : U32) (sourceStart valueHeight : Usize) (startPc : U32) (ifPc : Option Usize)
    (mapsCapacity : before.function.controls.length < Usize.max)
    (framesCapacity : before.frames.length < Usize.max) :
    (do
  let map := alloc.vec.Vec.len before.function.controls
  let (r4, b) ←
    runtime.compiler.Budget.charge ops
      before.budget runtime.compiler.CompileResource.Controls
  let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
  match cf4 with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let i1 ← lift (UScalar.cast .Usize startPc)
    let (r5, b1, v) ←
      runtime.compiler.Budget.push ops b
        before.function.controls
        ({
           kind,
           source_start := sourceStart,
           source_end := 0#usize,
           start_pc := i1,
           end_pc := 0#usize,
           stack_height := valueHeight,
           parameters := signature.params,
           results := signature.results
         } : _root_.Itasca.runtime.compiler.ControlMap)
    let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
    match cf5 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let (r6, b2, v1) ←
        runtime.compiler.Budget.push ops b1
          before.frames
          ({
             map,
             kind,
             height,
             params := signature.param_slots,
             results := signature.result_slots,
             start_pc := startPc,
             if_pc := ifPc,
             entry_reachable := before.reachable,
             end_reachable := false,
             fixups := (alloc.vec.Vec.new Std.Usize)
           } : _root_.Itasca.runtime.compiler.Frame)
      let cf6 ←
        core.result.Result.Insts.CoreOpsTry.branch r6
      match cf6 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        runtime.compiler.FunctionCompiler.observe
          ops
          {
            before
              with
              budget := b2,
              function :=
                { before.function with controls := v },
              frames := v1
          } state
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r7 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame
            _root_.Itasca.error.VisitError) residual
        Result.ok (r7,
          {
            before
              with
              budget := b2,
              function :=
                { before.function with controls := v },
              frames := v1
          })
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r6 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame
          _root_.Itasca.error.VisitError) residual
      Result.ok (r6,
        {
          before
            with
            budget := b1,
            function := { before.function with controls := v }
        })
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r5 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame
        _root_.Itasca.error.VisitError) residual
    Result.ok (r5, { before with budget := b })) ⦃ _ => True ⦄ := by
  step with charge_control ops before.budget as ⟨charged, budget⟩
  cases charged with
  | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
  | Ok value =>
    cases value
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step as ⟨start, startEq⟩
    step with budget_push ops law budget before.function.controls _ mapsCapacity
      as ⟨result, mapBudget, maps, pushed⟩
    rcases pushed with ⟨rfl, rfl, appended⟩ | ⟨rfl, rfl, rejected⟩
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with budget_push ops law mapBudget before.frames _ framesCapacity
        as ⟨result, finalBudget, frames, pushed⟩
      rcases pushed with ⟨rfl, rfl, appended⟩ | ⟨rfl, rfl, rejected⟩
      · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        apply WP.spec_mono (compiler_observe ops law _ state)
        intro out post
        trivial
      · simp only [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
    · simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]

/-- Every normal entry return preserves its structural frame. Allocator
correctness gives slot-capacity monotonicity; success also exposes the actual
prologue, exact publication, and final observation. -/
theorem _root_.Itasca.runtime.compiler.control.FunctionCompiler.enter.inv {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.control.FunctionCompiler.enter ops before state kind bt = .ok (status, after)) :
    EnterFrame before after ∧
      (Platform.AllocCorrect ops → before.function.slot_count.val ≤ after.function.slot_count.val) ∧
      (status = .Ok () → Entered ops before after state kind bt) := by
  have observeFrame : ∀ before after state status,
      runtime.compiler.FunctionCompiler.observe ops before state = .ok (status, after) →
      ObserveFrame before after := by
    intro before after state status called
    exact compiler_observe_frame_raw ops before state status after called
  have observeMono : ∀ before after state status, Platform.AllocCorrect ops →
      runtime.compiler.FunctionCompiler.observe ops before state = .ok (status, after) →
      before.function.slot_count.val ≤ after.function.slot_count.val := by
    intro before after state status law called
    have effect := compiler_observe_inv ops law before state
    rw [called, WP.spec_ok] at effect
    exact effect.2
  unfold runtime.compiler.control.FunctionCompiler.enter at called
  by_cases empty : alloc.vec.Vec.len state.ctrls = 0#usize
  · simp only [empty, if_pos, Result.ok.injEq, Prod.mk.injEq] at called
    obtain ⟨rfl, rfl⟩ := called
    exact enter_failed ops before before state kind bt .OutOfMemory rfl
  · simp only [if_neg empty] at called
    obtain ⟨index, subtracted, rest⟩ := bind_ok_inv _ _ _ called
    clear called
    obtain ⟨ctrl, read, next⟩ := bind_ok_inv _ _ _ rest
    clear rest
    rename' next => rest
    obtain ⟨prior, controls⟩ := enter_last_control state index ctrl subtracted read
    obtain ⟨signature, selected, next⟩ := bind_ok_inv _ _ _ rest
    clear rest
    rename' next => rest
    obtain ⟨height, heightRun, next⟩ := bind_ok_inv _ _ _ rest
    clear rest
    rename' next => rest
    obtain ⟨source, sourceRun, next⟩ := bind_ok_inv _ _ _ rest
    clear rest
    rename' next => rest
    have sourceEq := control_add_success sourceRun
    cases active : before.reachable <;> cases kind <;>
      simp only [bind_ok, active, Bool.false_eq_true, ite_false, ite_true] at rest
    all_goals first
    | (obtain ⟨⟨pcResult, current⟩, pcRun, rest⟩ := bind_ok_inv _ _ _ rest
       have pcEffect := compiler_pc ops before
       rw [pcRun, WP.spec_ok] at pcEffect
       cases pcResult with
       | Err error =>
         obtain ⟨_, _, budget, same⟩ := pcEffect
         change current = {before with budget} at same
         subst current
         simp only [uncurry_apply_pair, entry_branch_bind, bind_ok,
           core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
           core.convert.FromSame.from, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
         obtain ⟨statusEq, afterEq⟩ := rest
         subst status
         subst after
         exact enter_failed ops before _ state _ bt error rfl
       | Ok pc =>
         obtain ⟨same, position⟩ := enter_pc_success ops before current pc pcRun
         subst current
         simp only [uncurry_apply_pair, entry_branch_bind, bind_ok,
           active, Bool.false_eq_true, ite_false, ite_true] at rest
         first
         | (
            refine EntryReady.finish (prefixed := before)
              {prior, ctrl, signature, height, startPc := pc, condition := 0#u32, source,
               controls, selected, heightRun, sourceEq, operand := ?_, frame := rfl,
               entryPrefix := ?_, position := ?_} status ?_
            · intro live isThen
              cases isThen <;> simp only [active, Bool.false_eq_true] at live
            · intro law
              apply EnterEmissionPrefix.none
              simp only [active, enterInstructionCharge]
            · intro law
              simpa only [active, enterPcAdvance, Nat.add_zero] using position
            · apply publication_inv ops observeFrame observeMono
              simpa only [EntryReady.map, EntryReady.controlFrame, active, enterIfPc,
                entry_branch_bind, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                core.convert.FromSame.from, bind_ok, bind_tc_ok, bind_tc_eq, entry_uncurry_eq, entry_uncurry_apply, entry_pair_match, uncurry_apply_pair, lift] using rest
           )
         | (
            obtain ⟨⟨emittedResult, emitted⟩, emitRun, next⟩ := bind_ok_inv _ _ _ rest
            clear rest
            rename' next => rest
            have emission := runtime.compiler.FunctionCompiler.emit.inv ops before emitted .LoopHead emittedResult emitRun
            cases emittedResult with
            | Err error =>
              simp only [uncurry_apply_pair, entry_branch_bind, bind_ok,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                core.convert.FromSame.from, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
              obtain ⟨statusEq, afterEq⟩ := rest
              subst status
              subst after
              exact enter_failed ops before emitted state .Loop bt error emission.1
            | Ok value =>
              cases value
              simp only [uncurry_apply_pair, entry_branch_bind, bind_ok] at rest
              have sameControls : emitted.function.controls = before.function.controls := by
                have frame := emission.1
                unfold EmitFrame at frame
                rw [frame]
              have sameReachable : emitted.reachable = before.reachable := by
                have frame := emission.1
                unfold EmitFrame at frame
                rw [frame]
              refine EntryReady.finish (prefixed := emitted)
                {prior, ctrl, signature, height, startPc := pc, condition := 0#u32, source,
                 controls, selected, heightRun, sourceEq, operand := ?_, frame := emission.1,
                 entryPrefix := ?_, position := ?_} status ?_
              · intro live isThen
                cases isThen
              · intro law
                exact EnterEmissionPrefix.loop 0#u32 active ((emission.2 law).2 rfl)
              · intro law
                simpa only [active, enterPcAdvance, Nat.add_zero] using position
              · apply publication_inv ops observeFrame observeMono
                simpa only [EntryReady.map, EntryReady.controlFrame, active, enterIfPc,
                  sameControls, sameReachable, entry_branch_bind,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                  core.convert.FromSame.from, bind_ok, bind_tc_ok, bind_tc_eq, entry_uncurry_eq, entry_uncurry_apply, entry_pair_match, uncurry_apply_pair, lift] using rest
           )
       )
    | skip
    all_goals first
    | (
      obtain ⟨conditionResult, operandRun, next⟩ := bind_ok_inv _ _ _ rest
      clear rest
      rename' next => rest
      cases conditionResult with
      | Err error =>
        simp only [entry_branch_bind, bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
        obtain ⟨statusEq, afterEq⟩ := rest
        subst status
        subst after
        exact enter_failed ops before before state .Then bt error rfl
      | Ok condition =>
        simp only [entry_branch_bind, bind_ok] at rest
        obtain ⟨⟨emittedResult, emitted⟩, emitRun, next⟩ := bind_ok_inv _ _ _ rest
        clear rest
        rename' next => rest
        have emission := runtime.compiler.FunctionCompiler.emit.inv ops before emitted
          (.JumpIfZero condition core.num.U32.MAX) emittedResult emitRun
        cases emittedResult with
        | Err error =>
          simp only [uncurry_apply_pair, entry_branch_bind, bind_ok,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
          obtain ⟨statusEq, afterEq⟩ := rest
          subst status
          subst after
          exact enter_failed ops before emitted state .Then bt error emission.1
        | Ok value =>
          cases value
          simp only [uncurry_apply_pair, entry_branch_bind, bind_ok] at rest
          obtain ⟨⟨pcResult, current⟩, pcRun, next⟩ := bind_ok_inv _ _ _ rest
          clear rest
          rename' next => rest
          have pcEffect := compiler_pc ops emitted
          rw [pcRun, WP.spec_ok] at pcEffect
          cases pcResult with
          | Err error =>
            obtain ⟨_, _, budget, same⟩ := pcEffect
            change current = {emitted with budget} at same
            subst current
            simp only [uncurry_apply_pair, entry_branch_bind, bind_ok,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              core.convert.FromSame.from, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
            obtain ⟨statusEq, afterEq⟩ := rest
            subst status
            subst after
            apply enter_failed ops before _ state .Then bt error
            have frame := emission.1
            unfold EmitFrame at frame ⊢
            rw [frame]
          | Ok pc =>
            obtain ⟨same, position⟩ := enter_pc_success ops emitted current pc pcRun
            subst current
            have sameControls : emitted.function.controls = before.function.controls := by
              have frame := emission.1
              unfold EmitFrame at frame
              rw [frame]
            have sameReachable : emitted.reachable = before.reachable := by
              have frame := emission.1
              unfold EmitFrame at frame
              rw [frame]
            simp only [uncurry_apply_pair, entry_branch_bind, bind_ok,
              sameReachable, active, ite_true, Bool.false_eq_true, ite_false] at rest
            refine EntryReady.finish (prefixed := emitted)
              {prior, ctrl, signature, height, startPc := pc, condition, source,
               controls, selected, heightRun, sourceEq, operand := fun _ _ => operandRun,
               frame := emission.1, entryPrefix := ?_, position := ?_} status ?_
            · intro law
              exact EnterEmissionPrefix.then active ((emission.2 law).2 rfl)
            · intro law
              obtain ⟨used, code, sources, same, charged, codeEq, sourceEq⟩ := (emission.2 law).2 rfl
              rw [same] at position
              simpa only [codeEq, List.length_append, List.length_singleton,
                active, enterPcAdvance] using position
            · apply publication_inv ops observeFrame observeMono
              simpa only [EntryReady.map, EntryReady.controlFrame, active, enterIfPc,
                sameControls, sameReachable, entry_branch_bind,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                core.convert.FromSame.from, bind_ok, bind_tc_ok, bind_tc_eq, entry_uncurry_eq, entry_uncurry_apply, entry_pair_match, uncurry_apply_pair, lift] using rest
      )
    | skip

/-- Checked bounds and allocator correctness exclude extracted failure. A live
IF with no condition operand instead returns normally without allocator laws. -/
theorem _root_.Itasca.runtime.compiler.control.FunctionCompiler.enter.total {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (inputs : EnterTotalInputs before state bt)
    (normal : (Platform.AllocCorrect ops ∧ EnterTotalBounds before kind) ∨
      (before.reachable = true ∧ kind = .Then ∧ before.before.val = [] ∧
        before.function.body_start.val + before.next_source.val ≤ Usize.max)) :
    runtime.compiler.control.FunctionCompiler.enter ops before state kind bt ⦃ _ => True ⦄ := by
  obtain ⟨prior, ctrl, signature, controls, selected, valuesFit, heightFits⟩ := inputs
  have nonempty : alloc.vec.Vec.len state.ctrls ≠ 0#usize := by
    intro same
    have lengthEq := congrArg UScalar.val same
    simp only [alloc.vec.Vec.len, controls, List.length_append, List.length_singleton] at lengthEq
    scalar_tac
  have coordinate : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
    rcases normal with ⟨_, bounds⟩ | ⟨_, _, _, fits⟩
    · exact bounds.coordinate
    · exact fits
  unfold runtime.compiler.control.FunctionCompiler.enter
  rw [if_neg nonempty]
  step as ⟨last, lastEq⟩
  have atLast : last.val = prior.length := by
    simp only [alloc.vec.Vec.len, controls, List.length_append, List.length_singleton] at lastEq
    scalar_tac
  step as ⟨actual, actualEq⟩
  have same : actual = ctrl := by
    simpa only [atLast, controls, List.getElem_concat_length] using actualEq
  rw [same]
  step with block_signature before.signatures bt signature selected as ⟨sig, sigEq⟩
  subst sig
  step with control_stack_height state.vals.deref ctrl.value_stack_base before.function.local_slots
    (by simpa only [alloc.vec.Vec.deref, Slice.from_val] using valuesFit)
    (by simpa only [alloc.vec.Vec.deref, Slice.from_val] using heightFits) as ⟨height, heightEq⟩
  step as ⟨source, sourceEq⟩
  rcases normal with ⟨law, bounds⟩ | ⟨live, rfl, empty, _⟩
  · cases active : before.reachable <;> cases kind
    all_goals simp only [bind_ok, active, Bool.false_eq_true, ite_false, ite_true]
    all_goals try (solve |
      step with compiler_pc_available ops before bounds.pc as ⟨status, first, same, pc, accepted, _⟩
      subst first
      rw [accepted]
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        Bool.false_eq_true, ite_false, ite_true, ite_self]
      first
      | exact publication_total ops law before state _ signature height source ctrl.value_stack_base pc none
          bounds.maps bounds.frames
      | (have inactive : before.reachable = false := active
         rw [if_neg (by simp only [inactive, Bool.false_eq_true, not_false_eq_true])]
         exact publication_total ops law before state _ signature height source ctrl.value_stack_base pc none
           bounds.maps bounds.frames)
    )
    case true.Then =>
      step with compiler_operand_total ops before 1#usize as ⟨operand, member⟩
      cases operand with
      | Err error =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
      | Ok condition =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        obtain ⟨codeFits, sourcesFit⟩ := bounds.emission active (Or.inl rfl)
        step with compiler_emit ops law before (.JumpIfZero condition core.num.U32.MAX)
          codeFits sourcesFit bounds.coordinate as ⟨status, emitted, effect⟩
        cases status with
        | Err error =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
        | Ok value =>
          cases value
          obtain ⟨budget, code, sources, frame, codeEq, _⟩ := effect rfl
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
          have emittedPc : emitted.function.code.length ≤ U32.max := by
            rw [frame]
            simpa only [alloc.vec.Vec.length, codeEq, List.length_append, List.length_singleton] using
              bounds.thenPc active rfl
          step with compiler_pc_available ops emitted emittedPc as ⟨status, first, same, pc, accepted, _⟩
          subst first
          rw [accepted]
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
            Bool.false_eq_true, ite_false, ite_self]
          exact publication_total ops law emitted state .Then signature height source ctrl.value_stack_base pc
            (some (alloc.vec.Vec.len before.function.code))
            (by simpa only [frame] using bounds.maps) (by simpa only [frame] using bounds.frames)
    case true.Loop =>
      step with compiler_pc_available ops before bounds.pc as ⟨status, first, same, pc, accepted, _⟩
      subst first
      rw [accepted]
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, active, ite_true]
      obtain ⟨codeFits, sourcesFit⟩ := bounds.emission active (Or.inr rfl)
      step with compiler_emit ops law before .LoopHead codeFits sourcesFit bounds.coordinate
        as ⟨status, emitted, effect⟩
      cases status with
      | Err error =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
      | Ok value =>
        cases value
        obtain ⟨budget, code, sources, frame, codeEq, _⟩ := effect rfl
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        exact publication_total ops law emitted state .Loop signature height source ctrl.value_stack_base pc none
          (by simpa only [frame] using bounds.maps) (by simpa only [frame] using bounds.frames)
  · simp only [bind_ok, live, Bool.false_eq_true, ite_false, ite_true]
    step with compiler_operand_total ops before 1#usize as ⟨operand, member⟩
    cases operand with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
    | Ok condition =>
      have impossible := member condition rfl
      simp only [empty, List.not_mem_nil] at impossible

theorem charge_control_available_exact {A : Type} (ops : runtime.platform.Alloc A)
    (budget : runtime.compiler.Budget A)
    (room : budget.controls.val < budget.limits.max_controls.val) :
    runtime.compiler.Budget.charge ops budget .Controls ⦃ (status, after) =>
      status = .Ok () ∧ ∃ used, after = {budget with controls := used} ∧
        used.val = budget.controls.val + 1 ⦄ := by
  have notFull : ¬budget.controls ≥ budget.limits.max_controls := by scalar_tac
  simp only [runtime.compiler.Budget.charge, if_neg notFull]
  step as ⟨used, added⟩
  exact ⟨used, rfl, added⟩

/-- Independent resources used by control publication and final observation. -/
structure PublicationDemand {A : Type} (before : runtime.compiler.FunctionCompiler A)
    (state : code.OpIterState) (bound : Nat) : Prop where
  control : before.budget.controls.val < before.budget.limits.max_controls.val
  mapsCapacity : before.function.controls.length < Usize.max
  mapsReserve : before.function.controls.length + 1 ≤ bound
  framesCapacity : before.frames.length < Usize.max
  framesReserve : before.frames.length + 1 ≤ bound
  operands : state.vals.length ≤ bound
  slots : before.function.local_slots.val + 2 * state.vals.length ≤ U32.max

/-- Independent reserve bounds make the publication suffix succeed. -/
theorem publication_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (before : runtime.compiler.FunctionCompiler A) (state : code.OpIterState)
    (kind : code.LabelKind) (signature : runtime.compiler.Signature)
    (height : U32) (sourceStart valueHeight : Usize) (startPc : U32) (ifPc : Option Usize)
    (demand : PublicationDemand before state bound) :
    (do
  let map := alloc.vec.Vec.len before.function.controls
  let (r4, b) ←
    runtime.compiler.Budget.charge ops
      before.budget runtime.compiler.CompileResource.Controls
  let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
  match cf4 with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let i1 ← lift (UScalar.cast .Usize startPc)
    let (r5, b1, v) ←
      runtime.compiler.Budget.push ops b
        before.function.controls
        ({
           kind,
           source_start := sourceStart,
           source_end := 0#usize,
           start_pc := i1,
           end_pc := 0#usize,
           stack_height := valueHeight,
           parameters := signature.params,
           results := signature.results
         } : _root_.Itasca.runtime.compiler.ControlMap)
    let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
    match cf5 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let (r6, b2, v1) ←
        runtime.compiler.Budget.push ops b1
          before.frames
          ({
             map,
             kind,
             height,
             params := signature.param_slots,
             results := signature.result_slots,
             start_pc := startPc,
             if_pc := ifPc,
             entry_reachable := before.reachable,
             end_reachable := false,
             fixups := (alloc.vec.Vec.new Std.Usize)
           } : _root_.Itasca.runtime.compiler.Frame)
      let cf6 ←
        core.result.Result.Insts.CoreOpsTry.branch r6
      match cf6 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        runtime.compiler.FunctionCompiler.observe
          ops
          {
            before
              with
              budget := b2,
              function :=
                { before.function with controls := v },
              frames := v1
          } state
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r7 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame
            _root_.Itasca.error.VisitError) residual
        Result.ok (r7,
          {
            before
              with
              budget := b2,
              function :=
                { before.function with controls := v },
              frames := v1
          })
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r6 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame
          _root_.Itasca.error.VisitError) residual
      Result.ok (r6,
        {
          before
            with
            budget := b1,
            function := { before.function with controls := v }
        })
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r5 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame
        _root_.Itasca.error.VisitError) residual
    Result.ok (r5, { before with budget := b }))
      ⦃ (status, after) => status = .Ok () ∧ ∃ used,
        after.budget = {before.budget with controls := used} ∧
        used.val = before.budget.controls.val + 1 ⦄ := by
  step with charge_control_available_exact ops before.budget demand.control
    as ⟨status, budget, accepted, used, same, usedEq⟩
  subst status budget
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step as ⟨start, startEq⟩
  step with budget_push_available ops bound available {before.budget with controls := used}
    before.function.controls
    ⟨kind,sourceStart,0#usize,start,0#usize,valueHeight,signature.params,signature.results⟩
    demand.mapsCapacity demand.mapsReserve as ⟨status, budget, maps, accepted, same, appended⟩
  subst status budget
  simp only [bind_ok]
  step with budget_push_available ops bound available {before.budget with controls := used}
    before.frames
    ⟨alloc.vec.Vec.len before.function.controls,kind,height,signature.param_slots,
      signature.result_slots,startPc,ifPc,before.reachable,false,alloc.vec.Vec.new Usize⟩
    demand.framesCapacity demand.framesReserve as ⟨status, budget, frames, accepted, same, appended⟩
  subst status budget
  simp only [bind_ok]
  apply WP.spec_mono (compiler_observe_available_budget ops bound available
    {before with
      budget := {before.budget with controls := used},
      function := {before.function with controls := maps}, frames} state demand.operands demand.slots)
  intro out post
  exact ⟨post.1, used, post.2, usedEq⟩

/-- Every raw observed stack entry occupies at most two compiler words. -/
theorem stack_words_le_twice_length (values : List Itasca.code.StackType) :
    stackWords values ≤ 2*values.length := by
  induction values with
  | nil => simp [stackWords]
  | cons value rest ih =>
    have widthBound : compilerStackWidth value ≤ 2 := by
      cases value with
      | Bot => decide
      | Val ty => cases ty <;> decide
    simp only [stackWords,List.map_cons,List.sum_cons,List.length_cons] at ih ⊢
    omega

theorem _root_.Itasca.runtime.compiler.control.FunctionCompiler.enter.available {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat)
    (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : code.OpIterState)
    (kind : code.LabelKind) (bt : Itasca.signature.BlockType)
    (inputs : EnterInputs compiler state bt) (demand : EnterDemand compiler state kind bound)
    (operand : compiler.reachable = true → kind = .Then →
      ∃ condition, runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok condition)) :
    runtime.compiler.control.FunctionCompiler.enter ops compiler state kind bt ⦃ (status, after) =>
      status = .Ok () ∧ EnterBudget compiler after kind ⦄ := by
  obtain ⟨prior, ctrl, signature, controls, selected, valuesFit⟩ := inputs
  have heightFits : compiler.function.local_slots.val +
      stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max := by
    have words := stack_words_le_twice_length (state.vals.val.take ctrl.value_stack_base.val)
    have lengthBound : (state.vals.val.take ctrl.value_stack_base.val).length ≤ state.vals.val.length := by
      simp only [List.length_take]; exact Nat.min_le_right _ _
    have room := demand.slots
    simp only [alloc.vec.Vec.length] at room
    omega
  have nonempty : alloc.vec.Vec.len state.ctrls ≠ 0#usize := by
    intro same
    have lengthEq := congrArg UScalar.val same
    simp [alloc.vec.Vec.len, controls] at lengthEq
  unfold runtime.compiler.control.FunctionCompiler.enter
  rw [if_neg nonempty]
  step as ⟨last, hlast⟩
  have atLast : last.val = prior.length := by simp [alloc.vec.Vec.len, controls] at hlast; omega
  step as ⟨actual, hactual⟩
  have actualEq : actual = ctrl := by simpa [atLast, controls] using hactual
  rw [actualEq]
  step with block_signature compiler.signatures bt signature selected as ⟨sig, hsig⟩
  subst sig
  step with control_stack_height state.vals.deref ctrl.value_stack_base compiler.function.local_slots
    (by simpa [alloc.vec.Vec.deref] using valuesFit)
    (by simpa [alloc.vec.Vec.deref] using heightFits) as ⟨height, hheight⟩
  have coordinate := demand.coordinate
  step as ⟨source, hsource⟩
  cases active : compiler.reachable <;> cases kind
  all_goals simp only [bind_ok, active, Bool.false_eq_true, ite_false, ite_true]
  all_goals try
    step with compiler_pc_available ops compiler demand.pc as ⟨status, first, same, pc, accepted, _⟩
    subst first
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      Bool.false_eq_true, ite_false, ite_true, ite_self]
    try rw [if_neg (by simp [active])]
    apply WP.spec_mono (publication_available ops bound available compiler state _ signature height
      source ctrl.value_stack_base pc none ⟨demand.control, demand.mapsCapacity, demand.mapsReserve,
      demand.framesCapacity, demand.framesReserve, demand.operands, demand.slots⟩)
    intro out post
    obtain ⟨accepted, used, same, added⟩ := post
    refine ⟨accepted, compiler.budget.instructions, used, ?_, ?_, added⟩
    · simpa using same
    · simp [enterInstructionCharge, active]
  case true.Then =>
    obtain ⟨condition, read⟩ := operand active rfl
    rw [read]
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    obtain ⟨codeFits, sourcesFit, codeReserve, sourceReserve, instructionRoom⟩ :=
      demand.emission active (Or.inl rfl)
    step with runtime.compiler.FunctionCompiler.emit.available ops bound available compiler
      (.JumpIfZero condition core.num.U32.MAX) demand.pc codeFits sourcesFit codeReserve sourceReserve
      demand.coordinate instructionRoom
      as ⟨status, emitted, accepted, effect⟩
    obtain ⟨used, code, sources, frame, usedEq, codeAppend, _⟩ := effect
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    have emittedPc : emitted.function.code.length ≤ U32.max := by
      rw [frame]
      simpa [alloc.vec.Vec.length, codeAppend] using demand.thenPc active rfl
    step with compiler_pc_available ops emitted emittedPc as ⟨status, first, same, pc, accepted, _⟩
    subst first
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Bool.false_eq_true, ite_false, ite_self]
    apply WP.spec_mono (publication_available ops bound available emitted state .Then signature height
      source ctrl.value_stack_base pc (some (alloc.vec.Vec.len compiler.function.code))
      ⟨(by simpa [frame] using demand.control),
      (by simpa [frame] using demand.mapsCapacity), (by simpa [frame] using demand.mapsReserve),
      (by simpa [frame] using demand.framesCapacity), (by simpa [frame] using demand.framesReserve),
      demand.operands, (by simpa [frame] using demand.slots)⟩)
    intro out post
    obtain ⟨accepted, controls, budgetEq, controlsEq⟩ := post
    refine ⟨accepted, used, controls, ?_, ?_, ?_⟩
    · rw [budgetEq, frame]
    · simpa [enterInstructionCharge, active] using usedEq
    · simpa [frame] using controlsEq
  case true.Loop =>
    step with compiler_pc_available ops compiler demand.pc as ⟨status, first, same, pc, accepted, _⟩
    subst first
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, active, ite_true]
    obtain ⟨codeFits, sourcesFit, codeReserve, sourceReserve, instructionRoom⟩ :=
      demand.emission active (Or.inr rfl)
    step with runtime.compiler.FunctionCompiler.emit.available ops bound available compiler .LoopHead
      demand.pc codeFits sourcesFit codeReserve sourceReserve demand.coordinate instructionRoom
      as ⟨status, emitted, accepted, effect⟩
    obtain ⟨used, code, sources, frame, usedEq, codeAppend, _⟩ := effect
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    apply WP.spec_mono (publication_available ops bound available emitted state .Loop signature height
      source ctrl.value_stack_base pc none
      ⟨(by simpa [frame] using demand.control),
      (by simpa [frame] using demand.mapsCapacity), (by simpa [frame] using demand.mapsReserve),
      (by simpa [frame] using demand.framesCapacity), (by simpa [frame] using demand.framesReserve),
      demand.operands, (by simpa [frame] using demand.slots)⟩)
    intro out post
    obtain ⟨accepted, controls, budgetEq, controlsEq⟩ := post
    refine ⟨accepted, used, controls, ?_, ?_, ?_⟩
    · rw [budgetEq, frame]
    · simpa [enterInstructionCharge, active] using usedEq
    · simpa [frame] using controlsEq

end Itasca.Runtime.Compiler
