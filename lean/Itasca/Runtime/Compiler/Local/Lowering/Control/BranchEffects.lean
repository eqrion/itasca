import Itasca.Runtime.Compiler.Local.Lowering.Control.BranchContracts

/-! Pure projections from canonical branch traces. These recover selected
operand intervals and exact instruction/frame publication without unfolding the
compiler's branch implementation. -/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

theorem branch_index {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length) :
    (do
      let last ← alloc.vec.Vec.len compiler.frames - 1#usize
      let d ← lift (UScalar.cast .Usize depth)
      let selected ← last - d
      let found ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice runtime.compiler.Frame) compiler.frames selected
      Result.ok (selected, found)) ⦃ out => out = (index, frame) ⦄ := by
  step as ⟨last, hlast⟩
  step as ⟨d, hd⟩
  step as ⟨actualIndex, hindex⟩
  have indexEq : actualIndex = index := by apply UScalar.eq_of_val_eq; simp [alloc.vec.Vec.len] at hlast; scalar_tac
  subst actualIndex
  have inBounds := (List.getElem?_eq_some_iff.mp lookup).1
  step as ⟨found, hfound⟩
  have foundEq : found = frame := by simpa [List.getElem?_eq_getElem inBounds, hfound] using lookup
  simp [foundEq]


/-- Supplied selection and source coordinates identify the trace's checked
prologue, including for an ordinary error in a later phase. -/
theorem BranchEffect.condition {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {depth skip : U32} {conditional : Bool}
    {status : core.result.Result Unit Itasca.error.VisitError}
    (effect : BranchEffect ops before after depth skip conditional status)
    (selected : BranchSelection before depth) (source : U32)
    (position : source.val + (branchWidth selected.frame).val + skip.val = before.height.val) :
    BranchCondition ops before after selected.index selected.frame.height source
      (branchWidth selected.frame) conditional status := by
  obtain ⟨last, converted, index, frame, lastRun, convertedRun, indexRun, frameRun, tail⟩ := effect
  have found := branch_index before selected.frame selected.index depth selected.lookup selected.position
  rw [lastRun, bind_ok, convertedRun, bind_ok, indexRun, bind_ok, frameRun, bind_ok, WP.spec_ok] at found
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj found
  obtain ⟨sum, sumRun, tail⟩ := tail
  have sumFacts : lift (U32.checked_add skip (branchWidth selected.frame)) ⦃ value =>
      match value with
      | none => U32.max < skip.val + (branchWidth selected.frame).val
      | some value => value.val = skip.val + (branchWidth selected.frame).val ⦄ := by
    step as ⟨value, facts⟩
    cases value <;> dsimp only at facts ⊢
    · exact facts
    · exact facts.2.1
  rw [sumRun, WP.spec_ok] at sumFacts
  cases sum with
  | none =>
    dsimp only at sumFacts
    have heightBound : before.height.val ≤ U32.max := by scalar_tac
    omega
  | some sum =>
    dsimp only at sumFacts
    obtain ⟨actualSource, sourceRun, tail⟩ := tail
    have sourceFacts : lift (U32.checked_sub before.height sum) ⦃ value =>
        match value with
        | none => before.height.val < sum.val
        | some value => value.val + sum.val = before.height.val ⦄ := by
      step as ⟨value, facts⟩
      cases value <;> dsimp only at facts ⊢
      · exact facts
      · omega
    rw [sourceRun, WP.spec_ok] at sourceFacts
    cases actualSource with
    | none =>
      dsimp only at sourceFacts
      omega
    | some actualSource =>
      dsimp only at sourceFacts
      have same : actualSource = source := by apply UScalar.eq_of_val_eq; omega
      subst actualSource
      exact tail

/-- The selected frame either stays unchanged (loop) or records its pending
forward jump and end reachability. -/
def BranchFrameUpdate {A : Type} (before after : runtime.compiler.FunctionCompiler A)
    (index : Usize) (frame : runtime.compiler.Frame) (site : Usize) : Prop :=
  if branchLoop frame.kind then after.frames = before.frames
  else ∃ fixups, after.frames.val = before.frames.val.set index.val {frame with end_reachable := true, fixups} ∧
    fixups.val = frame.fixups.val ++ [site]

/-- A loop names its existing start; a forward branch leaves a pending target. -/
def branchTarget (frame : runtime.compiler.Frame) : U32 :=
  if branchLoop frame.kind then frame.start_pc else core.num.U32.MAX

/-- A successful jump without a guard patch is one exact emission. -/
theorem BranchJumpCall.unpatched {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {instruction : runtime.bytecode.Instr}
    (effect : BranchJumpCall ops before after instruction none (.Ok ())) (law : Platform.AllocCorrect ops) :
    EmittedExact before after instruction := by
  obtain ⟨answer, middle, emitted, tail⟩ := effect
  cases answer with
  | Err error => cases tail.1
  | Ok value =>
    cases value
    obtain ⟨_, rfl⟩ := tail
    exact ((runtime.compiler.FunctionCompiler.emit.inv ops before _ instruction _ emitted).2 law).2 rfl

/-- Successful guarded publication first emits its jump and then patches the
previous guard to the final PC. -/
theorem BranchJumpCall.guarded {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {instruction : runtime.bytecode.Instr}
    {site : Usize} {condition : U32}
    (effect : BranchJumpCall ops before after instruction (some site) (.Ok ()))
    (law : Platform.AllocCorrect ops)
    (atGuard : before.function.code.val[site.val]? = some (.JumpIfZero condition core.num.U32.MAX)) :
    ∃ middle target, EmittedExact before middle instruction ∧
      target.val = middle.function.code.val.length ∧
      Patched middle after site.val (.JumpIfZero condition target) := by
  obtain ⟨answer, middle, emitted, tail⟩ := effect
  cases answer with
  | Err error => cases tail.1
  | Ok value =>
    cases value
    have emission := ((runtime.compiler.FunctionCompiler.emit.inv ops before middle instruction _ emitted).2 law).2 rfl
    obtain ⟨pcAnswer, afterPc, pcRun, tail⟩ := tail
    cases pcAnswer with
    | Err error => cases tail.1
    | Ok target =>
      have pc := compiler_pc ops middle
      rw [pcRun, WP.spec_ok] at pc
      have targetPosition := pc.2.1 target rfl
      have bounded : middle.function.code.length ≤ U32.max := by
        simp only [alloc.vec.Vec.length]
        scalar_tac
      have successfulPc := compiler_pc_available ops middle bounded
      rw [pcRun, WP.spec_ok] at successfulPc
      have same : afterPc = middle := successfulPc.1
      subst afterPc
      have patched := runtime.compiler.control.FunctionCompiler.patch.available ops middle site
        (.zero condition) core.num.U32.MAX target (emission.emitted.old_instruction atGuard)
      rw [tail, WP.spec_ok] at patched
      exact ⟨middle, target, emission, targetPosition, patched.2⟩

/-- A successful publication has the exact selected-frame effect, and retains
its final jump/patch continuation for subsequent projections. -/
theorem BranchPublication.success {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index : Usize}
    {conditional copying : Bool} {condition : U32} {guard : Option Usize}
    (effect : BranchPublication ops before after index conditional copying condition guard (.Ok ()))
    (law : Platform.AllocCorrect ops) (frame : runtime.compiler.Frame)
    (lookup : before.frames.val[index.val]? = some frame) :
    ∃ ready frames, ready = {before with frames} ∧
      BranchFrameUpdate before ready index frame (alloc.vec.Vec.len before.function.code) ∧
      BranchJumpCall ops ready after (branchJump conditional copying condition (branchTarget frame)) guard (.Ok ()) := by
  obtain ⟨current, restore, read, tail⟩ := effect
  have inBounds := (List.getElem?_eq_some_iff.mp lookup).1
  have readSpec : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice runtime.compiler.Frame)
      before.frames index ⦃ (value, back) => value = frame ∧
        ∀ replacement, (back replacement).val = before.frames.val.set index.val replacement ⦄ := by
    step as ⟨value, back, found, replaced⟩
    have same : value = frame := found.trans (List.getElem?_eq_some_iff.mp lookup).2
    exact ⟨same, fun replacement => by rw [replaced]; exact alloc.vec.Vec.set_val_eq _ _ _⟩
  rw [read, WP.spec_ok] at readSpec
  have same := readSpec.1
  have restored := readSpec.2
  subst current
  cases loop : branchLoop frame.kind <;>
    simp only [loop, Bool.true_eq, Bool.false_eq_true, ite_true, ite_false] at tail
  · obtain ⟨answer, budget, fixups, pushed, tail⟩ := tail
    cases answer with
    | Err error => cases tail.1
    | Ok value =>
      cases value
      have pushedEffect := budget_push_success ops law before.budget budget frame.fixups fixups
        (alloc.vec.Vec.len before.function.code) pushed
      have sameBudget := pushedEffect.1
      subst budget
      refine ⟨_, restore {frame with end_reachable := true, fixups}, rfl, ?_, ?_⟩
      · simp only [BranchFrameUpdate, loop, Bool.false_eq_true, ite_false]
        exact ⟨fixups, restored _, pushedEffect.2⟩
      · simpa only [branchTarget, loop, Bool.false_eq_true, ite_false] using tail
  · have original : restore frame = before.frames := by
      apply alloc.vec.Vec.ext
      rw [restored]
      have found := (List.getElem?_eq_some_iff.mp lookup).2
      simpa only [← found] using List.set_getElem_self inBounds
    refine ⟨_, restore frame, rfl, ?_, ?_⟩
    · simp only [BranchFrameUpdate, loop, Bool.true_eq, ite_true]
      exact original
    · simpa only [branchTarget, loop, Bool.true_eq, ite_true] using tail

/-- The copy/publication portion retains its exact optional transfer and the
final jump continuation, sharing the proof across forward and loop targets. -/
theorem BranchCopy.success {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {depth : U32}
    {conditional copying : Bool} {condition : U32} {guard : Option Usize}
    (selected : BranchSelection before depth) (source : U32)
    (effect : BranchCopy ops before after selected.index selected.frame.height source
      (branchWidth selected.frame) conditional copying condition guard (.Ok ()))
    (law : Platform.AllocCorrect ops)
    (nonelided : copying = true → ¬ (branchWidth selected.frame = 0#u32 ∨ source = selected.frame.height)) :
    ∃ middle ready frames,
      (if copying then EmittedExact before middle
        (transferInstruction selected.frame.height source (branchWidth selected.frame)) else middle = before) ∧
      ready = {middle with frames} ∧
      BranchFrameUpdate middle ready selected.index selected.frame (alloc.vec.Vec.len middle.function.code) ∧
      BranchJumpCall ops ready after
        (branchJump conditional copying condition (branchTarget selected.frame)) guard (.Ok ()) := by
  cases copying <;> simp only [BranchCopy, Bool.true_eq, Bool.false_eq_true, ite_true, ite_false] at effect ⊢
  · obtain ⟨ready, frames, same, updated, jump⟩ := effect.success law selected.frame selected.lookup
    exact ⟨before, ready, frames, rfl, same, updated, jump⟩
  · obtain ⟨answer, middle, copied, tail⟩ := effect
    cases answer with
    | Err error => cases tail.1
    | Ok value =>
      cases value
      have exactCopy : EmittedExact before middle
          (transferInstruction selected.frame.height source (branchWidth selected.frame)) := by
        rcases runtime.compiler.FunctionCompiler.copy.inv ops before middle selected.frame.height source
            (branchWidth selected.frame) (.Ok ()) copied with ⟨elided, _, _⟩ | ⟨_, _, emitted⟩
        · exact False.elim (nonelided rfl elided)
        · exact ((runtime.compiler.FunctionCompiler.emit.inv ops before middle _ _ emitted).2 law).2 rfl
      have lookup : middle.frames.val[selected.index.val]? = some selected.frame := by
        obtain ⟨used, code, sources, rfl, _, _, _⟩ := exactCopy
        exact selected.lookup
      obtain ⟨ready, frames, same, updated, jump⟩ := tail.success law selected.frame lookup
      exact ⟨middle, ready, frames, exactCopy, same, updated, jump⟩


def BranchCodeBound {A : Type} (before after : runtime.compiler.FunctionCompiler A) (count : Nat) : Prop :=
  before.function.code.val.length ≤ after.function.code.val.length ∧
    after.function.code.val.length ≤ before.function.code.val.length + count

theorem BranchCodeBound.same {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (same : after.function.code.val.length = before.function.code.val.length) : BranchCodeBound before after 0 := by
  unfold BranchCodeBound
  rw [same]
  exact ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem BranchCodeBound.trans {A : Type} {before middle after : runtime.compiler.FunctionCompiler A} {first second}
    (head : BranchCodeBound before middle first) (tail : BranchCodeBound middle after second) :
    BranchCodeBound before after (first + second) := by
  obtain ⟨h1, h2⟩ := head
  obtain ⟨t1, t2⟩ := tail
  constructor <;> omega

theorem BranchCodeBound.weaken {A : Type} {before after : runtime.compiler.FunctionCompiler A} {small large}
    (effect : BranchCodeBound before after small) (bound : small ≤ large) : BranchCodeBound before after large := by
  obtain ⟨lower, upper⟩ := effect
  constructor <;> omega

private theorem branch_emit_code_bound {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (instruction : runtime.bytecode.Instr) (status)
    (called : runtime.compiler.FunctionCompiler.emit ops before instruction = .ok (status, after)) :
    BranchCodeBound before after 1 := by
  have growth := ((runtime.compiler.FunctionCompiler.emit.inv ops before after instruction status called).2 law).1
  rcases growth with same | added <;> unfold BranchCodeBound
  · rw [same]; omega
  · rw [added, List.length_append, List.length_singleton]; omega

private theorem branch_copy_code_bound {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (dst src count : U32) (status)
    (called : runtime.compiler.FunctionCompiler.copy ops before dst src count = .ok (status, after)) :
    BranchCodeBound before after 1 := by
  rcases runtime.compiler.FunctionCompiler.copy.inv ops before after dst src count status called with ⟨_, _, same⟩ | ⟨_, _, emitted⟩
  · rw [same]; exact (BranchCodeBound.same rfl).weaken (by omega)
  · exact branch_emit_code_bound ops law _ _ _ _ emitted

theorem BranchPatch.code_bound {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {guard status}
    (effect : BranchPatch ops before after guard status) : BranchCodeBound before after 0 := by
  cases guard with
  | none => rw [effect.2]; exact .same rfl
  | some site =>
    obtain ⟨answer, middle, called, rest⟩ := effect
    have pc := compiler_pc ops before
    rw [called, WP.spec_ok] at pc
    have same : middle.function = before.function := pc.1
    have head : BranchCodeBound before middle 0 := .same (by rw [same])
    apply head.trans (second := 0)
    cases answer with
    | Err error => rw [rest.2]; exact .same rfl
    | Ok target =>
      apply BranchCodeBound.same
      rcases compiler_patch_cases ops middle after site target status rest with unchanged | ⟨instruction, code, frame, contents⟩
      · rw [unchanged]
      · rw [frame]
        simp only [contents, List.length_set]

theorem BranchJumpCall.code_bound {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {instruction guard status}
    (effect : BranchJumpCall ops before after instruction guard status) (law : Platform.AllocCorrect ops) : BranchCodeBound before after 1 := by
  obtain ⟨answer, middle, called, rest⟩ := effect
  have head := branch_emit_code_bound ops law _ _ _ _ called
  cases answer with
  | Err error => rw [rest.2]; exact head
  | Ok value => exact head.trans rest.code_bound

theorem BranchPublication.code_bound {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index conditional copying condition guard status}
    (effect : BranchPublication ops before after index conditional copying condition guard status) (law : Platform.AllocCorrect ops) : BranchCodeBound before after 1 := by
  obtain ⟨frame, restore, _, rest⟩ := effect
  split at rest
  · have bound := rest.code_bound law
    exact bound
  · obtain ⟨answer, budget, fixups, _, rest⟩ := rest
    cases answer with
    | Err error => rw [rest.2]; exact (BranchCodeBound.same rfl).weaken (by omega)
    | Ok value =>
      have bound := rest.code_bound law
      exact bound

theorem BranchCopy.code_bound {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index dst src count conditional copying condition guard status}
    (effect : BranchCopy ops before after index dst src count conditional copying condition guard status) (law : Platform.AllocCorrect ops) : BranchCodeBound before after 2 := by
  unfold BranchCopy at effect
  split at effect
  · obtain ⟨answer, middle, called, rest⟩ := effect
    have head := branch_copy_code_bound ops law _ _ _ _ _ _ called
    cases answer with
    | Err error => rw [rest.2]; exact head.weaken (by omega)
    | Ok value => exact head.trans (rest.code_bound law)
  · exact (effect.code_bound law).weaken (by omega)

theorem BranchTransfer.code_bound {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index dst src count conditional condition status}
    (effect : BranchTransfer ops before after index dst src count conditional condition status) (law : Platform.AllocCorrect ops) :
    BranchCodeBound before after (if conditional then 3 else 2) := by
  dsimp only [BranchTransfer] at effect
  split at effect
  · rename_i guarded
    have live : conditional = true := (Bool.and_eq_true_iff.mp guarded).1
    simp only [live, ite_true]
    obtain ⟨answer, middle, called, rest⟩ := effect
    have head := branch_emit_code_bound ops law _ _ _ _ called
    cases answer with
    | Err error => rw [rest.2]; exact head.weaken (by omega)
    | Ok value => exact head.trans (rest.code_bound law)
  · apply (effect.code_bound law).weaken
    split <;> omega

theorem BranchCondition.code_bound {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index dst src count conditional status}
    (effect : BranchCondition ops before after index dst src count conditional status) (law : Platform.AllocCorrect ops) :
    BranchCodeBound before after (if conditional then 3 else 2) := by
  unfold BranchCondition at effect
  split at effect
  · obtain ⟨answer, _, rest⟩ := effect
    cases answer with
    | Err error => rw [rest.2]; exact (BranchCodeBound.same rfl).weaken (Nat.zero_le _)
    | Ok value => exact rest.code_bound law
  · exact effect.code_bound law

theorem BranchSource.code_bound {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index frame skip conditional status}
    (effect : BranchSource ops before after index frame skip conditional status) (law : Platform.AllocCorrect ops) :
    BranchCodeBound before after (if conditional then 3 else 2) := by
  obtain ⟨sum, _, rest⟩ := effect
  cases sum with
  | none => rw [rest.2]; exact (BranchCodeBound.same rfl).weaken (Nat.zero_le _)
  | some width =>
    obtain ⟨source, _, rest⟩ := rest
    cases source with
    | none => rw [rest.2]; exact (BranchCodeBound.same rfl).weaken (Nat.zero_le _)
    | some src => exact rest.code_bound law

theorem BranchEffect.code_bound {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {depth skip conditional status}
    (effect : BranchEffect ops before after depth skip conditional status) (law : Platform.AllocCorrect ops) :
    BranchCodeBound before after (if conditional then 3 else 2) := by
  obtain ⟨_, _, _, _, _, _, _, _, rest⟩ := effect
  exact rest.code_bound law

/-- Exact code and frame publication for a branch whose final jump needs no
separate guard patch. -/
theorem BranchCopy.unpatched_success {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {depth : U32}
    {conditional copying : Bool} {condition : U32}
    (selected : BranchSelection before depth) (source : U32)
    (effect : BranchCopy ops before after selected.index selected.frame.height source
      (branchWidth selected.frame) conditional copying condition none (.Ok ()))
    (law : Platform.AllocCorrect ops)
    (nonelided : copying = true → ¬ (branchWidth selected.frame = 0#u32 ∨ source = selected.frame.height)) :
    ∃ site,
      after.function.code.val = before.function.code.val ++
        (if copying then [transferInstruction selected.frame.height source (branchWidth selected.frame)] else []) ++
        [branchJump conditional copying condition (branchTarget selected.frame)] ∧
      site.val = before.function.code.val.length + (if copying then 1 else 0) ∧
      BranchFrameUpdate before after selected.index selected.frame site := by
  obtain ⟨middle, ready, frames, transferred, rfl, updated, jump⟩ :=
    effect.success selected source law nonelided
  have emitted := jump.unpatched law
  obtain ⟨used, code, sources, rfl, _, appended, _⟩ := emitted
  refine ⟨alloc.vec.Vec.len middle.function.code, ?_, ?_, ?_⟩
  · cases copying <;> simp only [Bool.true_eq, Bool.false_eq_true, ite_true, ite_false] at transferred ⊢
    · subst middle
      simpa only [List.append_nil] using appended
    · obtain ⟨copyUsed, copyCode, copySources, rfl, _, copied, _⟩ := transferred
      simpa only [copied] using appended
  · cases copying <;> simp only [Bool.true_eq, Bool.false_eq_true, ite_true, ite_false] at transferred ⊢
    · subst middle
      simp only [alloc.vec.Vec.len, Usize.ofNatCore_val_eq, Nat.add_zero]
    · obtain ⟨copyUsed, copyCode, copySources, rfl, _, copied, _⟩ := transferred
      simp only [alloc.vec.Vec.len, Usize.ofNatCore_val_eq, copied, List.length_append,
        List.length_cons, List.length_nil]
  · cases copying <;> simp only [Bool.true_eq, Bool.false_eq_true, ite_true, ite_false] at transferred
    · subst middle
      exact updated
    · obtain ⟨copyUsed, copyCode, copySources, rfl, _, _, _⟩ := transferred
      exact updated

/-- The nonelided-copy flag is false precisely in the two elision cases. -/
theorem branch_copy_flag_false (count source destination : U32)
    (elided : count = 0#u32 ∨ source = destination) :
    ((count != 0#u32) && (source != destination)) = false := by
  rcases elided with zero | same
  · simp only [zero, bne_self_eq_false, Bool.false_and]
  · simp only [same, bne_self_eq_false, Bool.and_false]

theorem branch_copy_flag_true (count source destination : U32)
    (nonelided : ¬ (count = 0#u32 ∨ source = destination)) :
    ((count != 0#u32) && (source != destination)) = true := by
  simp only [Bool.and_eq_true, bne_iff_ne]
  exact ⟨fun equal => nonelided (Or.inl equal), fun equal => nonelided (Or.inr equal)⟩

/-- A conditional transfer emits a guard, one copy, and its jump, then retargets
the guard to the point immediately after those three instructions. -/
theorem BranchTransfer.guarded_success {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {depth : U32} {condition : U32}
    (selected : BranchSelection before depth) (source : U32)
    (effect : BranchTransfer ops before after selected.index selected.frame.height source
      (branchWidth selected.frame) true condition (.Ok ()))
    (law : Platform.AllocCorrect ops)
    (nonelided : ¬ (branchWidth selected.frame = 0#u32 ∨ source = selected.frame.height)) :
    ∃ resume site,
      after.function.code.val = before.function.code.val ++
        [.JumpIfZero condition resume,
          transferInstruction selected.frame.height source (branchWidth selected.frame),
          .Jump (branchTarget selected.frame)] ∧
      site.val = before.function.code.val.length + 2 ∧
      BranchFrameUpdate before after selected.index selected.frame site ∧
      resume.val = before.function.code.val.length + 3 := by
  have flag := branch_copy_flag_true (branchWidth selected.frame) source selected.frame.height nonelided
  simp only [BranchTransfer, flag, Bool.true_and, Bool.true_eq, ite_true] at effect
  obtain ⟨answer, guardState, guardRun, tail⟩ := effect
  cases answer with
  | Err error => cases tail.1
  | Ok value =>
    cases value
    have guardEmission := ((runtime.compiler.FunctionCompiler.emit.inv ops before guardState _ _ guardRun).2 law).2 rfl
    obtain ⟨guardUsed, guardCode, guardSources, rfl, _, guardAppended, _⟩ := guardEmission
    have guardAt : guardCode.val[(alloc.vec.Vec.len before.function.code).val]? =
        some (.JumpIfZero condition core.num.U32.MAX) := by
      simp only [alloc.vec.Vec.len, Usize.ofNatCore_val_eq, guardAppended, List.getElem?_concat_length]
    obtain ⟨middle, ready, frames, copyEmission, rfl, updated, jump⟩ :=
      tail.success (show BranchSelection {before with
        budget := {before.budget with instructions := guardUsed}
        function := {before.function with code := guardCode, source_offsets := guardSources}} depth from
          ⟨selected.index, selected.frame, selected.lookup, selected.position⟩) source law (fun _ => nonelided)
    change EmittedExact _ middle _ at copyEmission
    have copiedGuard := copyEmission.emitted.old_instruction guardAt
    obtain ⟨copyUsed, copyCode, copySources, rfl, _, copyAppended, _⟩ := copyEmission
    obtain ⟨jumpState, resume, jumpEmission, resumePosition, patched⟩ := jump.guarded law copiedGuard
    obtain ⟨jumpUsed, jumpCode, jumpSources, rfl, _, jumpAppended, _⟩ := jumpEmission
    obtain ⟨patchedCode, rfl, patchedValues⟩ := patched
    simp only [branchJump, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false] at jumpAppended
    refine ⟨resume, alloc.vec.Vec.len copyCode, ?_, ?_, ?_, ?_⟩
    · change patchedCode.val = _
      simp only [alloc.vec.Vec.len, Usize.ofNatCore_val_eq] at patchedValues
      rw [patchedValues, jumpAppended, copyAppended, guardAppended]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      rw [List.set_append_right _ _ (Nat.le_refl _)]
      simp only [Nat.sub_self, List.set_cons_zero]
    · simp only [alloc.vec.Vec.len, Usize.ofNatCore_val_eq, copyAppended, guardAppended,
        List.length_append, List.length_cons, List.length_nil, Nat.add_assoc]
    · exact updated
    · simpa only [jumpAppended, copyAppended, guardAppended, List.length_append,
        List.length_cons, List.length_nil, Nat.add_assoc] using resumePosition

/-- Supplied conditional-operand evidence identifies the transfer trace. -/
theorem BranchEffect.transfer {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {depth skip : U32} {conditional : Bool}
    {status : core.result.Result Unit Itasca.error.VisitError}
    (effect : BranchEffect ops before after depth skip conditional status)
    (selected : BranchSelection before depth) (source : U32)
    (position : source.val + (branchWidth selected.frame).val + skip.val = before.height.val)
    (condition : U32) (ready : conditional = true →
      runtime.compiler.FunctionCompiler.operand ops before 1#usize = .ok (.Ok condition)) :
    BranchTransfer ops before after selected.index selected.frame.height source
      (branchWidth selected.frame) conditional (if conditional then condition else 0#u32) status := by
  have tail := effect.condition selected source position
  cases conditional <;> simp only [BranchCondition, Bool.true_eq, Bool.false_eq_true, ite_true, ite_false] at tail ⊢
  · exact tail
  · obtain ⟨answer, called, tail⟩ := tail
    rw [ready rfl] at called
    have same : answer = .Ok condition := (Result.ok_injective called).symm
    subst answer
    exact tail

/-- The exact instruction suffix of successful branch lowering. -/
def branchOutput (conditional : Bool) (frame : runtime.compiler.Frame) (source condition resume : U32) :
    List runtime.bytecode.Instr :=
  if branchWidth frame = 0#u32 ∨ source = frame.height then
    [branchJump conditional false condition (branchTarget frame)]
  else if conditional then
    [.JumpIfZero condition resume, transferInstruction frame.height source (branchWidth frame), .Jump (branchTarget frame)]
  else [transferInstruction frame.height source (branchWidth frame), .Jump (branchTarget frame)]

/-- Successful traces recover the exact code suffix, jump site, and selected
frame update. A conditional transfer also identifies its guard's final target. -/
theorem BranchEffect.success {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {depth skip : U32} {conditional : Bool}
    (effect : BranchEffect ops before after depth skip conditional (.Ok ()))
    (selected : BranchSelection before depth) (source : U32)
    (position : source.val + (branchWidth selected.frame).val + skip.val = before.height.val)
    (condition : U32) (ready : conditional = true →
      runtime.compiler.FunctionCompiler.operand ops before 1#usize = .ok (.Ok condition))
    (law : Platform.AllocCorrect ops) :
    ∃ resume site,
      after.function.code.val = before.function.code.val ++ branchOutput conditional selected.frame source condition resume ∧
      site.val = before.function.code.val.length + (branchInstructionCount conditional selected.frame source - 1) ∧
      BranchFrameUpdate before after selected.index selected.frame site ∧
      (conditional = true → ¬ (branchWidth selected.frame = 0#u32 ∨ source = selected.frame.height) →
        resume.val = before.function.code.val.length + 3) := by
  have trace := effect.transfer selected source position condition ready
  cases conditional <;> simp only [Bool.true_eq, Bool.false_eq_true, ite_true, ite_false] at trace ⊢
  all_goals by_cases elided : branchWidth selected.frame = 0#u32 ∨ source = selected.frame.height
  all_goals first
    | (have yes : branchWidth selected.frame = 0#u32 ∨ source = selected.frame.height := elided
       have flag := branch_copy_flag_false (branchWidth selected.frame) source selected.frame.height yes
       simp only [BranchTransfer, flag, Bool.and_false, Bool.false_and, Bool.true_and,
         Bool.false_eq_true, Bool.true_eq, ite_false, ite_true] at trace
       obtain ⟨site, code, sitePosition, updated⟩ :=
         trace.unpatched_success selected source law (by intro impossible; cases impossible)
       refine ⟨0#u32, site, ?_, ?_, updated, ?_⟩
       · simpa only [branchOutput, if_pos yes, branchJump, Bool.not_false, Bool.and_true,
           Bool.true_eq, Bool.false_eq_true, ite_true, ite_false, List.append_nil] using code
       · simpa only [branchInstructionCount, if_pos yes, Bool.false_eq_true, ite_false] using sitePosition
       · intro _ different
         exact False.elim (different yes))
    | (have no : ¬ (branchWidth selected.frame = 0#u32 ∨ source = selected.frame.height) := elided
       first
       | (obtain ⟨resume, site, code, sitePosition, updated, resumePosition⟩ :=
             trace.guarded_success selected source law no
          refine ⟨resume, site, ?_, ?_, updated, fun _ _ => resumePosition⟩
          · simpa only [branchOutput, if_neg no, Bool.true_eq, ite_true] using code
          · simpa only [branchInstructionCount, if_neg no, Bool.true_eq, ite_true] using sitePosition)
       | (have flag := branch_copy_flag_true (branchWidth selected.frame) source selected.frame.height no
          simp only [BranchTransfer, flag, Bool.false_and, Bool.false_eq_true, ite_false] at trace
          obtain ⟨site, code, sitePosition, updated⟩ := trace.unpatched_success selected source law (fun _ => no)
          refine ⟨0#u32, site, ?_, ?_, updated, ?_⟩
          · simpa only [branchOutput, if_neg no, branchJump, Bool.not_true, Bool.false_and,
              Bool.false_eq_true, ite_false, Bool.true_eq, ite_true, List.append_assoc,
              List.cons_append, List.nil_append] using code
          · simpa only [branchInstructionCount, if_neg no, Bool.false_eq_true, ite_false,
              Bool.true_eq, ite_true] using sitePosition
          · intro impossible
            cases impossible))

def BranchSourceTrace {A : Type} (before after : runtime.compiler.FunctionCompiler A) : Prop :=
  BranchFrame before after ∧ ∃ count,
    after.function.code.val.length = before.function.code.val.length + count ∧
    after.function.source_offsets.val.map UScalar.val = before.function.source_offsets.val.map UScalar.val ++
      List.replicate count (before.function.body_start.val + before.next_source.val)

theorem BranchSourceTrace.refl {A : Type} (before : runtime.compiler.FunctionCompiler A) : BranchSourceTrace before before := by
  exact ⟨rfl, 0, rfl, by simp only [List.replicate_zero, List.append_nil]⟩

theorem BranchSourceTrace.trans {A : Type} {before middle after : runtime.compiler.FunctionCompiler A}
    (first : BranchSourceTrace before middle) (second : BranchSourceTrace middle after) : BranchSourceTrace before after := by
  obtain ⟨firstFrame, n, firstCode, firstSources⟩ := first
  obtain ⟨secondFrame, m, secondCode, secondSources⟩ := second
  refine ⟨firstFrame.trans secondFrame, n + m, by omega, ?_⟩
  have origin : middle.function.body_start.val + middle.next_source.val = before.function.body_start.val + before.next_source.val := by
    rw [firstFrame]
  simp only [secondSources, firstSources, origin, List.replicate_add, List.append_assoc]

theorem EmittedExact.branch_sources {A : Type} {before after : runtime.compiler.FunctionCompiler A} {instruction}
    (effect : EmittedExact before after instruction) : BranchSourceTrace before after := by
  obtain ⟨used, code, sources, rfl, _, appended, mapped⟩ := effect
  refine ⟨rfl, 1, ?_, ?_⟩
  · simp only [appended, List.length_append, List.length_singleton]
  · simpa only [List.replicate_succ, List.replicate_zero] using mapped

private theorem branch_pc_source_trace {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (status)
    (called : runtime.compiler.FunctionCompiler.pc ops before = .ok (status, after)) : BranchSourceTrace before after := by
  have post := compiler_pc ops before
  rw [called, WP.spec_ok] at post
  obtain ⟨budget, same⟩ := post.2.2
  change after = {before with budget} at same
  rw [same]
  exact ⟨rfl, 0, rfl, by simp only [List.replicate_zero, List.append_nil]⟩

private theorem branch_patch_source_trace {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (site : Usize) (target : U32) (status)
    (called : runtime.compiler.control.FunctionCompiler.patch ops before site target = .ok (status, after)) : BranchSourceTrace before after := by
  rcases compiler_patch_cases ops before after site target status called with same | ⟨instruction, code, same, contents⟩
  · rw [same]; exact .refl _
  · rw [same]
    refine ⟨rfl, 0, ?_, ?_⟩
    · simp only [contents, List.length_set, Nat.add_zero]
    · simp only [List.replicate_zero, List.append_nil]

theorem BranchPatch.source_trace {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {guard}
    (effect : BranchPatch ops before after guard (.Ok ())) : BranchSourceTrace before after := by
  cases guard with
  | none => rw [effect.2]; exact .refl _
  | some site =>
    obtain ⟨answer, middle, called, rest⟩ := effect
    have head := branch_pc_source_trace ops _ _ _ called
    cases answer with
    | Err error => cases rest.1
    | Ok target => exact head.trans (branch_patch_source_trace ops _ _ _ _ _ rest)

theorem BranchJumpCall.source_trace {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {instruction guard}
    (effect : BranchJumpCall ops before after instruction guard (.Ok ())) (law : Platform.AllocCorrect ops) : BranchSourceTrace before after := by
  obtain ⟨answer, middle, called, rest⟩ := effect
  cases answer with
  | Err error => cases rest.1
  | Ok value =>
    cases value
    exact (((runtime.compiler.FunctionCompiler.emit.inv ops _ _ _ _ called).2 law).2 rfl).branch_sources.trans rest.source_trace

theorem BranchPublication.source_trace {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index conditional copying condition guard}
    (effect : BranchPublication ops before after index conditional copying condition guard (.Ok ())) (law : Platform.AllocCorrect ops) : BranchSourceTrace before after := by
  obtain ⟨frame, restore, _, rest⟩ := effect
  split at rest
  · have trace := rest.source_trace law
    exact trace
  · obtain ⟨answer, budget, fixups, _, rest⟩ := rest
    cases answer with
    | Err error => cases rest.1
    | Ok value =>
      have trace := rest.source_trace law
      exact trace

theorem BranchCopy.source_trace {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index dst src count conditional copying condition guard}
    (effect : BranchCopy ops before after index dst src count conditional copying condition guard (.Ok ())) (law : Platform.AllocCorrect ops) : BranchSourceTrace before after := by
  unfold BranchCopy at effect
  split at effect
  · obtain ⟨answer, middle, called, rest⟩ := effect
    cases answer with
    | Err error => cases rest.1
    | Ok value =>
      cases value
      have copied := (runtime.compiler.FunctionCompiler.copy.inv ops before middle dst src count (.Ok ()) called).exact law rfl
      rcases copied with same | emitted
      · subst middle
        exact rest.source_trace law
      · exact emitted.branch_sources.trans (rest.source_trace law)
  · exact effect.source_trace law

theorem BranchTransfer.source_trace {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index dst src count conditional condition}
    (effect : BranchTransfer ops before after index dst src count conditional condition (.Ok ())) (law : Platform.AllocCorrect ops) : BranchSourceTrace before after := by
  dsimp only [BranchTransfer] at effect
  split at effect
  · obtain ⟨answer, middle, called, rest⟩ := effect
    cases answer with
    | Err error => cases rest.1
    | Ok value =>
      cases value
      exact (((runtime.compiler.FunctionCompiler.emit.inv ops _ _ _ _ called).2 law).2 rfl).branch_sources.trans (rest.source_trace law)
  · exact effect.source_trace law

theorem BranchCondition.source_trace {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index dst src count conditional}
    (effect : BranchCondition ops before after index dst src count conditional (.Ok ())) (law : Platform.AllocCorrect ops) : BranchSourceTrace before after := by
  unfold BranchCondition at effect
  split at effect
  · obtain ⟨answer, _, rest⟩ := effect
    cases answer with
    | Err error => cases rest.1
    | Ok value => exact rest.source_trace law
  · exact effect.source_trace law

theorem BranchSource.source_trace {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index frame skip conditional}
    (effect : BranchSource ops before after index frame skip conditional (.Ok ())) (law : Platform.AllocCorrect ops) : BranchSourceTrace before after := by
  obtain ⟨sum, _, rest⟩ := effect
  cases sum with
  | none => cases rest.1
  | some width =>
    obtain ⟨source, _, rest⟩ := rest
    cases source with
    | none => cases rest.1
    | some src => exact rest.source_trace law

theorem BranchEffect.source_trace {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {depth skip conditional}
    (effect : BranchEffect ops before after depth skip conditional (.Ok ())) (law : Platform.AllocCorrect ops) : BranchSourceTrace before after := by
  obtain ⟨_, _, _, _, _, _, _, _, rest⟩ := effect
  exact rest.source_trace law

theorem BranchJumpCall.code_strict {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {instruction guard}
    (effect : BranchJumpCall ops before after instruction guard (.Ok ())) (law : Platform.AllocCorrect ops) : before.function.code.val.length < after.function.code.val.length := by
  obtain ⟨answer, middle, called, rest⟩ := effect
  cases answer with
  | Err error => cases rest.1
  | Ok value =>
    cases value
    have emitted := (((runtime.compiler.FunctionCompiler.emit.inv ops _ _ _ _ called).2 law).2 rfl).branch_sources
    obtain ⟨_, count, code, _⟩ := emitted
    have one : middle.function.code.val = before.function.code.val ++ [instruction] := by
      obtain ⟨used, code, sources, same, _, appended, mapped⟩ :=
        ((runtime.compiler.FunctionCompiler.emit.inv ops _ _ _ _ called).2 law).2 rfl
      rw [same]
      exact appended
    obtain ⟨lower, upper⟩ := rest.code_bound
    simp only [one, List.length_append, List.length_singleton] at lower upper
    omega

theorem BranchPublication.code_strict {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index conditional copying condition guard}
    (effect : BranchPublication ops before after index conditional copying condition guard (.Ok ())) (law : Platform.AllocCorrect ops) : before.function.code.val.length < after.function.code.val.length := by
  obtain ⟨frame, restore, _, rest⟩ := effect
  split at rest
  · have trace := rest.code_strict law
    exact trace
  · obtain ⟨answer, budget, fixups, _, rest⟩ := rest
    cases answer with
    | Err error => cases rest.1
    | Ok value =>
      have trace := rest.code_strict law
      exact trace

theorem BranchCopy.code_strict {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index dst src count conditional copying condition guard}
    (effect : BranchCopy ops before after index dst src count conditional copying condition guard (.Ok ())) (law : Platform.AllocCorrect ops) : before.function.code.val.length < after.function.code.val.length := by
  unfold BranchCopy at effect
  split at effect
  · obtain ⟨answer, middle, called, rest⟩ := effect
    cases answer with
    | Err error => cases rest.1
    | Ok value =>
      cases value
      have copied := (runtime.compiler.FunctionCompiler.copy.inv ops before middle dst src count (.Ok ()) called).exact law rfl
      rcases copied with same | emitted
      · subst middle
        exact rest.code_strict law
      · have growth := (emitted.branch_sources).2
        obtain ⟨count, code, _⟩ := growth
        have strict := rest.code_strict law
        omega
  · exact effect.code_strict law

theorem BranchTransfer.code_strict {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index dst src count conditional condition}
    (effect : BranchTransfer ops before after index dst src count conditional condition (.Ok ())) (law : Platform.AllocCorrect ops) : before.function.code.val.length < after.function.code.val.length := by
  dsimp only [BranchTransfer] at effect
  split at effect
  · obtain ⟨answer, middle, called, rest⟩ := effect
    cases answer with
    | Err error => cases rest.1
    | Ok value =>
      cases value
      obtain ⟨_, count, code, _⟩ := (((runtime.compiler.FunctionCompiler.emit.inv ops _ _ _ _ called).2 law).2 rfl).branch_sources
      have strict := rest.code_strict law
      omega
  · exact effect.code_strict law

theorem BranchCondition.code_strict {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index dst src count conditional}
    (effect : BranchCondition ops before after index dst src count conditional (.Ok ())) (law : Platform.AllocCorrect ops) : before.function.code.val.length < after.function.code.val.length := by
  unfold BranchCondition at effect
  split at effect
  · obtain ⟨answer, _, rest⟩ := effect
    cases answer with
    | Err error => cases rest.1
    | Ok value => exact rest.code_strict law
  · exact effect.code_strict law

theorem BranchSource.code_strict {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index frame skip conditional}
    (effect : BranchSource ops before after index frame skip conditional (.Ok ())) (law : Platform.AllocCorrect ops) : before.function.code.val.length < after.function.code.val.length := by
  obtain ⟨sum, _, rest⟩ := effect
  cases sum with
  | none => cases rest.1
  | some width =>
    obtain ⟨source, _, rest⟩ := rest
    cases source with
    | none => cases rest.1
    | some src => exact rest.code_strict law

theorem BranchEffect.code_strict {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {depth skip conditional}
    (effect : BranchEffect ops before after depth skip conditional (.Ok ())) (law : Platform.AllocCorrect ops) : before.function.code.val.length < after.function.code.val.length := by
  obtain ⟨_, _, _, _, _, _, _, _, rest⟩ := effect
  exact rest.code_strict law


end Itasca.Runtime.Compiler
