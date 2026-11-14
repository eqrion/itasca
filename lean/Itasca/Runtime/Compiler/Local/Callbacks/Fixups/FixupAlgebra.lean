import Itasca.Runtime.Compiler.Local.Relations.Control

/-!
Sections, each formerly its own module: Fixups, FixupAlgebra.
-/

/-! ## Fixups -/

section

/-! The actual end-label fixup loops terminate normally and change only code.
Every listed branch receives the exit PC, including duplicate fixup addresses;
branch conditions, code length, unrelated instructions, and compiler layout are
preserved. The initial branch-shape premise is a syntactic hole invariant. -/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

def retarget (instruction : runtime.bytecode.Instr) (target : U32) : runtime.bytecode.Instr :=
  match instruction with
  | .Jump _ => .Jump target
  | .JumpIfZero condition _ => .JumpIfZero condition target
  | .JumpIfNonZero condition _ => .JumpIfNonZero condition target
  | other => other

def patchCode (code : List runtime.bytecode.Instr) (sites : List Usize) (target : U32) :
    List runtime.bytecode.Instr :=
  match sites with
  | [] => code
  | pc :: rest =>
    let changed := match code[pc.val]? with
      | some instruction => code.set pc.val (retarget instruction target)
      | none => code
    patchCode changed rest target

def BranchSites (code : List runtime.bytecode.Instr) (sites : List Usize) : Prop :=
  ∀ pc, pc ∈ sites → ∃ (kind : BranchKind) (old : U32), code[pc.val]? = some (kind.instruction old)

def OnlyCode {A : Type} (before after : runtime.compiler.FunctionCompiler A) : Prop :=
  ∃ code, after = { before with function := { before.function with code } }

theorem OnlyCode.refl {A : Type} (compiler : runtime.compiler.FunctionCompiler A) :
    OnlyCode compiler compiler := ⟨compiler.function.code, rfl⟩

theorem OnlyCode.trans {A : Type} {a b c : runtime.compiler.FunctionCompiler A}
    (ab : OnlyCode a b) (bc : OnlyCode b c) : OnlyCode a c := by
  obtain ⟨code, rfl⟩ := ab
  obtain ⟨code', rfl⟩ := bc
  exact ⟨code', rfl⟩

theorem Patched.only_code {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {pc instruction} (patched : Patched before after pc instruction) : OnlyCode before after := by
  obtain ⟨code, rfl, _⟩ := patched
  exact ⟨code, rfl⟩

theorem Patched.branch_sites {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {pc target sites} {kind : BranchKind} (patched : Patched before after pc (kind.instruction target))
    (inside : pc < before.function.code.val.length)
    (old : BranchSites before.function.code.val sites) : BranchSites after.function.code.val sites := by
  intro site member
  by_cases same : site.val = pc
  · exact ⟨kind, target, same ▸ patched.target inside⟩
  · obtain ⟨k, previous, h⟩ := old site member
    exact ⟨k, previous, (patched.other same).trans h⟩

def compilerSnapshot {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (result : core.result.Result Unit Itasca.error.VisitError) :=
  (compiler.signatures, compiler.func_param_slots, compiler.budget,
   compiler.batch_start, compiler.function, compiler.frames, compiler.reachable,
   compiler.next_source, compiler.before, compiler.height, compiler.local_offsets,
   compiler.table_depths, result)

abbrev CompilerSnapshot (A : Type) :=
  Slice runtime.compiler.Signature × Slice U32 × runtime.compiler.Budget A × Usize ×
  runtime.bytecode.CompiledFunction × alloc.vec.Vec runtime.compiler.Frame × Bool × Usize ×
  alloc.vec.Vec U32 × U32 × alloc.vec.Vec U32 × alloc.vec.Vec U32 ×
  core.result.Result Unit Itasca.error.VisitError

def snapshotCompiler {A : Type} (output : CompilerSnapshot A) : runtime.compiler.FunctionCompiler A :=
  let (signatures, functionSlots, budget, batchStart, function, frames, reachable,
    nextSource, operands, height, offsets, depths, _) := output
  ⟨signatures, functionSlots, budget, batchStart, function, frames, reachable,
    nextSource, operands, height, offsets, depths⟩

theorem compiler_fixups_effect {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (sites : alloc.vec.Vec Usize)
    (target : U32) (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (output : CompilerSnapshot A)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0
      ops before sites target index status = .ok output) :
    OnlyCode before (snapshotCompiler output) ∧
      (snapshotCompiler output).function.code.val.length = before.function.code.val.length := by
  generalize measure : Usize.max - index.val = n
  induction n using Nat.strong_induction_on generalizing before index status with
  | h n ih =>
    unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0 at accepted
    rw [loop] at accepted
    simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0.body] at accepted
    split at accepted
    · cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, Result.ok.injEq] at accepted
        subst output
        exact ⟨.refl _, rfl⟩
      | Ok value =>
        cases value
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte, Std.bind_assoc] at accepted
        obtain ⟨site, _, rest⟩ := bind_ok_inv _ _ _ accepted
        obtain ⟨⟨result, middle⟩, patched, tail⟩ := bind_ok_inv _ _ _ rest
        simp only [uncurry_apply_pair, Std.bind_assoc, bind_ok] at tail
        obtain ⟨nextIndex, increment, tail⟩ := bind_ok_inv _ _ _ tail
        have arithmetic := UScalar.add_equiv index 1#usize
        rw [increment] at arithmetic
        have progress : nextIndex.val = index.val + 1 := by simpa using arithmetic.2.1
        have nextMax := nextIndex.hmax
        have smaller : Usize.max - nextIndex.val < n := by scalar_tac
        have tail' : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0
            ops middle sites target nextIndex result = .ok output := by
          simpa only [uncurry_apply_pair, bind_ok,
            runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0,
            runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0.body,
            core.result.Result.is_ok] using tail
        have patchFrame : OnlyCode before middle := by
          rcases compiler_patch_cases ops before middle site target result patched with same | ⟨instruction, effect⟩
          · rw [same]; exact .refl _
          · exact effect.only_code
        have tailEffect := ih _ smaller middle nextIndex result tail' rfl
        refine ⟨patchFrame.trans tailEffect.1, ?_⟩
        rw [tailEffect.2]
        rcases compiler_patch_cases ops before middle site target result patched with same | ⟨instruction, code, same, contents⟩
        · rw [same]
        · rw [same]
          simp only [contents, List.length_set]

    · simp only [bind_ok, Result.ok.injEq] at accepted
      subst output
      exact ⟨.refl _, rfl⟩

theorem compiler_fixups_frame {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (sites : alloc.vec.Vec Usize)
    (target : U32) (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (output : CompilerSnapshot A)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0
      ops before sites target index status = .ok output) :
    OnlyCode before (snapshotCompiler output) := by
  exact (compiler_fixups_effect ops before sites target index status output accepted).1

theorem compiler_fixups_code_length {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (sites : alloc.vec.Vec Usize)
    (target : U32) (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (output : CompilerSnapshot A)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0
      ops before sites target index status = .ok output) :
    (snapshotCompiler output).function.code.val.length = before.function.code.val.length := by
  exact (compiler_fixups_effect ops before sites target index status output accepted).2

@[step] theorem compiler_fixups {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (sites : alloc.vec.Vec Usize)
    (target : U32) (i : Usize) (index : i.val ≤ sites.val.length)
    (branches : BranchSites compiler.function.code.val sites.val) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0
      ops compiler sites target i (.Ok ()) ⦃ out =>
      ∃ after, out = compilerSnapshot after (.Ok ()) ∧ OnlyCode compiler after ∧
        after.function.code.val = patchCode compiler.function.code.val (sites.val.drop i.val) target ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0
  apply loop.spec_decr_nat (fun p => sites.val.length - p.2.1.val)
    (fun p => p.2.1.val ≤ sites.val.length ∧ p.2.2 = .Ok () ∧
      OnlyCode compiler p.1 ∧ BranchSites p.1.function.code.val sites.val ∧
      patchCode p.1.function.code.val (sites.val.drop p.2.1.val) target =
        patchCode compiler.function.code.val (sites.val.drop i.val) target)
  · rintro ⟨current, j, result⟩ ⟨hj, rfl, onlyCode, currentSites, effect⟩
    dsimp only at hj onlyCode currentSites effect
    unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0.body
    dsimp only
    split
    · rename_i more
      have hlt : j.val < sites.val.length := by scalar_tac
      simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
      step as ⟨site, hsite⟩
      have member : site ∈ sites.val := by rw [hsite]; exact List.getElem_mem hlt
      obtain ⟨kind, old, atPc⟩ := currentSites site member
      step with compiler_patch ops current site kind old target atPc as ⟨r, changed, hr, patched⟩
      subst r
      step as ⟨j1, hj1⟩
      refine ⟨?_, onlyCode.trans patched.only_code, ?_, ?_, ?_⟩
      · omega
      · exact patched.branch_sites (List.getElem?_eq_some_iff.mp atPc).1 currentSites
      · obtain ⟨code, hchanged, hcode⟩ := patched
        rw [List.drop_eq_getElem_cons hlt, ← hsite, patchCode, atPc] at effect
        have retargeted : retarget (kind.instruction old) target = kind.instruction target := by
          cases kind <;> rfl
        simpa [hj1, hcode, retargeted, hchanged] using effect
      · omega
    · rename_i stop
      have done : j.val = sites.val.length := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨current, rfl, onlyCode, ?_⟩
      simpa [done, patchCode] using effect
  · exact ⟨index, rfl, OnlyCode.refl compiler, branches, rfl⟩
@[step] theorem compiler_fixups_after_if {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (sites : alloc.vec.Vec Usize)
    (target : U32) (i : Usize) (index : i.val ≤ sites.val.length)
    (branches : BranchSites compiler.function.code.val sites.val) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop1
      ops compiler sites target i (.Ok ()) ⦃ out =>
      ∃ after, out = compilerSnapshot after (.Ok ()) ∧ OnlyCode compiler after ∧
        after.function.code.val = patchCode compiler.function.code.val (sites.val.drop i.val) target ⦄ := by
  exact compiler_fixups ops compiler sites target i index branches

theorem patch_code_length (code : List runtime.bytecode.Instr) (sites : List Usize) (target : U32) :
    (patchCode code sites target).length = code.length := by
  induction sites generalizing code with
  | nil => rfl
  | cons site rest ih =>
    simp only [patchCode]
    split <;> simp [ih]

theorem patch_code_other (code : List runtime.bytecode.Instr) (sites : List Usize)
    (target : U32) (pc : Nat) (separate : ∀ site, site ∈ sites → pc ≠ site.val) :
    (patchCode code sites target)[pc]? = code[pc]? := by
  induction sites generalizing code with
  | nil => rfl
  | cons site rest ih =>
    have different := separate site (by simp)
    have restSeparate : ∀ site, site ∈ rest → pc ≠ site.val := by
      intro site member
      exact separate site (List.mem_cons_of_mem _ member)
    simp only [patchCode]
    split
    · rw [ih _ restSeparate]
      simp [Ne.symm different]
    · exact ih code restSeparate

end Itasca.Runtime.Compiler

end

/-! ## FixupAlgebra -/

section

/-!
Retargeting and branch-site patch algebra.

Main declarations: `retarget_retarget` and `patch_code_new_branch`. A direct consumer is `Compiler.Local.Checking.OpenInstructionPatch`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas.Std

theorem retarget_retarget (instruction : Bytecode) (first second : U32) :
    retarget (retarget instruction first) second = retarget instruction second := by
  cases instruction <;> rfl

theorem patch_code_get (code : List Bytecode) (sites : List Usize) (target : U32) (index : Nat) :
    (patchCode code sites target)[index]? =
      if ∃ site ∈ sites, site.val = index then (code[index]?).map (fun i => retarget i target)
      else code[index]? := by
  induction sites generalizing code with
  | nil => simp [patchCode]
  | cons site rest ih =>
    simp only [patchCode]
    split
    · rename_i instruction found
      rw [ih]
      by_cases equal : site.val = index
      · subst index
        have inside := (List.getElem?_eq_some_iff.mp found).1
        simp [inside, (List.getElem?_eq_some_iff.mp found).2, retarget_retarget]
      · simp [equal]
    · rename_i absent
      rw [ih]
      by_cases equal : site.val = index
      · subst index
        simp [absent]
      · simp [equal]

theorem patch_code_append_code (code suffix : List Bytecode) (sites : List Usize) (target : U32)
    (inside : ∀ site, site ∈ sites → site.val < code.length) :
    patchCode (code ++ suffix) sites target = patchCode code sites target ++ suffix := by
  apply List.ext_getElem?
  intro index
  rw [patch_code_get, List.getElem?_append, List.getElem?_append, patch_code_length]
  by_cases before : index < code.length
  · simp [before, patch_code_get]
  · have absent : ¬ ∃ site ∈ sites, site.val = index := by
      rintro ⟨site, member, position⟩
      have := inside site member
      omega
    simp [before, absent]

theorem patch_code_append_sites (code : List Bytecode) (left right : List Usize) (target : U32) :
    patchCode code (left ++ right) target = patchCode (patchCode code left target) right target := by
  induction left generalizing code with
  | nil => rfl
  | cons site rest ih => simp only [List.cons_append, patchCode]; exact ih _

/-- Appending a newly emitted branch and its fixup resolves just that new
branch after the already pending sites; preceding transfer or guard code stays
literal. This is the forward-branch update of the resolved compiler emitted. -/
theorem patch_code_new_branch (code emitted : List Bytecode) (sites : List Usize)
    (kind : BranchKind) (old target : U32) (site : Usize)
    (position : site.val = code.length + emitted.length)
    (inside : ∀ pc, pc ∈ sites → pc.val < code.length) :
    patchCode (code ++ emitted ++ [kind.instruction old]) (sites ++ [site]) target =
      patchCode code sites target ++ emitted ++ [kind.instruction target] := by
  rw [patch_code_append_sites]
  have prior := patch_code_append_code code (emitted ++ [kind.instruction old]) sites target inside
  rw [List.append_assoc, prior]
  have sitePosition : site.val = (patchCode code sites target ++ emitted).length := by
    simp [position, patch_code_length]
  simp only [patchCode, ← List.append_assoc]
  rw [sitePosition]
  simp only [List.getElem?_concat_length]
  have changed : retarget (kind.instruction old) target = kind.instruction target := by cases kind <;> rfl
  simp [changed]

theorem compiler_patch_code_length {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (pc : Usize) (target : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.patch ops before pc target = .ok (status, after)) :
    after.function.code.val.length = before.function.code.val.length := by
  rcases compiler_patch_cases ops before after pc target status accepted with rfl | ⟨_, _, rfl, set⟩
  · rfl
  · simp [set]

theorem compiler_fixups_after_if_code_length {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (sites : alloc.vec.Vec Usize)
    (target : U32) (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (output : CompilerSnapshot A)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop1
      ops before sites target index status = .ok output) :
    (snapshotCompiler output).function.code.val.length = before.function.code.val.length :=
  compiler_fixups_code_length ops before sites target index status output accepted

end Itasca.Runtime.Compiler

end
