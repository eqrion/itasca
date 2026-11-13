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
open Aeneas Aeneas.Std

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

end Itasca.Runtime.Compiler

end
