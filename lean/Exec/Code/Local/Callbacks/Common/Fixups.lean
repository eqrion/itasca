import Exec.Code.Local.Relations.Control.Control
/-! The actual end-label fixup loops terminate normally and change only code.
Every listed branch receives the exit PC, including duplicate fixup addresses;
branch conditions, code length, unrelated instructions, and compiler layout are
preserved. The initial branch-shape premise is a syntactic hole invariant. -/

namespace Exec.Code
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

theorem patchCode_length (code : List runtime.bytecode.Instr) (sites : List Usize) (target : U32) :
    (patchCode code sites target).length = code.length := by
  induction sites generalizing code with
  | nil => rfl
  | cons site rest ih =>
    simp only [patchCode]
    split <;> simp [ih]

theorem patchCode_keeps_target (code : List runtime.bytecode.Instr) (sites : List Usize)
    (target : U32) (pc : Nat) (kind : BranchKind)
    (atPc : code[pc]? = some (kind.instruction target)) :
    (patchCode code sites target)[pc]? = some (kind.instruction target) := by
  induction sites generalizing code with
  | nil => exact atPc
  | cons site rest ih =>
    simp only [patchCode]
    split
    · rename_i instruction found
      apply ih
      by_cases same : pc = site.val
      · have eq : instruction = kind.instruction target := by
          rw [← same, atPc] at found
          exact Option.some.inj found.symm
        subst instruction
        have bound := (List.getElem?_eq_some_iff.mp atPc).1
        cases kind <;> simp [← same, retarget, BranchKind.instruction, bound]
      · simpa [Ne.symm same] using atPc
    · exact ih code atPc

theorem patchCode_target (code : List runtime.bytecode.Instr) (sites : List Usize)
    (target old : U32) (pc : Usize) (kind : BranchKind)
    (member : pc ∈ sites) (atPc : code[pc.val]? = some (kind.instruction old)) :
    (patchCode code sites target)[pc.val]? = some (kind.instruction target) := by
  induction sites generalizing code with
  | nil => simp at member
  | cons site rest ih =>
    simp only [patchCode]
    rcases List.mem_cons.mp member with same | member
    · subst site
      rw [atPc]
      apply patchCode_keeps_target
      have bound := (List.getElem?_eq_some_iff.mp atPc).1
      cases kind <;> simp [retarget, BranchKind.instruction, bound]
    · split
      · rename_i instruction found
        by_cases same : pc.val = site.val
        · have eq : instruction = kind.instruction old := by
            rw [← same, atPc] at found
            exact Option.some.inj found.symm
          subst instruction
          apply patchCode_keeps_target
          have bound := (List.getElem?_eq_some_iff.mp atPc).1
          cases kind <;> simp [← same, retarget, BranchKind.instruction, bound]
        · apply ih _ member
          simpa [Ne.symm same] using atPc
      · exact ih code member atPc

theorem OnlyCode.layout {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {stack} (changed : OnlyCode before after) (layout : CompilerLayout before stack) :
    CompilerLayout after stack := by
  obtain ⟨code, rfl⟩ := changed
  exact ⟨layout.localSlots, layout.localOffsets, layout.operandOffsets, layout.height, layout.capacity⟩

theorem patchCode_other (code : List runtime.bytecode.Instr) (sites : List Usize)
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

@[step] theorem compiler_fixups_complete {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (sites : alloc.vec.Vec Usize)
    (target : U32) (branches : BranchSites compiler.function.code.val sites.val) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0
      ops compiler sites target 0#usize (.Ok ()) ⦃ out =>
      ∃ after, out = compilerSnapshot after (.Ok ()) ∧ OnlyCode compiler after ∧
        after.function.code.val.length = compiler.function.code.val.length ∧
        (∀ pc kind old, pc ∈ sites.val →
          compiler.function.code.val[pc.val]? = some (BranchKind.instruction kind old) →
          after.function.code.val[pc.val]? = some (kind.instruction target)) ∧
        (∀ pc, (∀ site, site ∈ sites.val → pc ≠ site.val) →
          after.function.code.val[pc]? = compiler.function.code.val[pc]?) ⦄ := by
  step with compiler_fixups ops compiler sites target 0#usize (by simp) branches as
    ⟨out, after, hout, onlyCode, effect⟩
  simp only [List.drop_zero] at effect
  refine ⟨after, hout, onlyCode, ?_, ?_, ?_⟩
  · rw [effect, patchCode_length]
  · intro pc kind old member atPc
    rw [effect]
    exact patchCode_target _ _ _ _ _ _ member atPc
  · intro pc separate
    rw [effect]
    exact patchCode_other _ _ _ _ separate

end Exec.Code
