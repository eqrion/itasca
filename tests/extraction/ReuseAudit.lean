import Reuse.Funs
import Lean.Util.CollectAxioms
open Aeneas Aeneas.Std
example {V : Type} (v : ReuseBase.validator.Visitor V) (state : V)
    (token : ReuseBase.validator.Token) :
    Reuse.validator.validate v state token = ReuseBase.validator.validate v state token := rfl
example : Reuse.runtime.compile ⟨.Small, 5#u32⟩ = .ok ⟨5#u32⟩ := by
  simp [Reuse.runtime.compile, Reuse.validator.validate, ReuseBase.validator.validate,
    Reuse.runtime.Compiler.Insts.ReuseValidatorVisitor.visit]
example : Reuse.runtime.compile ⟨.Large, 5#u32⟩ = .ok ⟨6#u32⟩ := by
  simp [Reuse.runtime.compile, Reuse.validator.validate, ReuseBase.validator.validate,
    Reuse.runtime.Compiler.Insts.ReuseValidatorVisitor.visit, lift]
  rfl
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules := env.header.moduleNames
  let decls ← env.constants.foldM (init := #[]) fun names n _ => do
    if let some idx := env.getModuleIdxFor? n then
      if [`ReuseBase, `Reuse].any (·.isPrefixOf modules[idx.toNat]!) then
        return names.push n
    return names
  for decl in decls do
    for ax in ← Lean.collectAxioms decl do
      unless allowed.contains ax do
        throwError "{decl} depends on unapproved axiom {ax}"
  logInfo m!"Audited {decls.size} type reuse declarations."
