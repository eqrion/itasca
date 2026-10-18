import Runtime.Funs
import Platform.Funs
import Lean.Util.CollectAxioms
open Aeneas Aeneas.Std
#print axioms Platform.invoke
#print axioms loop.fixpoint_induct
#print axioms loop.spec
#print axioms Runtime.validator.validate
#check loop.fixpoint_induct
example {V : Type} (v : Runtime.validator.Visitor V) (state : V)
    (token : Runtime.validator.Token) :
    Runtime.validator.validate v state token =
      Validator.validator.validate ⟨v.visit⟩ state token := rfl
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let moduleNames := env.header.moduleNames
  let declarations ← env.constants.foldM (init := #[]) fun names n _ => do
    if let some idx := env.getModuleIdxFor? n then
      if [`Validator, `Runtime, `Platform].any (·.isPrefixOf moduleNames[idx.toNat]!) then
        return names.push n
    return names
  for decl in declarations do
    for ax in ← Lean.collectAxioms decl do
      unless allowed.contains ax do
        throwError "{decl} depends on unapproved axiom {ax}"
  logInfo m!"Audited {declarations.size} probe declarations; only standard Lean logical axioms."
