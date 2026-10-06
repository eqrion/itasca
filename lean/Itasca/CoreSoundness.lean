import Itasca.CoreBody
import Itasca.CoreStepSimple
import Itasca.CoreStepBranch
import Itasca.CoreStepControl

open Aeneas Aeneas.Std

namespace Itasca.Core

/-- Exhaustive preservation and termination for every opcode in the profile.
All cases execute the extracted dispatcher and retain its visitor behavior. -/
theorem steps {V : Type} (visitor : code.OpVisitor V) (hvisitor : CoreVisitor.Total visitor)
    (data : Slice U8) (tokens : List Token) (env : module.Env) (ctx : code.Context)
    (bt : code.BlockType) : Steps visitor data tokens env ctx bt := by
  intro st token p v
  cases token with
  | nop => exact p.step_nop visitor hvisitor env v
  | unreachable => exact p.step_unreachable visitor hvisitor env v
  | drop => exact p.step_drop visitor hvisitor env v
  | i32Add => exact p.step_i32Add visitor hvisitor env v
  | i32Const value => exact p.step_i32Const visitor hvisitor env v
  | block result => exact p.step_block visitor env v hvisitor
  | loop result => exact p.step_loop visitor env v hvisitor
  | if_ result => exact p.step_if visitor env v hvisitor
  | else_ => exact p.step_else visitor env v hvisitor
  | end_ => exact p.step_end visitor env v hvisitor
  | br depth => exact p.step_br visitor hvisitor env v
  | brIf depth => exact p.step_brIf visitor hvisitor env v
  | return_ => exact p.step_return visitor hvisitor env v

/-- Lexical membership does not assume correct stack typing, branch depths, or
balanced constructs. Signed and unsigned immediates may be nonminimal. -/
def Profile (data : Slice U8) : Prop := ∃ tokens, Rest data 0#usize tokens

end Itasca.Core

namespace Itasca

/-- The public visiting validator terminates on every core-profile token stream.
Acceptance implies exact binary provenance and generated SpecTec body typing.
Only termination is required of hooks; hooks may reject or change their state. -/
theorem code.validate_body_with.core_spec {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : CoreVisitor.Total visitor) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (bt : code.BlockType)
    (hresults : ctx.results.val = Control.results bt)
    (hprofile : Core.Profile data) (v : V) :
    code.validate_body_with visitor data env ctx v ⦃ r =>
      r.1 = .Ok () → Core.Validated data ctx bt ⦄ := by
  obtain ⟨tokens, hbytes⟩ := hprofile
  exact code.validate_body_with.of_core_steps visitor data tokens env ctx bt hresults hbytes
    (Core.steps visitor hvisitor data tokens env ctx bt) v

theorem code.validate_body_with.core_total {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : CoreVisitor.Total visitor) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (bt : code.BlockType)
    (hresults : ctx.results.val = Control.results bt)
    (hprofile : Core.Profile data) (v : V) :
    ∃ r, code.validate_body_with visitor data env ctx v = .ok r := by
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists
    (code.validate_body_with.core_spec visitor hvisitor data env ctx bt hresults hprofile v)
  exact ⟨r, hr⟩

theorem code.validate_body_with.core_sound {V : Type} (visitor : code.OpVisitor V)
    (hvisitor : CoreVisitor.Total visitor) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (bt : code.BlockType)
    (hresults : ctx.results.val = Control.results bt)
    (hprofile : Core.Profile data) (v v' : V)
    (haccepted : code.validate_body_with visitor data env ctx v = .ok (.Ok (), v')) :
    Core.Validated data ctx bt := by
  have h := code.validate_body_with.core_spec visitor hvisitor data env ctx bt hresults hprofile v
  simpa [haccepted] using h

/-- End-to-end termination and soundness of the extracted non-visiting body API
for the documented core profile, with no abstract step-preservation premise. -/
theorem code.validate_body.core_spec (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (bt : code.BlockType)
    (hresults : ctx.results.val = Control.results bt) (hprofile : Core.Profile data) :
    code.validate_body data env ctx ⦃ r => r = .Ok () → Core.Validated data ctx bt ⦄ := by
  obtain ⟨⟨r, v⟩, hr, hp⟩ := WP.spec_imp_exists
    (code.validate_body_with.core_spec code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      CoreVisitor.empty_total data env ctx bt hresults hprofile ())
  simpa [code.validate_body, hr] using hp

theorem code.validate_body.core_total (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (bt : code.BlockType)
    (hresults : ctx.results.val = Control.results bt) (hprofile : Core.Profile data) :
    ∃ r, code.validate_body data env ctx = .ok r := by
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists
    (code.validate_body.core_spec data env ctx bt hresults hprofile)
  exact ⟨r, hr⟩

theorem code.validate_body.core_sound (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (bt : code.BlockType)
    (hresults : ctx.results.val = Control.results bt) (hprofile : Core.Profile data)
    (haccepted : code.validate_body data env ctx = .ok (.Ok ())) :
    Core.Validated data ctx bt := by
  have h := code.validate_body.core_spec data env ctx bt hresults hprofile
  simpa [haccepted] using h

end Itasca
