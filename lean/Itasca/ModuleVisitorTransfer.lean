import Itasca.ModuleCompleteness
import Itasca.ModuleCodeVisitor
import Itasca.ModuleCustomVisitor

open Aeneas Aeneas.Std

namespace Itasca

/-- Module/custom callbacks only reject, while a CodeVisitor override must
certify its accepted entries. No callback-totality premise is needed when the
actual visiting execution has already accepted. -/
theorem module.validate_module_with.accepted_erase {V : Type}
    (mv : module.ModuleVisitor V) (cv : module.CodeVisitor V)
    (data : Slice U8) (v v' : V) (decoded : module.Module)
    (hv : ModuleCodeVisitor.Validates cv data decoded.env)
    (h : module.validate_module_with mv cv data v = .ok (.Ok decoded, v')) :
    module.validate_module data = .ok (.Ok decoded) := by
  obtain ⟨hsize, codePos, tailPos, v1, v2, henv, hcode, htail⟩ :=
    ModulePipeline.accepted_parts_with mv cv data v v' decoded h
  have he := module.validate_env_with.accepted_erase mv data v decoded.env codePos v1 henv
  have hc := module.validate_code_with.accepted_erase cv data codePos decoded.env tailPos hv v1 v2 hcode
  have ht := module.validate_tail_with.accepted_erase mv data tailPos decoded.env v2 decoded.tail v' htail
  exact ModulePipeline.accepted_of_parts data decoded.env decoded.tail codePos tailPos hsize he hc ht

/-- Accepting hooks preserve every successful default module validation and
return exactly the same environment and tail. -/
theorem module.validate_module_with.accepted_lift {V : Type}
    (mv : module.ModuleVisitor V) (cv : module.CodeVisitor V)
    (data : Slice U8) (v : V) (decoded : module.Module)
    (hm : ModuleTail.HooksAccept mv) (hc : ModuleCodeVisitor.Accepts cv data decoded.env)
    (h : module.validate_module data = .ok (.Ok decoded)) :
    ∃ v', module.validate_module_with mv cv data v = .ok (.Ok decoded, v') := by
  obtain ⟨hsize, codePos, tailPos, henv, hcode, htail⟩ := ModulePipeline.accepted_parts data decoded h
  obtain ⟨v1, he⟩ := module.validate_env_with.accepted_lift mv hm data v decoded.env codePos henv
  obtain ⟨v2, hco⟩ := module.validate_code_with.accepted_lift cv data codePos decoded.env tailPos hc v1 hcode
  obtain ⟨v3, ht⟩ := module.validate_tail_with.accepted_lift mv hm data tailPos decoded.env v2 decoded.tail htail
  exact ⟨v3, ModulePipeline.accepted_of_parts_with mv cv data decoded.env decoded.tail
    codePos tailPos v v1 v2 v3 hsize he hco ht⟩

/-- An accepted validating consumer can be replaced by any accepting consumer,
including a recorder or compiler with a different state type. -/
theorem module.validate_module_with.accepted_transfer {V W : Type}
    (mv : module.ModuleVisitor V) (cv : module.CodeVisitor V)
    (replacementM : module.ModuleVisitor W) (replacementC : module.CodeVisitor W)
    (data : Slice U8) (v v' : V) (w : W) (decoded : module.Module)
    (hv : ModuleCodeVisitor.Validates cv data decoded.env)
    (hm : ModuleTail.HooksAccept replacementM)
    (hc : ModuleCodeVisitor.Accepts replacementC data decoded.env)
    (h : module.validate_module_with mv cv data v = .ok (.Ok decoded, v')) :
    ∃ w', module.validate_module_with replacementM replacementC data w = .ok (.Ok decoded, w') :=
  module.validate_module_with.accepted_lift replacementM replacementC data w decoded hm hc
    (module.validate_module_with.accepted_erase mv cv data v v' decoded hv h)

/-- Whole-module soundness for accepted validating visitors has exactly the
same byte/typing/profile/metadata conclusion as the default public API. -/
theorem module.validate_module_with.wasm_sound {V : Type}
    (mv : module.ModuleVisitor V) (cv : module.CodeVisitor V)
    (data : Slice U8) (v v' : V) (decoded : module.Module)
    (hv : ModuleCodeVisitor.Validates cv data decoded.env)
    (h : module.validate_module_with mv cv data v = .ok (.Ok decoded, v')) :
    ModuleSound.Validated data decoded :=
  module.validate_module.wasm_sound data decoded
    (module.validate_module_with.accepted_erase mv cv data v v' decoded hv h)

/-- Declarative completeness survives accepting callbacks. The entry callback
may validate or defer: accepting entries already accepted by the default entry
validator suffices for this direction. -/
theorem module.validate_module_with.wasm_complete {V : Type}
    (mv : module.ModuleVisitor V) (cv : module.CodeVisitor V)
    (data : Slice U8) (raw : ModuleBinary.Module) (v : V)
    (hm : ModuleTail.HooksAccept mv)
    (hc : ∀ env, ModuleCodeVisitor.Accepts cv data env)
    (hb : ModuleBinary.ModuleEncodingWithinLimits raw data.val)
    (he : ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw))
    (ht : Module_ok (ModuleElaboration.moduleOf raw)) (hp : ModuleElaboration.Profile raw) :
    ∃ decoded v', module.validate_module_with mv cv data v = .ok (.Ok decoded, v') ∧
      ModuleElaboration.Matches decoded.env decoded.tail raw ∧
      ModuleElaboration.AccessorTypes decoded.env raw := by
  obtain ⟨decoded, ha, hmatch, hmeta⟩ := module.validate_module.wasm_complete_with_metadata data raw hb he ht hp
  obtain ⟨v', hv⟩ := module.validate_module_with.accepted_lift mv cv data v decoded hm (hc decoded.env) ha
  exact ⟨decoded, v', hv, hmatch, hmeta⟩

end Itasca
