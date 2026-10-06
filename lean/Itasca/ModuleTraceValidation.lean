import Itasca.ModuleCustomTrace
import Itasca.ModuleCodeTrace
import Itasca.ModuleTraceRecorders
import Itasca.ModuleVisitorTransfer
import Itasca.ModuleVisitorValidation
import Itasca.ModuleDeferredValidation

open Aeneas Aeneas.Std

namespace Itasca.ModuleTrace

/-- An accepted module callback log traverses the actual independent section
regions in byte order. Code handoffs alone do not claim body typing; soundness
is supplied separately by immediate validation or completed worker obligations. -/
def Accepted (data : Slice U8) (decoded : module.Module) (events : List Event) : Prop :=
  ∃ codePos tailPos envEvents codeEvents tailEvents,
    events = envEvents ++ codeEvents ++ tailEvents ∧
    EnvTrace data codePos envEvents ∧
    CodeTrace data decoded.env.func_type_indices.val.length codePos tailPos codeEvents ∧
    TailTrace data tailPos tailEvents

end Itasca.ModuleTrace

namespace Itasca

/-- Every accepted recording module walk reports exactly its custom-section
ranges, readiness requests and ordered framed code-entry handoffs. The source
hooks need not be total or validating; these are byte/dispatch observations. -/
theorem module.validate_module_with.trace {V : Type}
    (mv : module.ModuleVisitor V) (cv : module.CodeVisitor V)
    (observe : V → List ModuleTrace.Event)
    (hm : ModuleTrace.RecordsCustom mv observe) (hc : ModuleTrace.RecordsCode cv observe)
    (data : Slice U8) (v v' : V) (decoded : module.Module)
    (h : module.validate_module_with mv cv data v = .ok (.Ok decoded, v')) :
    ∃ events, observe v' = observe v ++ events ∧ ModuleTrace.Accepted data decoded events := by
  obtain ⟨_, codePos, tailPos, v1, v2, henv, hcode, htail⟩ :=
    ModulePipeline.accepted_parts_with mv cv data v v' decoded h
  obtain ⟨ee, heLog, heTrace⟩ := module.validate_env_with.accepted_trace
    mv observe hm data v decoded.env codePos v1 henv
  have hcodePos : codePos.val ≤ data.length := by
    obtain ⟨_, _, ht⟩ := heTrace
    exact ht.span.2
  obtain ⟨ce, hcLog, hcTrace⟩ := module.validate_code_with.accepted_trace
    cv observe hc data codePos decoded.env v1 v2 tailPos hcodePos hcode
  obtain ⟨te, htLog, htTrace⟩ := module.validate_tail_with.accepted_trace
    mv observe hm data tailPos decoded.env v2 decoded.tail v' hcTrace.span.2 htail
  refine ⟨ee ++ ce ++ te, ?_, codePos, tailPos, ee, ce, te, rfl, heTrace, hcTrace, htTrace⟩
  simp only [htLog, hcLog, heLog, List.append_assoc]

/-- Validating overrides give typing and complete callback provenance for the
same actual accepted module, without a source-totality premise. -/
theorem module.validate_module_with.trace_sound {V : Type}
    (mv : module.ModuleVisitor V) (cv : module.CodeVisitor V)
    (observe : V → List ModuleTrace.Event)
    (hm : ModuleTrace.RecordsCustom mv observe) (hc : ModuleTrace.RecordsCode cv observe)
    (data : Slice U8) (v v' : V) (decoded : module.Module)
    (hv : ModuleCodeVisitor.Validates cv data decoded.env)
    (h : module.validate_module_with mv cv data v = .ok (.Ok decoded, v')) :
    ∃ events, observe v' = observe v ++ events ∧ ModuleTrace.Accepted data decoded events ∧
      ModuleSound.Validated data decoded := by
  obtain ⟨events, he, ht⟩ := module.validate_module_with.trace mv cv observe hm hc data v v' decoded h
  exact ⟨events, he, ht, module.validate_module_with.wasm_sound mv cv data v v' decoded hv h⟩

/-- Recording all module callbacks automatically preserves the projected work
list across custom sections. Deferred workers may validate precisely that
projection after the whole walk has returned. -/
theorem module.validate_module_with.deferred_trace_sound {V : Type}
    (mv : module.ModuleVisitor V) (cv : module.CodeVisitor V)
    (observe : V → List ModuleTrace.Event)
    (hm : ModuleTrace.RecordsCustom mv observe) (hc : ModuleTrace.RecordsCode cv observe)
    (data : Slice U8) (v v' : V) (decoded : module.Module)
    (h : module.validate_module_with mv cv data v = .ok (.Ok decoded, v'))
    (hworkers : ModuleCodeVisitor.EntriesValidate data decoded.env (ModuleTrace.entries (observe v'))) :
    ∃ events, observe v' = observe v ++ events ∧ ModuleTrace.Accepted data decoded events ∧
      ModuleSound.Validated data decoded := by
  obtain ⟨events, he, ht⟩ := module.validate_module_with.trace mv cv observe hm hc data v v' decoded h
  exact ⟨events, he, ht, module.validate_module_with.deferred_wasm_sound mv cv
    (fun w => ModuleTrace.entries (observe w)) hc.entries hm.entries data v v' decoded h hworkers⟩

/-- Every accepted default module has a real validating recording execution,
with all callbacks accounted for by independent byte framing. -/
theorem module.validate_module.recorded (data : Slice U8) (decoded : module.Module)
    (h : module.validate_module data = .ok (.Ok decoded)) :
    ∃ events, module.validate_module_with ModuleTrace.customRecorder ModuleTrace.validatingRecorder
        data [] = .ok (.Ok decoded, events) ∧
      ModuleTrace.Accepted data decoded events ∧ ModuleSound.Validated data decoded := by
  obtain ⟨events, hr⟩ := module.validate_module_with.accepted_lift
    ModuleTrace.customRecorder ModuleTrace.validatingRecorder data [] decoded
    ModuleTrace.customRecorder_accepts (ModuleTrace.validatingRecorder_accepts data decoded.env) h
  obtain ⟨added, he, ht, hs⟩ := module.validate_module_with.trace_sound
    ModuleTrace.customRecorder ModuleTrace.validatingRecorder id ModuleTrace.customRecorder_records
    ModuleTrace.validatingRecorder_records data [] events decoded
    (ModuleTrace.validatingRecorder_validates data decoded.env) hr
  have he : events = added := by simpa using he
  exact ⟨events, hr, by simpa only [he] using ht, hs⟩

/-- Declarative module completeness also produces the complete accepted
callback trace for any accepting recording consumer. -/
theorem module.validate_module_with.trace_complete {V : Type}
    (mv : module.ModuleVisitor V) (cv : module.CodeVisitor V)
    (observe : V → List ModuleTrace.Event)
    (hm : ModuleTrace.RecordsCustom mv observe) (hc : ModuleTrace.RecordsCode cv observe)
    (data : Slice U8) (ham : ModuleTail.HooksAccept mv)
    (hac : ∀ env, ModuleCodeVisitor.Accepts cv data env)
    (raw : ModuleBinary.Module) (v : V)
    (hb : ModuleBinary.ModuleEncodingWithinLimits raw data.val)
    (he : ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw))
    (ht : Module_ok (ModuleElaboration.moduleOf raw)) (hp : ModuleElaboration.Profile raw) :
    ∃ decoded v' events, module.validate_module_with mv cv data v = .ok (.Ok decoded, v') ∧
      observe v' = observe v ++ events ∧ ModuleTrace.Accepted data decoded events ∧
      ModuleElaboration.Matches decoded.env decoded.tail raw ∧
      ModuleElaboration.AccessorTypes decoded.env raw := by
  obtain ⟨decoded, v', ha, hmatch, hmeta⟩ :=
    module.validate_module_with.wasm_complete mv cv data raw v ham hac hb he ht hp
  obtain ⟨events, hlog, htrace⟩ := module.validate_module_with.trace mv cv observe hm hc data v v' decoded ha
  exact ⟨decoded, v', events, ha, hlog, htrace, hmatch, hmeta⟩

end Itasca
