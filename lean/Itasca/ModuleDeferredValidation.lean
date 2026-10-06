import Itasca.ModuleDeferred
import Itasca.ModuleCustomObservation
import Itasca.ModuleRegions

open Aeneas Aeneas.Std

namespace Itasca

/-- A decomposed code walk may return before its workers validate the entries.
Once all recorded work succeeds, adjacent accepted phases certify the module. -/
theorem module.validate_module.deferred_wasm_sound {V : Type}
    (cv : module.CodeVisitor V) (observe : V → List ModuleCodeVisitor.Entry)
    (hr : ModuleCodeVisitor.Records cv observe)
    (data : Slice U8) (env : module.Env) (tail : module.Tail)
    (codePos tailPos : Usize) (v v' : V)
    (hsize : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (henv : module.validate_env data = .ok (.Ok (env, codePos)))
    (hcode : module.validate_code_with cv data codePos env v = .ok (.Ok tailPos, v'))
    (hworkers : ModuleCodeVisitor.EntriesValidate data env (observe v'))
    (htail : module.validate_tail data tailPos env = .ok (.Ok tail)) :
    ModuleSound.Validated data ⟨env, tail⟩ :=
  module.validate_module.wasm_sound_of_parts data env tail codePos tailPos hsize henv
    (module.validate_code_with.deferred_erase cv observe hr data codePos env v v' tailPos hcode hworkers) htail

/-- Separate environment/code/tail buffers and deferred entry workers compose
with exactly the same byte provenance and module typing as the default API. -/
theorem module.validate_module.regions_deferred_wasm_sound {V : Type}
    (cv : module.CodeVisitor V) (observe : V → List ModuleCodeVisitor.Entry)
    (hr : ModuleCodeVisitor.Records cv observe)
    (data environment codeBytes tailBytes : Slice U8) (env : module.Env) (tail : module.Tail)
    (v v' : V) (hbytes : data.val = environment.val ++ codeBytes.val ++ tailBytes.val)
    (hsize : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (henv : module.validate_env environment = .ok (.Ok (env, Slice.len environment)))
    (hcode : module.validate_code_with cv codeBytes 0#usize env v = .ok (.Ok (Slice.len codeBytes), v'))
    (hworkers : ModuleCodeVisitor.EntriesValidate codeBytes env (observe v'))
    (htail : module.validate_tail tailBytes 0#usize env = .ok (.Ok tail)) :
    ModuleSound.Validated data ⟨env, tail⟩ :=
  module.validate_module.regions_wasm_sound data environment codeBytes tailBytes env tail
    hbytes hsize henv
    (module.validate_code_with.deferred_erase cv observe hr codeBytes 0#usize env v v'
      (Slice.len codeBytes) hcode hworkers) htail

/-- The final state of a whole-module walk can carry deferred worker results.
Custom callbacks must preserve that work observation so the tail cannot erase
an outstanding entry. No callback-totality or immediate-validation assumption
is used for this accepted-run theorem. -/
theorem module.validate_module_with.deferred_erase {V : Type}
    (mv : module.ModuleVisitor V) (cv : module.CodeVisitor V)
    (observe : V → List ModuleCodeVisitor.Entry)
    (hr : ModuleCodeVisitor.Records cv observe) (hm : ModuleTail.Preserves mv observe)
    (data : Slice U8) (v v' : V) (decoded : module.Module)
    (h : module.validate_module_with mv cv data v = .ok (.Ok decoded, v'))
    (hworkers : ModuleCodeVisitor.EntriesValidate data decoded.env (observe v')) :
    module.validate_module data = .ok (.Ok decoded) := by
  obtain ⟨hsize, codePos, tailPos, v1, v2, henv, hcode, htail⟩ :=
    ModulePipeline.accepted_parts_with mv cv data v v' decoded h
  have ho := module.validate_tail_with.accepted_preserves mv observe hm
    data tailPos decoded.env v2 decoded.tail v' htail
  have hworkers' : ModuleCodeVisitor.EntriesValidate data decoded.env (observe v2) := by
    simpa only [ho] using hworkers
  exact ModulePipeline.accepted_of_parts data decoded.env decoded.tail codePos tailPos hsize
    (module.validate_env_with.accepted_erase mv data v decoded.env codePos v1 henv)
    (module.validate_code_with.deferred_erase cv observe hr data codePos decoded.env v1 v2 tailPos hcode hworkers')
    (module.validate_tail_with.accepted_erase mv data tailPos decoded.env v2 decoded.tail v' htail)

theorem module.validate_module_with.deferred_wasm_sound {V : Type}
    (mv : module.ModuleVisitor V) (cv : module.CodeVisitor V)
    (observe : V → List ModuleCodeVisitor.Entry)
    (hr : ModuleCodeVisitor.Records cv observe) (hm : ModuleTail.Preserves mv observe)
    (data : Slice U8) (v v' : V) (decoded : module.Module)
    (h : module.validate_module_with mv cv data v = .ok (.Ok decoded, v'))
    (hworkers : ModuleCodeVisitor.EntriesValidate data decoded.env (observe v')) :
    ModuleSound.Validated data decoded :=
  module.validate_module.wasm_sound data decoded
    (module.validate_module_with.deferred_erase mv cv observe hr hm data v v' decoded h hworkers)

end Itasca
