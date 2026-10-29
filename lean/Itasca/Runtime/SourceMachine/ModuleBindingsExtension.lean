import Itasca.Runtime.Spec.ExtensionTyping
import Itasca.Runtime.SourceMachine.Typing
namespace Itasca.Runtime.Abs

/-- Module bindings survive specification store extension, including growth,
content writes, and dropping segments. -/
theorem ModuleBindings.extend {s t : store} {module : moduleinst} {C : context}
    (bindings : ModuleBindings s module C) (extension : Extend_store s t) :
    ModuleBindings t module C := by
  refine ⟨bindings.types, ?_, ?_, ?_, ?_, ?_, ?_, bindings.wf⟩
  · apply bindings.funcs.imp
    rintro address ty ⟨fn, found, typed⟩
    exact ⟨fn, Spec.function_lookup_extend extension found, typed⟩
  · exact bindings.globals.imp (fun _ _ typed => Spec.externaddr_ok_extend extension typed)
  · exact bindings.tables.imp (fun _ _ typed => Spec.externaddr_ok_extend extension typed)
  · exact bindings.mems.imp (fun _ _ typed => Spec.externaddr_ok_extend extension typed)
  · apply bindings.elems.imp
    rintro address ty ⟨entry, found, typed⟩
    exact Spec.element_lookup_extend extension found typed
  · apply bindings.datas.imp
    rintro address ty ⟨entry, found, typed⟩
    exact Spec.data_lookup_extend extension found typed

/-- Existing function bodies keep their source typing under store extension.
New function bodies are certified independently when they are published. -/
theorem FunctionsTyped.extend_old {s t : store} (functions : FunctionsTyped s)
    (extension : Extend_store s t) (fn : funcinst) (member : fn ∈ s.FUNCS) :
    match fn.CODE with
    | .HOST _ => Functype_ok fn.TYPE
    | .FUNC index locals body => ∃ C, ModuleBindings t fn.MODULE C ∧
        C.LOCALS = [] ∧ C.LABELS = [] ∧ C.RETURN = none ∧
        Func_ok C (.FUNC index locals body) fn.TYPE := by
  have typed := functions fn member
  cases code : fn.CODE with
  | HOST identity => simpa only [code] using typed
  | FUNC index locals body =>
    simp only [code] at typed ⊢
    obtain ⟨C, bindings, locals, labels, returns, body⟩ := typed
    exact ⟨C, bindings.extend extension, locals, labels, returns, body⟩

/-- A store update that adds no functions preserves all function typing. -/
theorem FunctionsTyped.extend_same {s t : store} (functions : FunctionsTyped s)
    (extension : Extend_store s t) (same : t.FUNCS = s.FUNCS) : FunctionsTyped t := by
  intro fn member
  exact functions.extend_old extension fn (same ▸ member)
end Itasca.Runtime.Abs
