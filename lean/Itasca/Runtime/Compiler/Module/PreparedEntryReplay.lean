import Itasca.Module.Code.ReachedEntry
import Itasca.Module.Code.LocalsComplete

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- Exact prepared source bytes replay the actual entry parser around its two
visitor-bearing calls. This requires only those reached calls, rather than a
visitor that accepts arbitrary contexts or instruction traces. -/
theorem prepared_entry_replay {V : Type} (visitor : code.OpVisitor V)
    {data env index start profile} (w : CodeEntry.Prepared data env index start profile)
    (before started after : V)
    (begun : visitor.on_function_start before w.ctx w.typeIdx w.bodyStart w.finish = .ok (.Ok (),started))
    (body : code.validate_body_with visitor w.body env w.ctx w.typeIdx profile started = .ok (.Ok (),after)) :
    module.validate_code_entry_with visitor data start env index profile before
      ⦃ result => result = (.Ok w.finish,after) ⦄ := by
  have read := reader.read_u32_leb.complete data start w.size w.content w.header
  obtain ⟨declared,decoded,declaredValues⟩ := module.decode_locals.complete data w.content profile w.groups w.bodyStart
    w.locals_bytes w.locals_allowed w.locals_bound
  have indexBound : ¬ index ≥ alloc.vec.Vec.len env.func_type_indices := by
    have bound := w.index_lt
    scalar_tac
  unfold module.validate_code_entry_with
  simp [indexBound,read,core.result.Result.Insts.CoreOpsTry.branch]
  step
  obtain ⟨reply,haveBytes,haveBytesPost⟩ := WP.spec_imp_exists
    (module.have_bytes.spec data w.content n (by have bound := w.header.span; omega))
  have enough : reply = .Ok () := haveBytesPost.1.mpr (by have bound := w.body_bytes.bound; have extent := w.extent; scalar_tac)
  rw [enough] at haveBytes
  simp [haveBytes]
  step
  have endEq : «end» = w.finish := UScalar.eq_of_val_eq (by have extent := w.extent; scalar_tac)
  simp [decoded]
  have span := w.body_bytes.length
  have bodyStartBound : ¬ «end».val < w.bodyStart.val := by rw [endEq]; omega
  simp only [bodyStartBound,↓reduceIte]
  step
  have typeEq : type_idx = w.typeIdx := by simpa only [w.index_type] using type_idx_post
  step
  have typeBound : ¬ env.types.val.length ≤ t.val := by have bound := w.type_lt; rw [← typeEq] at bound; scalar_tac
  simp only [typeBound,↓reduceIte]
  step
  have functionEq : ft = w.ft := by
    simpa [t_post,typeEq,w.function_type] using ft_post
  have localRoom : ft.params.val.length+declared.val.length ≤ Usize.max := by
    rw [functionEq,declaredValues]
    have length := congrArg List.length w.context_locals
    simp only [List.length_append] at length
    have bound := w.ctx.locals.property
    omega
  obtain ⟨locals,build,localValues⟩ := WP.spec_imp_exists
    (module.build_func_locals.spec ft.params.deref declared.deref (by simpa [alloc.vec.Vec.deref] using localRoom))
  obtain ⟨results,copy,resultValues⟩ := WP.spec_imp_exists (module.copy_value_types.spec ft.results.deref)
  rw [build,copy]
  simp only [bind_ok]
  have localsEq : locals = w.ctx.locals := alloc.vec.Vec.ext _ _ (by
    simpa [alloc.vec.Vec.deref,functionEq,declaredValues,w.context_locals] using localValues)
  have resultsEq : results = w.ctx.results := alloc.vec.Vec.ext _ _ (by
    simpa [alloc.vec.Vec.deref,functionEq,w.context_results] using resultValues)
  have contextEq : (⟨locals,results⟩ : code.Context) = w.ctx := by rw [localsEq,resultsEq]
  rw [contextEq,typeEq,endEq,begun]
  simp only [bind_ok]
  step as ⟨actual,actualSpec⟩
  have bytes := ModuleBinary.slice_bytes (by have length := w.body_bytes.length; scalar_tac)
    w.body_bytes.bound actualSpec
  have bodyEq : actual = w.body := Slice.ext _ _ (by
    exact List.append_cancel_right (bytes.suffix.symm.trans w.body_bytes.suffix))
  rw [bodyEq,body]
  simp

end Itasca.Runtime.Compiler
