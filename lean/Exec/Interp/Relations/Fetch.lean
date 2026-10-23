import Exec.Interp.Relations.Execute

/-! Fetching an instruction in the extracted interpreter. The compiler/frame
relation supplies address and program-counter bounds; the selected handler
supplies its own postcondition. This bridge checks all intervening indexing and
the exact program-counter update. -/
namespace Exec.Interp
open Aeneas Aeneas.Std

@[step] theorem vec_index_given {T : Type} (values : alloc.vec.Vec T)
    (index : Usize) (value : T) (h : values.val[index.val]? = some value) :
    alloc.vec.Vec.index_usize values index
      ⦃ out => out = value ⦄ := by
  have hi : index.val < values.length := List.getElem?_eq_some_iff.mp h |>.1
  step as ⟨out, hout⟩
  have he := List.getElem?_eq_getElem hi
  rw [h] at he
  exact hout.trans (Option.some.inj he).symm

theorem step_fetch {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (frame : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some frame)
    (hi : store.instances.val[frame.instance.val]? = some inst)
    (hc : inst.module.functions.val[frame.function.val]? = some code)
    (hop : code.code.val[frame.pc.val]? = some instruction)
    (pcBound : frame.pc.val < U32.max)
    (post : core.result.Result Unit runtime.ExecError × runtime.interp.Execution ×
      runtime.store.Store M × P → Prop)
    (handler : ∀ next : U32, next.val = frame.pc.val + 1 →
      runtime.interp.dispatch memory hooks floats allocator
        { exec with frames := exec.frames.set index { frame with pc := next } }
        store platform index frame.instance frame.function frame.base instruction ⦃ post ⦄) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ post ⦄ := by
  unfold runtime.interp.step
  step as ⟨actualIndex, hindex⟩
  have he : actualIndex = index := by scalar_tac
  subst actualIndex
  step with vec_index_given exec.frames index frame hf as ⟨found, hfound⟩
  subst found
  step with vec_index_given store.instances frame.instance inst hi as ⟨found, hfound⟩
  subst found
  step with vec_index_given inst.module.functions frame.function code hc as ⟨found, hfound⟩
  subst found
  simp only [lift, bind_ok]
  step with vec_index_given code.code (UScalar.cast .Usize frame.pc) instruction
    (by simpa only [U32.cast_Usize_val_eq] using hop) as ⟨found, hfound⟩
  subst found
  have hchecked := U32.checked_add_bv_spec frame.pc 1#u32
  cases hnext : U32.checked_add frame.pc 1#u32 with
  | none =>
    simp only [hnext] at hchecked
    scalar_tac
  | some next =>
    simp only [hnext] at hchecked ⊢
    step as ⟨old, back, hold, hback⟩
    have hframe : old = frame := by
      have he := List.getElem?_eq_getElem (show index.val < exec.frames.length by omega)
      rw [hf] at he
      exact hold.trans (Option.some.inj he).symm
    have hb : index.val < exec.frames.val.length := by
      change index.val < exec.frames.length
      omega
    have hread : exec.frames.val[index.val]'hb = frame := hold.symm.trans hframe
    simpa only [hback, hframe, hread] using handler next hchecked.2.1

end Exec.Interp
