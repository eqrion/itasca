import Exec.Code.Body.Reader.Common.ReaderSaturating
import Exec.Code.Local.Lowering.Float.FloatEffects
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

theorem reader_saturating_capacity_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (index : U32) (op : Abs.Float.Instruction) (extension : 256 ≤ (floatOpcode op).val)
    (subopcode : U32) (next : Usize)
    (subopcodeEq : subopcode.val = (floatOpcode op).val - 256)
    (decoded : Leb128.Decoded data st.core.pos subopcode next)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 0xfc#u8 before = .ok (.Ok (),out,after)) :
    CapacityStep before after out.core := by
  obtain ⟨sub,operation,hook,subEq,bound,meaning,instruction,inputs,output,encoding,hookEq⟩ :=
    float_saturating_reader_facts ops before out.core op extension
  have same : sub = subopcode := (UScalar.eq_equiv _ _).mpr (subEq.trans subopcodeEq.symm)
  subst sub
  obtain ⟨_,run⟩ := profile_scalar_success
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx index 0xfc#u8 before after (by decide) accepted
  rw [code.step_wasm2.saturating _ _ _ _ _ _ _ _ decoded bound,code.step_extended.prefixed] at run
  have readLeb := reader.read_u32_leb.complete data st.core.pos subopcode next decoded
  simp only [Wasm2.prefixedStep,readLeb,bind_ok,meaning] at run
  obtain ⟨value,_,callback⟩ := reader_run_success _ _ _ _ _ run
  have dispatch := ExtendedNumericHook.dispatch (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before out.core hook
  rw [encoding] at dispatch
  dsimp only at dispatch
  rw [dispatch,hookEq] at callback
  exact compiler_float_capacity ops law before after out.core op callback
end Exec.Code
