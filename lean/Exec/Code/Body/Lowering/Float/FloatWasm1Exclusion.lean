import Exec.Code.Body.Reader.Common.ReaderProfile
import Exec.Code.Body.Reader.Integer.ReaderInteger
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem float_saturating_wasm1_impossible {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (st out : code.OpIterState) (data : Slice U8)
    (env : module.Env) (ctx : code.Context)
    (accepted : code.step visitor st data env ctx 252#u8 before = .ok (.Ok (),out,after)) : False := by
  rw [code.step.numeric_dispatch visitor st data env ctx 252#u8 before (by decide),
    code.step_numeric.unrecognized visitor st 252#u8 before rfl] at accepted
  simp at accepted
end Exec.Code
