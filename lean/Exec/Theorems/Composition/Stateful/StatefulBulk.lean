import Exec.Store.Initialization.BulkMemory
import Exec.Abs.Stateful.Transition
import Exec.Interp.Relations.FrameStoreMetadata
namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store Itasca.Runtime.Interp

def statefulBulkResult {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (front : List val)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M) : Abs.AResult :=
  match out.1 with
  | .Ok _ => Abs.advance {state with store := decodeStore view code out.2} {f with code := after,vals := front} rest
  | .Err _ => .trap

theorem bulk_integer_decoded (word : U64) :
    Abs.integer .I32 (Abs.integerVal .I32 (bulkWord word).val) = some (bulkWord word).val :=
  Abs.integer_accepts .I32 _ (by change (bulkWord word).val < 2^32; simp only [bulkWord,U32.cast_U64_val_eq]; scalar_tac)
end Itasca.Runtime.Theorems
