import Exec.Code.Module.EntryDemand
import Exec.Code.Module.FunctionDemandEnvelope

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Independently prepared, encoded, and typed source entries in byte/index
order, with conservative source maxima. Preparation contains only source
metadata and decoding facts, never a compiler callback or target certificate. -/
inductive PreparedBatchSource (data : Slice U8) (env : module.Env) (profile : ValidationProfile)
    (bodyBytes localCount peak : Nat) : Nat → Usize → List ModuleBinary.Code → Usize → Prop where
  | nil (index start) : PreparedBatchSource data env profile bodyBytes localCount peak index start [] start
  | cons {index start next finish entry entries}
      (ordinal : Usize) (ordinalValue : ordinal.val = index)
      (indexBound : ordinal.val < env.func_type_indices.val.length)
      (typed : Profile.EntryTyped profile env env.func_type_indices.val[ordinal.val] entry)
      (encoded : ModuleBinary.At (Profile.CodeEncodingWithinLimits profile) data start entry next)
      (prepared : CodeEntry.Prepared data env ordinal start profile) (ending : prepared.finish = next)
      (bytes : prepared.body.length ≤ bodyBytes) (locals : prepared.ctx.locals.val.length ≤ localCount)
      (operands : (independentBodyDemand prepared.body env prepared.ctx prepared.typeIdx).operands ≤ peak)
      (rest : PreparedBatchSource data env profile bodyBytes localCount peak (index+1) next entries finish) :
      PreparedBatchSource data env profile bodyBytes localCount peak index start (entry::entries) finish

end Exec.Code
