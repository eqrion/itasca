import SpecExt.Builtins
import Lean.Elab.Command

/-! Coverage inventory of every pinned builtin signature. Classification records
intended source domains and semantic alternatives separately from signature
agreement. This is a review inventory, not a global reduction-determinism proof.
The audit also compares its symbols with generated Wasm2Builtins. -/
namespace SpecExt.Builtins.Review

inductive Family where
  | structural | typeIndex | integerConversion | integerCount | bitwise | shift | rotate
  | average | q15 | storage | lanes | floatSign | floatCompare | pseudoMinMax
  | floatArithmetic | floatIntegral | integerToFloat | floatFormat | floatToInteger
  deriving DecidableEq

inductive Alternatives where
  | deterministic | nanAlternatives | unused
  deriving DecidableEq

inductive Domain where
  | structural | rational | nonnegativeIndex | integerWidths | unsignedAverage | signedQ15
  | storageWidths | vectorShape | floatWidths | conversionWidths
  deriving DecidableEq

structure BuiltinReview where
  symbol : Lean.Name
  family : Family
  alternatives : Alternatives
  domain : Domain

/-- Each symbol is resolved by Lean; generated-signature coverage is checked
independently by the audit script. Domain premises remain necessary. -/
def inventory : List BuiltinReview :=
  [
    ⟨``inv_concat_,.structural,.unused,.structural⟩,
    ⟨``s33_to_u32,.typeIndex,.deterministic,.nonnegativeIndex⟩,
    ⟨``truncz,.integerConversion,.deterministic,.rational⟩,
    ⟨``extend__,.integerConversion,.deterministic,.integerWidths⟩,
    ⟨``fabs_,.floatSign,.deterministic,.floatWidths⟩,
    ⟨``fceil_,.floatIntegral,.nanAlternatives,.floatWidths⟩,
    ⟨``ffloor_,.floatIntegral,.nanAlternatives,.floatWidths⟩,
    ⟨``fnearest_,.floatIntegral,.nanAlternatives,.floatWidths⟩,
    ⟨``fneg_,.floatSign,.deterministic,.floatWidths⟩,
    ⟨``fsqrt_,.floatArithmetic,.nanAlternatives,.floatWidths⟩,
    ⟨``ftrunc_,.floatIntegral,.nanAlternatives,.floatWidths⟩,
    ⟨``iclz_,.integerCount,.deterministic,.integerWidths⟩,
    ⟨``ictz_,.integerCount,.deterministic,.integerWidths⟩,
    ⟨``ipopcnt_,.integerCount,.deterministic,.integerWidths⟩,
    ⟨``wrap__,.integerConversion,.deterministic,.integerWidths⟩,
    ⟨``fadd_,.floatArithmetic,.nanAlternatives,.floatWidths⟩,
    ⟨``fcopysign_,.floatSign,.deterministic,.floatWidths⟩,
    ⟨``fdiv_,.floatArithmetic,.nanAlternatives,.floatWidths⟩,
    ⟨``fmax_,.floatArithmetic,.nanAlternatives,.floatWidths⟩,
    ⟨``fmin_,.floatArithmetic,.nanAlternatives,.floatWidths⟩,
    ⟨``fmul_,.floatArithmetic,.nanAlternatives,.floatWidths⟩,
    ⟨``fsub_,.floatArithmetic,.nanAlternatives,.floatWidths⟩,
    ⟨``iand_,.bitwise,.deterministic,.integerWidths⟩,
    ⟨``ior_,.bitwise,.deterministic,.integerWidths⟩,
    ⟨``irotl_,.rotate,.deterministic,.integerWidths⟩,
    ⟨``irotr_,.rotate,.deterministic,.integerWidths⟩,
    ⟨``ishl_,.shift,.deterministic,.integerWidths⟩,
    ⟨``ishr_,.shift,.deterministic,.integerWidths⟩,
    ⟨``ixor_,.bitwise,.deterministic,.integerWidths⟩,
    ⟨``feq_,.floatCompare,.deterministic,.floatWidths⟩,
    ⟨``fge_,.floatCompare,.deterministic,.floatWidths⟩,
    ⟨``fgt_,.floatCompare,.deterministic,.floatWidths⟩,
    ⟨``fle_,.floatCompare,.deterministic,.floatWidths⟩,
    ⟨``flt_,.floatCompare,.deterministic,.floatWidths⟩,
    ⟨``fne_,.floatCompare,.deterministic,.floatWidths⟩,
    ⟨``convert__,.integerToFloat,.deterministic,.conversionWidths⟩,
    ⟨``demote__,.floatFormat,.nanAlternatives,.conversionWidths⟩,
    ⟨``promote__,.floatFormat,.nanAlternatives,.conversionWidths⟩,
    ⟨``reinterpret__,.storage,.deterministic,.storageWidths⟩,
    ⟨``trunc__,.floatToInteger,.deterministic,.conversionWidths⟩,
    ⟨``trunc_sat__,.floatToInteger,.deterministic,.conversionWidths⟩,
    ⟨``narrow__,.integerConversion,.deterministic,.integerWidths⟩,
    ⟨``ibits_,.storage,.deterministic,.storageWidths⟩,
    ⟨``fbits_,.storage,.deterministic,.storageWidths⟩,
    ⟨``ibytes_,.storage,.deterministic,.storageWidths⟩,
    ⟨``fbytes_,.storage,.deterministic,.storageWidths⟩,
    ⟨``nbytes_,.storage,.deterministic,.storageWidths⟩,
    ⟨``vbytes_,.storage,.deterministic,.storageWidths⟩,
    ⟨``inv_ibits_,.storage,.deterministic,.storageWidths⟩,
    ⟨``inv_fbits_,.storage,.deterministic,.storageWidths⟩,
    ⟨``inv_ibytes_,.storage,.deterministic,.storageWidths⟩,
    ⟨``inv_fbytes_,.storage,.deterministic,.storageWidths⟩,
    ⟨``inv_nbytes_,.storage,.deterministic,.storageWidths⟩,
    ⟨``inv_vbytes_,.storage,.deterministic,.storageWidths⟩,
    ⟨``inot_,.bitwise,.deterministic,.integerWidths⟩,
    ⟨``irev_,.bitwise,.deterministic,.integerWidths⟩,
    ⟨``iandnot_,.bitwise,.deterministic,.integerWidths⟩,
    ⟨``ibitselect_,.bitwise,.deterministic,.integerWidths⟩,
    ⟨``iavgr_,.average,.deterministic,.unsignedAverage⟩,
    ⟨``iq15mulr_sat_,.q15,.deterministic,.signedQ15⟩,
    ⟨``fpmin_,.pseudoMinMax,.deterministic,.floatWidths⟩,
    ⟨``fpmax_,.pseudoMinMax,.deterministic,.floatWidths⟩,
    ⟨``lanes_,.lanes,.deterministic,.vectorShape⟩,
    ⟨``inv_lanes_,.lanes,.deterministic,.vectorShape⟩
  ]

theorem inventory_count : inventory.length = 64 := by decide

theorem inventory_symbols_unique : (inventory.map BuiltinReview.symbol).Nodup := by decide

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for review in inventory do
    match env.find? review.symbol with
    | some (.defnInfo _) => pure ()
    | _ => throwError "Builtin inventory entry {review.symbol} is not a concrete definition"

end SpecExt.Builtins.Review
