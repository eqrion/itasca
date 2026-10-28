import Itasca.Runtime.Representation.Store
import Itasca.Binary.Unicode

/-! Store names use the same independent Unicode decoding as the source grammar. -/
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std Itasca

theorem decodeNameChars_source (bytes : List U8) :
    decodeNameChars bytes = ModuleBinary.decodeChars bytes := by
  induction bytes using decodeNameChars.induct <;>
    (try simp only [decodeNameChars, ModuleBinary.decodeChars]) <;>
    (try simp_all only [ite_false])
  all_goals
    unfold decodeNameChars ModuleBinary.decodeChars
    simp_all only [ite_true, ite_false]

theorem decodeName_source (bytes : List U8) :
    decodeName bytes = ModuleBinary.nameOfBytes bytes := by
  simp only [decodeName, ModuleBinary.nameOfBytes, decodeNameChars_source]

end Itasca.Runtime.Store
