import Itasca.Runtime.Representation.Layout
namespace Itasca.Runtime.Theorems
open SpecExt
/-- Public buffer storage is computed from decoded parameter/result types. -/
def signatureWords : functype → Nat
  | .mk_functype (.mk_list params) (.mk_list results) => max (Code.slots params) (Code.slots results)

end Itasca.Runtime.Theorems
