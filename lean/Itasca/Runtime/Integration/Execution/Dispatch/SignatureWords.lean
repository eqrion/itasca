import Itasca.Runtime.Representation.Layout
namespace Itasca.Runtime.Integration
open SpecExt
/-- Public buffer storage is computed from decoded parameter/result types. -/
def signatureWords : functype → Nat
  | .mk_functype (.mk_list params) (.mk_list results) => max (Compiler.slots params) (Compiler.slots results)

end Itasca.Runtime.Integration
