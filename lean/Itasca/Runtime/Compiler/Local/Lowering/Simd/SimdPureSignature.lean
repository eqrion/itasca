import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdSourceShape
import Itasca.Runtime.SourceMachine.Simd.Signature
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.Wasm2.Simd
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

def simdPureOutput (signature : Signature) : valtype :=
  match signature with | .test => .I32 | _ => .V128

private def PureSignatureCorrect (opcode : U32) : Prop :=
  match pureMeaning opcode.val with
  | none => True
  | some op => Abs.Simd.PureSignature op.instruction op.signature.inputs (simdPureOutput op.signature)

private theorem pure_signature_table (opcode : U32) (bounded : opcode.val < 256) :
    PureSignatureCorrect opcode := by
  rcases opcode with ⟨⟨n,hn⟩⟩
  change n < 256 at bounded
  interval_cases n <;> with_unfolding_all (first | exact True.intro | constructor)

theorem pure_source_signature {opcode : U32} {op : Operation}
    (meaning : pureMeaning opcode.val = some op) :
    Abs.Simd.PureSignature op.instruction op.signature.inputs (simdPureOutput op.signature) := by
  have table := pure_signature_table opcode (pure_bound meaning)
  unfold PureSignatureCorrect at table
  simpa only [meaning] using table

end Itasca.Runtime.Code
