import Exec.Code.Local.Control.Simd.StructuredSimdEmbedding
import Exec.Code.Body.Reader.Simd.ReaderSimdEmissions
import Exec.Code.Body.Callbacks.Common.CompilerPrefix
import Exec.Code.Local.Control.Common.Structured
import Exec.Code.Local.Control.Common.StructuredComposition
import Exec.Code.Local.Relations.Common.Concatenation
import Exec.Code.Local.Relations.Common.Extension
import Exec.Code.Local.Relations.Common.PrefixZipper
import Exec.Code.Local.Relations.Common.Prefix
import Exec.Code.Local.Relations.Common.ResolvedPrefix
import Exec.Code.Local.Control.Common.UniversalPrefix
import Exec.Code.Local.Control.Common.UniversalTerminal
import Exec.Code.Local.Control.Common.UniversalDormant
import Exec.Code.Local.Callbacks.Common.CompilerDeadMetadata
import Exec.Code.Body.Reader.Common.ReaderSpan
import Exec.Code.Local.Callbacks.Table.CompilerTablePreservation
import Exec.Code.Body.Reader.Simd.ReaderSimdCallbackEmission
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- All information retained from one actually accepted SIMD reader and
callback. The source meaning is supplied by the independent opcode tables. -/
structure SimdReaderEvent {A : Type} (ops : runtime.platform.Alloc A)
    {data env locals index st} (p : Wasm2.Pending data env .Wasm2 locals index st)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState) (C : context) where
  source : instr
  inputs : List types.ValueType
  output : Option types.ValueType
  sub : U32
  a : U32
  b : U32
  bits : U128
  opcode : U16
  number : opcode.val = 512 + sub.val
  meaning : SimdCallbackMeaning C sub a bits inputs source output
  values : List code.StackType
  position : Usize
  post : ReaderPostWasm2 p out source p.current.ctrl.polymorphic_base values
  effect : Wasm2.Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals inputs output values
  read : Wasm2.Simd.readFixed {st.core with pos := position} inputs output = .ok (.Ok (),out)
  callback : runtime.compiler.lower.FunctionCompiler.op ops before out opcode a b bits = .ok (.Ok (),after)
  capacity : st.core.vals.val.length < Usize.max

theorem SimdReaderEvent.capacity_step {A : Type} {ops : runtime.platform.Alloc A}
    {data env locals index st p before after out C}
    (event : @SimdReaderEvent A ops data env locals index st p before after out C)
    (law : Platform.AllocCorrect ops) : CapacityStep before after out := by
  have bound := event.meaning.opcode_bound
  exact (compiler_lower_simd_effects ops law before after out event.opcode event.a event.b event.bits
    (by have number := event.number; omega) (by have number := event.number; omega) event.callback).2.2.2

end Exec.Code
