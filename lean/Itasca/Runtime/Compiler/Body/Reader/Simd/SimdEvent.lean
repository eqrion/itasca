import Itasca.Runtime.Compiler.Local.Control.Simd.StructuredSimdEmbedding
import Itasca.Runtime.Compiler.Body.Reader.Simd.SimdEmissions
import Itasca.Runtime.Compiler.Body.Callbacks.Prefix.CompilerPrefix
import Itasca.Runtime.Compiler.Local.Control.Segments.Structured
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredComposition
import Itasca.Runtime.Compiler.Local.Relations.Prefix.Concatenation
import Itasca.Runtime.Compiler.Local.Relations.Prefix.Extension
import Itasca.Runtime.Compiler.Local.Relations.Prefix.PrefixZipper
import Itasca.Runtime.Compiler.Local.Relations.Prefix.Prefix
import Itasca.Runtime.Compiler.Local.Relations.Prefix.ResolvedPrefix
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalPrefix
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalTerminal
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalDormant
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerDeadMetadata
import Itasca.Runtime.Compiler.Body.Reader.Replay.Span
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerTablePreservation
import Itasca.Runtime.Compiler.Body.Reader.Simd.CallbackEmission

/-!
All information retained from one actually accepted SIMD reader and callback. The source meaning is supplied by the independent opcode tables.

Main declarations: `SimdReaderEvent`. A direct consumer is `Compiler.Body.Reader.Simd.Dispatch`.
-/

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler
