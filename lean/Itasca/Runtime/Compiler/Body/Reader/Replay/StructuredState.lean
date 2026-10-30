import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefix
import Itasca.Runtime.Compiler.Body.Reader.Control.Boundary
import Itasca.Runtime.Compiler.Body.Reader.Control.ScopeFronts
import Itasca.Runtime.Compiler.Body.Reader.Control.ReachabilitySteps
import Itasca.Runtime.Compiler.Body.Reader.Control.KnownFronts

/-!
The shared state invariant for structured source/compiler replay.

Main declarations: `StructuredReaderCompilerStateWasm2`. A direct consumer is `Compiler.Body.Reader.Calls.Compilation`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

structure StructuredReaderCompilerStateWasm2 (jumpTables : List U32) (emit : List valtype → instr → List Bytecode → List valtype → Prop) {A : Type}
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (data : Slice U8) (env : metadata.Env) (sourceLocals : alloc.vec.Vec Itasca.wasm_types.ValueType)
    (index : U32) (ft : Itasca.wasm_types.FuncType) (st : code.BodyState)
    (parents : List SourceScope) (current : SourceScope)
    (savedParents : List Wasm2.Frames.Saved) (savedCurrent : Wasm2.Frames.Saved) : Prop where
  compiled : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial compiler types functions returns locals parents current st.core.vals.val st.core.pos.val
  boundary : ReaderBoundaryWasm2 data env sourceLocals index ft st savedParents savedCurrent
  sources : ReaderScopeZipperWasm2 parents current savedParents savedCurrent
  reach : ReaderReachabilityWasm2 compiler.reachable parents current savedParents savedCurrent
  fronts : ReaderScopeFronts parents current (savedParents.map Wasm2.Frames.Saved.vals)
  knownFronts : ReaderKnownFronts parents current (savedParents.map Wasm2.Frames.Saved.vals)

theorem StructuredReaderCompilerStateWasm2.advance {jumpTables : List U32} {A : Type}
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env sourceLocals index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWasm2 (jumpTables := jumpTables) emit initial before types functions returns locals data env sourceLocals index ft
      st parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    {out instruction poly values}
    (post : Wasm2.ReaderPost (state.boundary.pending next advance inbounds) out instruction poly values)
    (declared : DeclaredReferences.Instruction (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) instruction)
    (compiled : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance instruction)
      out.vals.val out.pos.val) (mono : after.reachable = true → poly = false) :
    StructuredReaderCompilerStateWasm2 (jumpTables := jumpTables) emit initial after types functions returns locals data env sourceLocals index ft {core := out}
      parents (current.advance instruction) savedParents
      (savedCurrent.advance (.plain instruction) instruction poly values) :=
  ⟨compiled, post.boundary declared, state.sources.advance _ _ _ _, state.reach.advance _ _ _ _ _ mono,
    state.fronts.advance instruction, state.knownFronts.advance instruction⟩

end Itasca.Runtime.Compiler
