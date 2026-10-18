import Exec.Code.Body.Control.Common.StructuredCompilerPrefix
import Exec.Code.Body.Reader.Common.ReaderBoundary
import Exec.Code.Body.Reader.Control.ReaderScopeFronts
import Exec.Code.Body.Reader.Common.ReaderReachabilitySteps
import Exec.Code.Body.Reader.Common.ReaderKnownFronts
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- The complete compiler fold state retains one particular canonical source
zipper, together with its emitted-code invariant and exact saved stack fronts.
Static signature/local-layout facts remain parameters of the body fold. -/
structure StructuredReaderCompilerStateWasm1 (emit : List valtype → instr → List Bytecode → List valtype → Prop) {A : Type}
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (bodyBt : code.BlockType)
    (st : code.OpIterState) (parents : List SourceScope) (current : SourceScope)
    (savedParents : List Wasm1.Frames.Saved) (savedCurrent : Wasm1.Frames.Saved) : Prop where
  compiled : StructuredCompilerPrefix emit initial compiler types functions returns locals parents current st.vals.val st.pos.val
  boundary : ReaderBoundaryWasm1 data env ctx bodyBt st savedParents savedCurrent
  sources : ReaderScopeZipperWasm1 parents current savedParents savedCurrent
  reach : ReaderReachabilityWasm1 compiler.reachable parents current savedParents savedCurrent
  fronts : ReaderScopeFronts parents current (savedParents.map Wasm1.Frames.Saved.vals)
  knownFronts : ReaderKnownFronts parents current (savedParents.map Wasm1.Frames.Saved.vals)

structure StructuredReaderCompilerStateWasm2 (emit : List valtype → instr → List Bytecode → List valtype → Prop) {A : Type}
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (data : Slice U8) (env : module.Env) (sourceLocals : alloc.vec.Vec Itasca.types.ValueType)
    (index : U32) (ft : Itasca.types.FuncType) (st : code.BodyState)
    (parents : List SourceScope) (current : SourceScope)
    (savedParents : List Wasm2.Frames.Saved) (savedCurrent : Wasm2.Frames.Saved) : Prop where
  compiled : StructuredCompilerPrefix emit initial compiler types functions returns locals parents current st.core.vals.val st.core.pos.val
  boundary : ReaderBoundaryWasm2 data env sourceLocals index ft st savedParents savedCurrent
  sources : ReaderScopeZipperWasm2 parents current savedParents savedCurrent
  reach : ReaderReachabilityWasm2 compiler.reachable parents current savedParents savedCurrent
  fronts : ReaderScopeFronts parents current (savedParents.map Wasm2.Frames.Saved.vals)
  knownFronts : ReaderKnownFronts parents current (savedParents.map Wasm2.Frames.Saved.vals)

/-- Ordinary readers extend exactly the retained zipper, rather than selecting
an unrelated witness from a general validator-state theorem. -/
theorem StructuredReaderCompilerStateWasm1.advance {A : Type}
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx bodyBt st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWasm1 emit initial before types functions returns locals data env ctx bodyBt
      st parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    {out instruction poly values}
    (post : ReaderPostWasm1 (state.boundary.pending next advance inbounds) out instruction poly values)
    (compiled : StructuredCompilerPrefix emit initial after types functions returns locals parents (current.advance instruction)
      out.vals.val out.pos.val) (mono : after.reachable = true → poly = false) :
    StructuredReaderCompilerStateWasm1 emit initial after types functions returns locals data env ctx bodyBt out
      parents (current.advance instruction) savedParents
      (savedCurrent.advance (.plain instruction) instruction poly values) :=
  ⟨compiled, post.boundary, state.sources.advance _ _ _ _, state.reach.advance _ _ _ _ _ mono,
    state.fronts.advance instruction, state.knownFronts.advance instruction⟩

theorem StructuredReaderCompilerStateWasm2.advance {A : Type}
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env sourceLocals index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWasm2 emit initial before types functions returns locals data env sourceLocals index ft
      st parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    {out instruction poly values}
    (post : ReaderPostWasm2 (state.boundary.pending next advance inbounds) out instruction poly values)
    (declared : DeclaredReferences.Instruction (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) instruction)
    (compiled : StructuredCompilerPrefix emit initial after types functions returns locals parents (current.advance instruction)
      out.vals.val out.pos.val) (mono : after.reachable = true → poly = false) :
    StructuredReaderCompilerStateWasm2 emit initial after types functions returns locals data env sourceLocals index ft {core := out}
      parents (current.advance instruction) savedParents
      (savedCurrent.advance (.plain instruction) instruction poly values) :=
  ⟨compiled, post.boundary declared, state.sources.advance _ _ _ _, state.reach.advance _ _ _ _ _ mono,
    state.fronts.advance instruction, state.knownFronts.advance instruction⟩

end Exec.Code
