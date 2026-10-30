import Itasca.Runtime.Compiler.Body.Reader.Replay.Post

/-!
The pending reader boundary between source scopes and compiler state.

Main declarations: `ReaderBoundaryWasm2` and `ReaderBoundaryWasm2.pending`. A direct consumer is `Compiler.Body.Reader.Control.BoundaryInitial`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

structure ReaderBoundaryWasm2 (data : Slice U8) (env : metadata.Env)
    (locals : alloc.vec.Vec wasm_types.ValueType) (index : U32) (ft : wasm_types.FuncType)
    (st : code.BodyState) (parents : List Wasm2.Frames.Saved) (current : Wasm2.Frames.Saved) : Prop where
  signature : env.types.val[index.val]? = some ft
  bounds : Wasm2.Bounds data st
  opened : Wasm2.Frames.Open env (Wasm2.bodyContext env locals ft) st parents current
  bodyType : Wasm2.Frames.bodyType parents current = some (.TypeIndex index)
  consumed : Wasm2.Consumed data 0#usize (Wasm2.Frames.trace parents current) st.core.pos
  declared : Wasm2.TokensDeclared (env.declared_funcs.val.map (fun i => uN.mk_uN i.val))
    (Wasm2.Frames.trace parents current)

def ReaderBoundaryWasm2.pending {data env locals index ft st parents current}
    (boundary : ReaderBoundaryWasm2 data env locals index ft st parents current)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length) :
    Wasm2.Pending data env .Wasm2 locals index {core := {st.core with pos := next}} :=
  ⟨st.core.pos, ft, parents, current, boundary.signature, boundary.bounds.size, boundary.opened.with_pos next,
    boundary.bodyType, boundary.consumed, boundary.declared, inbounds, advance, boundary.bounds.ctrls,
    (fun h => nomatch h), (fun h => nomatch h), (fun h => nomatch h)⟩

theorem _root_.Itasca.Wasm2.ReaderPost.boundary {data env locals index st out instruction poly values}
    {p : Wasm2.Pending data env .Wasm2 locals index st}
    (post : Wasm2.ReaderPost p out instruction poly values)
    (declared : DeclaredReferences.Instruction (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) instruction) :
    ReaderBoundaryWasm2 data env locals index p.ft {core := out} p.parents
      (p.current.advance (.plain instruction) instruction poly values) := by
  refine ⟨p.signature, post.after.1.bounds, post.opened, ?_, ?_, ?_⟩
  · simpa only [Wasm2.Frames.bodyType_advance] using p.bodyType
  · have consumed := Wasm2.Consumed.snoc p.consumed post.encoded
    simpa [Wasm2.Frames.trace, Wasm2.Frames.Saved.trace, Wasm2.Frames.Saved.advance, List.append_assoc] using consumed
  · have trace : Wasm2.Frames.trace p.parents (p.current.advance (.plain instruction) instruction poly values) =
        Wasm2.Frames.trace p.parents p.current ++ [.plain instruction] := by
      simp [Wasm2.Frames.trace, Wasm2.Frames.Saved.trace, Wasm2.Frames.Saved.advance, List.append_assoc]
    rw [trace, Wasm2.tokensDeclared_append, Wasm2.tokensDeclared_singleton]
    exact ⟨p.declared, declared⟩

end Itasca.Runtime.Compiler
