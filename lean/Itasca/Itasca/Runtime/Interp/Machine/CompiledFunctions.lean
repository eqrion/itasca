import Itasca.Runtime.Interp.Recording
import Itasca.Runtime.Interp.Machine.Frames.FrameAndReturnStacks
import Itasca.Runtime.Interp.Machine.Frames.Reposition
import Itasca.Runtime.SourceMachine.Core.OperationsAndMemoryTyping
import Itasca.Runtime.SourceMachine.EntryAndBranchTables
import Itasca.Runtime.Interp.Relations.ReadbackAndBindings
import Itasca.Runtime.Compiler.Local.Relations.Function.CapturedContext
import Itasca.Runtime.SourceMachine.Typing
import Itasca.Runtime.Interp.Machine.SuspendedPoint
import Itasca.Runtime.Compiler.Local.Control.Structured.NestedScopes

open WebAssembly

/-!
Proofs for Runtime / Interp / Machine.

This module collects Execution, CompiledFunctions.
Each section documents its contracts and consumers.
-/

/-! ## Execution -/

section

/-!
The structured machine execution relation and its control cursor.

Main declarations: `Execution` and `ExecutionCursor`.
-/

namespace Itasca.Interp.Machine
open Aeneas Aeneas.Std

theorem FrameStackRel.top {M : Type} {store : runtime.store.Store M} {sourceStore : WebAssembly.store}
    {exec : runtime.interp.Execution} {source : SourceMachine.AFrame} {rest : List SourceMachine.AFrame}
    (relation : FrameStackRel store sourceStore exec (source :: rest))
    (raw : runtime.interp.Frame) (top : exec.frames.val.getLast? = some raw) :
    ActiveFrame store sourceStore exec raw source := by
  cases relation with
  | active frames active saved =>
    have same := top
    simp only [frames,List.getLast?_concat,Option.some.injEq] at same
    subst raw
    exact active

theorem ControlTop.pc {M : Type} {store : runtime.store.Store M} {sourceStore : WebAssembly.store}
    {exec : runtime.interp.Execution} {source : SourceMachine.AFrame} {pc : Nat} {pending : Bool}
    (cursor : ControlTop store sourceStore exec source pc pending) :
    (exec.frames.val.getLast?).map (fun raw => raw.pc.val) = some pc := by
  obtain ⟨raw,compiled,C,targets,next,output,top,same,program,point⟩ := cursor
  simp only [top,Option.map_some,same]

theorem ControlTop.updated {M : Type} {store : runtime.store.Store M} {sourceStore : WebAssembly.store}
    {exec : runtime.interp.Execution} {raw : runtime.interp.Frame}
    {compiled : runtime.bytecode.CompiledFunction} {C : context}
    {before after : SourceMachine.AFrame} {pc : U32} {pending : Bool}
    (top : exec.frames.val.getLast? = some {raw with pc := pc})
    (program : FrameProgram store raw compiled (before.locals.map Representation.valueType) before.resultTypes C.FUNCS)
    (metadata : FrameMetadata before after)
    (point : ∃ targets next output, ControlPoint sourceStore {raw with pc := pc} after compiled C targets next output pending) :
    ControlTop store sourceStore exec after pc.val pending := by
  obtain ⟨targets,next,output,point⟩ := point
  exact ⟨{raw with pc := pc},compiled,C,targets,next,output,top,rfl,program.reposition pc metadata,point⟩

theorem ReadyTop.cursor {M : Type} {store : runtime.store.Store M} {sourceStore : WebAssembly.store}
    {exec : runtime.interp.Execution} {source : SourceMachine.AFrame}
    (ready : ReadyTop store sourceStore exec source) : ∃ pc, ControlTop store sourceStore exec source pc false := by
  obtain ⟨raw,compiled,C,targets,next,output,top,program,point⟩ := ready
  exact ⟨raw.pc.val,raw,compiled,C,targets,next,output,top,rfl,program,.ready point⟩

theorem ReadyState.cursor {M : Type} {store : runtime.store.Store M}
    {exec : runtime.interp.Execution} {source : SourceMachine.AState}
    (ready : ReadyState store exec source) : ∃ pc, ExecutionCursor store exec source pc false := by
  cases frames : source.frames with
  | nil => exact ⟨0,by simpa only [ExecutionCursor,ReadyState,frames,true_and] using ready⟩
  | cons frame rest =>
    simp only [ReadyState,frames] at ready
    obtain ⟨pc,cursor⟩ := ready.cursor
    exact ⟨pc,by simpa only [ExecutionCursor,frames] using cursor⟩
end Itasca.Interp.Machine

end

/-! ## CompiledFunctions -/

section

open Itasca.Representation

/-! ## Typing -/

section

/-!
The completed module context has no ambient function-local declarations.

Main declarations: `moduleSourceContext` and `CoreFunctionTyped`.
-/

namespace Itasca.Interp
open Aeneas Aeneas.Std

theorem CoreFunctionsTyped.functions_typed {M : Type} {view : M → Slice U8}
    {code : Representation.CodeInterpretation} {store : runtime.store.Store M}
    (typed : CoreFunctionsTyped view code store) :
    SourceMachine.FunctionsTyped (Representation.decodeStore view code store) := by
  intro fn member
  obtain ⟨function, present, rfl⟩ := List.mem_map.mp member
  have body := typed function present
  cases kind : function.code with
  | Host id => simpa only [CoreFunctionTyped, kind, Representation.decodeFunction] using body
  | Wasm ii fi =>
    simp only [CoreFunctionTyped, kind] at body
    obtain ⟨inst, index, locals, instructions, found, source, bindings, body⟩ := body
    simp only [Representation.decodeFunction, kind, found, source] at body ⊢
    exact ⟨Compiler.moduleSourceContext inst.module, bindings, rfl, rfl, rfl, body⟩
end Itasca.Interp

end

/-! ## FunctionCode -/

section

/-!
Function-local emission metadata and complete syntactic compiler evidence.

Main declarations: `FunctionCode`.
-/

namespace Itasca.Interp.Machine
open Aeneas.Std

theorem FunctionCode.entry {C params declared results body compiled epilogue}
    (certificate : FunctionCode C params declared results body compiled epilogue) :
    Compiler.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS results C.LOCALS compiled.code.val compiled.jump_tables.val
      [Compiler.functionRootLabel results compiled epilogue] [] body 0 epilogue.val results := by
  simpa only [certificate.1] using certificate.2.entry
end Itasca.Interp.Machine

end

/-! ## CompiledFunctions -/

section

/-!
Concrete function lookup retains the canonical source context for mutable instructions. This is source syntax and layout evidence, independent of any claim about execution or mutable store contents.

Main declarations: `FunctionCompiled` and `CompiledFunctions`.
-/

namespace Itasca.Interp.Machine
open Aeneas Aeneas.Std

theorem declared_types_not_bottom {C params declared results body compiled epilogue}
    (certificate : FunctionCode C params declared results body compiled epilogue) :
    Forall (fun ty => ty ≠ valtype.BOT) declared := by
  intro ty member
  have present : ty ∈ params ++ declared := List.mem_append_right _ member
  rw [← certificate.2.locals] at present
  obtain ⟨rawType, _, rfl⟩ := List.mem_map.mp present
  cases rawType <;> decide
end Itasca.Interp.Machine

end

end
