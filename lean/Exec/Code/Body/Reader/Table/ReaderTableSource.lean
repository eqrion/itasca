import Exec.Code.Body.Reader.Table.ReaderTableWasm2
import Itasca.Binary.Wasm1.EncodingUnique
import Itasca.Visitor.TraceBytes
import Itasca.Visitor.Recording
import Itasca.Handler.BrTable
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Canonical independent immediate decoding determines every collected Wasm 2
target and the exact accepted final callback. -/
theorem compiler_table_source_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st final : code.BodyState) (data : Slice U8) (env : module.Env)
    (shape : Control.Shape st.core) (depths : List U32) (fallback : U32) (next : Usize)
    (encoded : BrTable.Decoded data st.core.pos depths fallback next)
    (accepted : code.branch_table_with (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env .Wasm2 before = .ok (.Ok (),final,after)) :
    ∃ budget buffer types,
      buffer.val = before.table_depths.val ++ depths ∧
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
        ops {before with budget,table_depths := buffer} final.core fallback types = .ok (.Ok (),after) := by
  obtain ⟨count,first,selector,popped,actual,default,types,last,readState,budget,buffer,
    countDecoded,popCall,bufferEq,labelsDecoded,defaultDecoded,lengthEq,marked,callback⟩ :=
    compiler_read_br_table ops law before after st final data env _ accepted
  have movedShape : Control.Shape {st.core with pos := first} := ⟨shape.ordered,shape.bounded⟩
  have poppedSpec := code.pop_with_type.total {st.core with pos := first} .I32 movedShape
  rw [popCall,WP.spec_ok] at poppedSpec
  have position : popped.pos = first := poppedSpec.2.2.1
  rw [position] at labelsDecoded
  have decoded : BrTable.Decoded data st.core.pos actual default readState.core.pos :=
    ⟨count,first,last,countDecoded,lengthEq,labelsDecoded,defaultDecoded⟩
  obtain ⟨rfl,rfl,_⟩ := decoded.unique encoded
  exact ⟨budget,buffer,types,bufferEq,callback⟩
end Exec.Code
