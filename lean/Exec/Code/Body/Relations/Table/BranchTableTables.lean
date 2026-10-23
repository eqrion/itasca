import Exec.Code.Local.Relations.Table.BranchTableEffects
import Exec.Code.Body.Reader.Table.ReaderTableEffects
import Exec.Code.Local.Callbacks.Table.CompilerTables
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem compiler_br_table_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : code.OpIterState) (fallback : U32) (types : signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops before state fallback types=.ok (.Ok (),after)) :
    ∃ targets, CompilerTables.ofFunction after.function =
      (CompilerTables.ofFunction before.function).append ⟨[],[],[],targets⟩ := by
  by_cases live : before.reachable=true
  · have fixed := compiler_br_table_fixed ops law before after state fallback types live accepted
    obtain ⟨budget,depths,start,len,selector,emitted,lowered,targets,_,_,_,_,_,_,_,tables,_⟩ :=
      compiler_br_table_production ops law before after state fallback types live accepted
    refine ⟨targets,?_⟩
    simp only [CompilerTables.ofFunction,CompilerTables.append,List.append_nil,
      fixed.indirect,fixed.simd,fixed.constants,tables]
  · obtain ⟨fixed,_,tables,_⟩ := compiler_br_table_dead_effect ops law before after state fallback types
      (Bool.eq_false_iff.mpr live) accepted
    refine ⟨[],?_⟩
    simp only [CompilerTables.ofFunction,CompilerTables.append,List.append_nil,
      fixed.indirect,fixed.simd,fixed.constants,tables]

theorem compiler_reader_table_tables_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st final : code.BodyState) (data : Slice U8) (env : module.Env)
    (shape : Control.Shape st.core) (depths : List U32) (fallback : U32) (next : Usize)
    (encoded : BrTable.Decoded data st.core.pos depths fallback next)
    (accepted : code.branch_table_with (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env .Wasm2 before=.ok (.Ok (),final,after)) :
    ∃ targets, CompilerTables.ofFunction after.function =
      (CompilerTables.ofFunction before.function).append ⟨[],[],[],targets⟩ := by
  obtain ⟨budget,buffer,types,_,callback⟩ := compiler_table_source_wasm2 ops law before after st final data env
    shape depths fallback next encoded accepted
  exact compiler_br_table_tables ops law {before with budget,table_depths := buffer} after final.core fallback types callback
end Exec.Code
