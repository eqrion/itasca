import Itasca.Runtime.Compiler.Local.Relations.Table.StatefulAuxiliaryTables
namespace Itasca.Runtime.Compiler
open Aeneas.Std

theorem compiler_tables_pair_append (before after : runtime.bytecode.CompiledFunction)
    (extra : List (U32 × U32))
    (pairs : after.indirect.val = before.indirect.val ++ extra)
    (auxiliary : compilerAuxiliaryTables after = compilerAuxiliaryTables before) :
    CompilerTables.ofFunction after = (CompilerTables.ofFunction before).append ⟨extra,[],[],[]⟩ := by
  simp only [compilerAuxiliaryTables, Prod.mk.injEq] at auxiliary
  obtain ⟨simd,constants,jumps⟩ := auxiliary
  simp only [CompilerTables.ofFunction,CompilerTables.append,CompilerTables.mk.injEq,List.append_nil]
  exact ⟨pairs,simd,constants,jumps⟩
end Itasca.Runtime.Compiler
