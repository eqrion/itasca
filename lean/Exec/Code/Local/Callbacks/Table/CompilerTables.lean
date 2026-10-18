import Exec.Generated.Types
namespace Exec.Code
open Aeneas Aeneas.Std

/-- Function-local syntactic tables used by emitted instructions. -/
structure CompilerTables where
  indirect : List (U32 × U32)
  simd : List runtime.bytecode.SimdImmediate
  constants : List U128
  jumpTables : List U32

namespace CompilerTables

def empty : CompilerTables := ⟨[],[],[],[]⟩
def append (before extra : CompilerTables) : CompilerTables :=
  ⟨before.indirect ++ extra.indirect,before.simd ++ extra.simd,before.constants ++ extra.constants,before.jumpTables ++ extra.jumpTables⟩
def ofFunction (function : runtime.bytecode.CompiledFunction) : CompilerTables :=
  ⟨function.indirect.val,function.simd.val,function.v128_pool.val,function.jump_tables.val⟩

theorem append_assoc (a b c : CompilerTables) : append (append a b) c = append a (append b c) := by
  cases a; cases b; cases c
  simp only [append,List.append_assoc]

theorem append_empty (a : CompilerTables) : append a empty = a := by
  cases a
  simp only [append,empty,List.append_nil]

end CompilerTables

end Exec.Code
