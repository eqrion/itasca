import Exec.Code.Local.Relations.Memory.MemoryOperands

namespace Exec.Code
open Aeneas Aeneas.Std

@[step] theorem compiler_memory_load_emission {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.types.ValueType)
    (front : List valtype) (op : Abs.Memory.Load) (offset alignment : U32)
    (C : context) (memory : memtype) (argument : memarg)
    (locals : C.LOCALS = compilerLocals compiler) (available : C.MEMS[0]? = some memory)
    (sourceOffset : argument.OFFSET = .mk_uN offset.val)
    (layout : CompilerLayout compiler (front ++ [.I32])) (reachable : compiler.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (typed : types.map Itasca.Translate.valueType = front ++ [valtype_numtype op.type])
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (memoryLoadOpcode op) offset alignment 0#u128
      ⦃ out => out.1 = .Ok () → ∃ instruction,
        Lowered compiler out.2 instruction (front ++ [valtype_numtype op.type]) ∧
        CoreEmission C (front ++ [.I32]) (op.source argument) [instruction] (front ++ [valtype_numtype op.type]) ⦄ := by
  apply WP.spec_mono (compiler_memory_load_lowered ops law compiler state types front op offset alignment
    layout reachable concrete typed codeFits sourceFits coordinateFits)
  intro out success accepted
  obtain ⟨address,position,lowered⟩ := success accepted
  exact ⟨_,lowered,.load front op argument address offset memory available sourceOffset (by simpa only [locals] using position)⟩

@[step] theorem compiler_memory_store_emission {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.types.ValueType)
    (front : List valtype) (op : Abs.Memory.Store) (offset alignment : U32)
    (C : context) (memory : memtype) (argument : memarg)
    (locals : C.LOCALS = compilerLocals compiler) (available : C.MEMS[0]? = some memory)
    (sourceOffset : argument.OFFSET = .mk_uN offset.val)
    (layout : CompilerLayout compiler (front ++ [.I32,valtype_numtype op.type])) (reachable : compiler.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (typed : types.map Itasca.Translate.valueType = front)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (memoryStoreOpcode op) offset alignment 0#u128
      ⦃ out => out.1 = .Ok () → ∃ instruction,
        Lowered compiler out.2 instruction front ∧
        CoreEmission C (front ++ [.I32,valtype_numtype op.type]) (op.source argument) [instruction] front ⦄ := by
  apply WP.spec_mono (compiler_memory_store_lowered ops law compiler state types front op offset alignment
    layout reachable concrete typed codeFits sourceFits coordinateFits)
  intro out success accepted
  obtain ⟨address,value,addressPosition,valuePosition,lowered⟩ := success accepted
  exact ⟨_,lowered,.store front op argument address value offset memory available sourceOffset
    (by simpa only [locals] using addressPosition) valuePosition⟩
end Exec.Code
