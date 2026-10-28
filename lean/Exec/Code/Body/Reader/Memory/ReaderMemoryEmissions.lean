import Exec.Code.Body.Reader.Memory.MemoryReaderFacts
import Exec.Code.Body.Reader.Memory.ReaderMemoryTypes
import Exec.Code.Local.Relations.Memory.MemoryEmission
import Exec.Code.Local.Relations.Common.CoreLoweringEffects
import Exec.Code.Body.Reader.Common.ReaderValues
import Exec.Code.Body.Reader.Common.ReaderProfile
import Exec.Code.Local.Lowering.Common.LoweringArithmetic
import Exec.Code.Local.Relations.Common.Prefix
import Exec.Code.Local.Relations.Common.ResolvedPrefix
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem reader_emit_memory_load_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (op : Abs.Memory.Load) (C : context)
    (contextLocalsCode : C.LOCALS = compilerLocals before)
    (contextMemories : C.MEMS = env.mem_types.val.map EnvTranslation.memType)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (memoryLoadOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (memoryLoadOpcode op)) before = .ok (.Ok (),out,after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧ after.next_source = out.core.pos ∧
    ∃ arg front values, Sequence.stackTypes st.core.vals.val = front ++ [.I32] ∧
      ReaderPostWasm2 p out.core (op.source (MemoryMeaning.memArg arg)) p.current.ctrl.polymorphic_base values ∧
      ∃ emitted, TypedLowered before after out.core.vals.val emitted (front ++ [valtype_numtype op.type]) ∧
        ScalarEmission C (front ++ [.I32]) (op.source (MemoryMeaning.memArg arg)) [emitted] (front ++ [valtype_numtype op.type]) := by
  obtain ⟨meaning,_,_,_,_,ordinary,base,sign,misc⟩ := memory_load_reader_facts ops before out.core op ⟨0#u32,0#u32⟩
  obtain ⟨capacity,run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨locals,p.ft.results⟩ index _ before after ordinary base sign misc contextLocals accepted
  obtain ⟨arg,values,callback,read,post⟩ := reader_memory_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core _ (memoryLoadMeaning op)
    capacity byte meaning run
  obtain ⟨_,kind,ty,source,callbackEq,_,_,_,_⟩ := memory_load_reader_facts ops before out.core op arg
  rw [callbackEq] at callback
  rw [source] at post
  simp only [memoryReader,kind,Bool.false_eq_true,↓reduceIte,ty] at read
  have ordinary := compiler_core_ordinary_result ops law before after out.core (.load op arg.offset arg.align) (.Ok ()) callback
  have sources := compiler_core_sources ops law before after out.core (.load op arg.offset arg.align) callback
  have cursor := compiler_core_cursor ops law before after out.core (.load op arg.offset arg.align) callback
  refine ⟨ordinary,sources,cursor,?_⟩
  obtain ⟨sourceC,outer,spine,header,base,typed,ctrls,blocks,vals⟩ := p.opened
  have currentKnown : ConcreteStack p.current.vals := (concreteStack_append.mp (vals ▸ known)).2
  have poly : Control.polymorphic st.core = false := by simpa [Control.polymorphic,ctrls] using monomorphic
  have baseEq : (Control.base st.core).val = outer.length := by simpa [Control.base,ctrls] using base
  obtain ⟨rest,shape,stack,controls,checked⟩ := reader_memory_load_stack st.core out.core data env _ _ arg outer p.current.vals
    vals baseEq poly currentKnown capacity read
  obtain ⟨front,types,oldTypes,concrete,newTypes⟩ := memory_load_stack_types known vals shape stack
  simp only [memoryRawType_translate] at oldTypes newTypes
  rw [oldTypes] at layout
  obtain ⟨memory,available⟩ := memory_reader_available env arg _ C contextMemories checked
  have lowered := compiler_memory_load_emission ops law before out.core types front op arg.offset arg.align
    C memory (MemoryMeaning.memArg arg) contextLocalsCode available rfl layout reachable concrete newTypes
    codeFits sourceFits coordinateFits
  rw [callback,WP.spec_ok] at lowered
  obtain ⟨emitted,lower,emission⟩ := lowered rfl
  exact ⟨arg,front,values,oldTypes,post,emitted,⟨lower,SourceStack.of_map types concrete newTypes⟩,emission⟩

theorem reader_emit_memory_store_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (op : Abs.Memory.Store) (C : context)
    (contextLocalsCode : C.LOCALS = compilerLocals before)
    (contextMemories : C.MEMS = env.mem_types.val.map EnvTranslation.memType)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (memoryStoreOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (memoryStoreOpcode op)) before = .ok (.Ok (),out,after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧ after.next_source = out.core.pos ∧
    ∃ arg front values, Sequence.stackTypes st.core.vals.val = front ++ [.I32,valtype_numtype op.type] ∧
      ReaderPostWasm2 p out.core (op.source (MemoryMeaning.memArg arg)) p.current.ctrl.polymorphic_base values ∧
      ∃ emitted, TypedLowered before after out.core.vals.val emitted (front) ∧
        ScalarEmission C (front ++ [.I32,valtype_numtype op.type]) (op.source (MemoryMeaning.memArg arg)) [emitted] (front) := by
  obtain ⟨meaning,_,_,_,_,ordinary,base,sign,misc⟩ := memory_store_reader_facts ops before out.core op ⟨0#u32,0#u32⟩
  obtain ⟨capacity,run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨locals,p.ft.results⟩ index _ before after ordinary base sign misc contextLocals accepted
  obtain ⟨arg,values,callback,read,post⟩ := reader_memory_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core _ (memoryStoreMeaning op)
    capacity byte meaning run
  obtain ⟨_,kind,ty,source,callbackEq,_,_,_,_⟩ := memory_store_reader_facts ops before out.core op arg
  rw [callbackEq] at callback
  rw [source] at post
  simp only [memoryReader,kind,↓reduceIte,ty] at read
  have ordinary := compiler_core_ordinary_result ops law before after out.core (.store op arg.offset arg.align) (.Ok ()) callback
  have sources := compiler_core_sources ops law before after out.core (.store op arg.offset arg.align) callback
  have cursor := compiler_core_cursor ops law before after out.core (.store op arg.offset arg.align) callback
  refine ⟨ordinary,sources,cursor,?_⟩
  obtain ⟨sourceC,outer,spine,header,base,typed,ctrls,blocks,vals⟩ := p.opened
  have currentKnown : ConcreteStack p.current.vals := (concreteStack_append.mp (vals ▸ known)).2
  have poly : Control.polymorphic st.core = false := by simpa [Control.polymorphic,ctrls] using monomorphic
  have baseEq : (Control.base st.core).val = outer.length := by simpa [Control.base,ctrls] using base
  obtain ⟨rest,shape,stack,controls,checked⟩ := reader_memory_store_stack st.core out.core data env _ _ arg outer p.current.vals
    vals baseEq poly currentKnown read
  obtain ⟨front,types,oldTypes,concrete,newTypes⟩ := memory_store_stack_types known vals shape stack
  simp only [memoryRawType_translate] at oldTypes newTypes
  rw [oldTypes] at layout
  obtain ⟨memory,available⟩ := memory_reader_available env arg _ C contextMemories checked
  have lowered := compiler_memory_store_emission ops law before out.core types front op arg.offset arg.align
    C memory (MemoryMeaning.memArg arg) contextLocalsCode available rfl layout reachable concrete newTypes
    codeFits sourceFits coordinateFits
  rw [callback,WP.spec_ok] at lowered
  obtain ⟨emitted,lower,emission⟩ := lowered rfl
  exact ⟨arg,front,values,oldTypes,post,emitted,⟨lower,SourceStack.of_map types concrete newTypes⟩,emission⟩
end Itasca.Runtime.Code
