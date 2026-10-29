import Itasca.Runtime.Compiler.Local.Callbacks.CodeGrowth.CompilerCodeMonotoneScalar
import Itasca.Runtime.Compiler.Body.Reader.Float.FloatConstantLowering
import Itasca.Runtime.Compiler.Body.Reader.Memory.MemoryEmissions
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupPreservation
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerTerminalMetadata
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerTableScratchScalar
import Itasca.Runtime.Compiler.Body.Control.Embedding.StructuredScalarEmbedding
import Itasca.Runtime.Compiler.Body.Callbacks.Prefix.CompilerPrefix
import Itasca.Runtime.Compiler.Local.Control.Segments.Structured
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredComposition
import Itasca.Runtime.Compiler.Local.Relations.Prefix.Concatenation
import Itasca.Runtime.Compiler.Local.Relations.Prefix.Extension
import Itasca.Runtime.Compiler.Local.Relations.Prefix.PrefixZipper
import Itasca.Runtime.Compiler.Local.Relations.Prefix.Prefix
import Itasca.Runtime.Compiler.Local.Relations.Prefix.ResolvedPrefix
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalPrefix
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalTerminal
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalDormant
import Itasca.Runtime.Compiler.Body.Reader.Control.Boundary
import Itasca.Runtime.Compiler.Body.Reader.Control.ScopeFronts
import Itasca.Runtime.Compiler.Body.Reader.Control.ReachabilitySteps
import Itasca.Runtime.Compiler.Body.Reader.Control.KnownFronts
import Itasca.Runtime.Compiler.Body.Reader.Global.GlobalEmissions
import Itasca.Runtime.Compiler.Body.Reader.Scalar.SelectEmissions
import Itasca.Runtime.Compiler.Body.Reader.Replay.Span
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerDeadMetadata
import Itasca.Runtime.Compiler.Body.Reader.Memory.Instructions
import Itasca.Runtime.Compiler.Local.Relations.Emission.CoreLoweringEffects
import Itasca.Runtime.Compiler.Body.Reader.Stacks.Values
import Itasca.Runtime.Compiler.Local.Lowering.Integer.LoweringArithmetic
import Itasca.Runtime.Compiler.Body.Reader.Float.FloatConstantEmissions
import Itasca.Runtime.Compiler.Body.Control.Embedding.StructuredLinearEmbedding
import Itasca.Runtime.Compiler.Local.Source.SourceCursor
import Itasca.Runtime.Compiler.Local.Relations.Operations.DeadCode
import Itasca.Runtime.Compiler.Body.Reader.Replay.ProfileAgreement
import Itasca.Runtime.Compiler.Local.Relations.Stacks.KnownPopStack
import Itasca.Runtime.Compiler.Body.Reader.Float.FloatConstant
import Itasca.Runtime.Compiler.Local.Callbacks.CodeGrowth.CompilerCodeMonotoneLiteral
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CompilerCodeMonotoneCallbacks
import Itasca.Runtime.Compiler.Body.Reader.Calls.Instructions
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerLiteralMetadata
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.FixupCallbacks
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerTableScratchLiteral
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerTableScratchCallbacks
import Itasca.Runtime.Compiler.Local.Relations.Syntax.ReaderOpcode
import Itasca.Runtime.Compiler.Local.Lowering.Integer.NumericEncoding
import Itasca.Runtime.Compiler.Body.Reader.Scalar.SignEmissions
import Itasca.Runtime.Compiler.Local.Relations.Stacks.KnownNumericStack
import Itasca.Runtime.Compiler.Body.Reader.Scalar.SignExtension
import Itasca.Runtime.Compiler.Body.Reader.Scalar.NumericEmissions
import Itasca.Runtime.Compiler.Body.Reader.Scalar.IntegerFacts
import Itasca.Runtime.Compiler.Body.Reader.Scalar.Emissions
import Itasca.Runtime.Compiler.Body.Reader.Scalar.Empty
import Itasca.Runtime.Compiler.Local.Lowering.Literal.LiteralSources
import Itasca.Runtime.Compiler.Local.Source.SourceLengthsTactic
import Itasca.Runtime.Compiler.Local.Lowering.Local.LoweringLocal
import Itasca.Runtime.Compiler.Local.Lowering.Literal.LiteralCursor
import Itasca.Runtime.Compiler.Local.Source.SourceCursorTactic
import Itasca.Runtime.Compiler.Body.Source.TypedLowering
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerMetadataTactic
import Itasca.Runtime.Compiler.Body.Reader.Local.LocalEmissions
import Itasca.Runtime.Compiler.Body.Reader.Local.LocalEffects
import Itasca.Runtime.Compiler.Body.Reader.Calls.CallLowering
import Itasca.Support.EnvTranslation
import Itasca.Runtime.Compiler.Body.Reader.Calls.CallEffects
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CallbackSources
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CallbackCursor
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerOrdinaryResults
import Itasca.Runtime.Compiler.Local.Capacity.EmissionGrowth
import Itasca.Runtime.Compiler.Body.Reader.Scalar.Unreachable
import Itasca.Runtime.Compiler.Local.Lowering.Control.LoweringReturn
import Itasca.Runtime.Compiler.Local.Relations.Control.KnownControlStack
import Itasca.Runtime.Compiler.Body.Reader.Control.ReturnStack
import Itasca.Runtime.Compiler.Body.Reader.Control.RootFrame
import Itasca.Runtime.Compiler.Local.Lowering.Emission.LoweringEmpty
import Itasca.Runtime.Compiler.Body.Reader.Float.FloatFacts
import Itasca.Runtime.Compiler.Body.Reader.Scalar.Saturating
import Itasca.Runtime.Compiler.Local.Lowering.Table.ScalarTablePreservation
import Itasca.Runtime.Compiler.Local.Lowering.Table.LiteralTablePreservation
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CallbackTables
import Itasca.Runtime.Compiler.Local.Callbacks.Effects.OrdinaryEffects
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CallbackCapacity
import Itasca.Runtime.Compiler.Local.Capacity.LiteralCapacity
import Itasca.Runtime.Compiler.Local.Lowering.Integer.NumericEffects
import Itasca.Runtime.Compiler.Local.Lowering.Float.FloatEffects

/-!
Every successful ordinary reader step is one compiler callback with
`OrdinaryEffects`. The per-opcode lemmas are stated over the shared scalar
step `code.step`; the `_wasm2` dispatchers reduce `code.step_profile .Wasm2`
to it first.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

theorem reader_unreachable_effects {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 0#u8 before = .ok (.Ok (),out,after)) :
    OrdinaryEffects before after out := by
  have dispatch := dispatch_unreachable (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at accepted
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ accepted
  cases value
  exact ⟨compiler_unreachable_tables ops law before after out callback,
    compiler_unreachable_depths ops law before after out callback,
    compiler_unreachable_code_mono ops law before after out callback,
    compiler_unreachable_ordinary_result ops law before after out _ callback,
    compiler_unreachable_capacity ops law before after out callback⟩

theorem reader_nop_effects {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 1#u8 before = .ok (.Ok (),out,after)) :
    OrdinaryEffects before after out := by
  have dispatch := dispatch_nop (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at accepted
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ accepted
  cases value
  exact ⟨compiler_nop_tables ops law before after out callback,
    compiler_nop_depths ops law before after out callback,
    compiler_nop_code_mono ops law before after out callback,
    compiler_nop_ordinary_result ops law before after out _ callback,
    compiler_nop_capacity ops law before after out callback⟩

theorem reader_drop_effects {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 26#u8 before = .ok (.Ok (),out,after)) :
    OrdinaryEffects before after out := by
  have dispatch := dispatch_drop (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at accepted
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ accepted
  exact ⟨compiler_drop_tables ops law before after out value callback,
    compiler_drop_depths ops law before after out value callback,
    compiler_drop_code_mono ops law before after out value callback,
    compiler_drop_ordinary_result ops law before after out value _ callback,
    compiler_drop_capacity ops law before after out value callback⟩

theorem reader_local_get_effects {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 32#u8 before = .ok (.Ok (),out,after)) :
    OrdinaryEffects before after out := by
  have dispatch := dispatch_local_get (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at accepted
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ accepted
  exact ⟨compiler_local_get_tables ops law before after out value callback,
    compiler_local_get_depths ops law before after out value callback,
    compiler_local_get_code_mono ops law before after out value callback,
    compiler_local_get_ordinary_result ops law before after out value _ callback,
    compiler_local_get_capacity ops law before after out value callback⟩

theorem reader_local_set_effects {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 33#u8 before = .ok (.Ok (),out,after)) :
    OrdinaryEffects before after out := by
  have dispatch := dispatch_local_set (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at accepted
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ accepted
  exact ⟨compiler_local_set_tables ops law before after out value callback,
    compiler_local_set_depths ops law before after out value callback,
    compiler_local_set_code_mono ops law before after out value callback,
    compiler_local_set_ordinary_result ops law before after out value _ callback,
    compiler_local_set_capacity ops law before after out value callback⟩

theorem reader_local_tee_effects {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 34#u8 before = .ok (.Ok (),out,after)) :
    OrdinaryEffects before after out := by
  have dispatch := dispatch_local_tee (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at accepted
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ accepted
  exact ⟨compiler_local_tee_tables ops law before after out value callback,
    compiler_local_tee_depths ops law before after out value callback,
    compiler_local_tee_code_mono ops law before after out value callback,
    compiler_local_tee_ordinary_result ops law before after out value _ callback,
    compiler_local_tee_capacity ops law before after out value callback⟩

theorem reader_i32_const_effects {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 65#u8 before = .ok (.Ok (),out,after)) :
    OrdinaryEffects before after out := by
  have dispatch := dispatch_i32_const (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at accepted
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ accepted
  exact ⟨compiler_i32_const_tables ops law before after out value callback,
    compiler_i32_const_depths ops law before after out value callback,
    compiler_i32_const_code_mono ops law before after out value callback,
    compiler_i32_const_ordinary_result ops law before after out value _ callback,
    compiler_i32_const_capacity ops law before after out value callback⟩

theorem reader_i64_const_effects {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 66#u8 before = .ok (.Ok (),out,after)) :
    OrdinaryEffects before after out := by
  have dispatch := dispatch_i64_const (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at accepted
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ accepted
  exact ⟨compiler_i64_const_tables ops law before after out value callback,
    compiler_i64_const_depths ops law before after out value callback,
    compiler_i64_const_code_mono ops law before after out value callback,
    compiler_i64_const_ordinary_result ops law before after out value _ callback,
    compiler_i64_const_capacity ops law before after out value callback⟩

theorem reader_select_effects {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 27#u8 before = .ok (.Ok (),out,after)) :
    OrdinaryEffects before after out := by
  have dispatch := dispatch_select (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at accepted
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ accepted
  exact ⟨compiler_core_tables ops law before after out (.select false) callback,
    compiler_core_depths ops law before after out (.select false) callback,
    compiler_core_code_mono ops law before after out (.select false) callback,
    compiler_core_ordinary_result ops law before after out (.select false) _ callback,
    compiler_core_capacity ops law before after out (.select false) callback⟩

theorem reader_global_get_effects {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 35#u8 before = .ok (.Ok (),out,after)) :
    OrdinaryEffects before after out := by
  have dispatch := dispatch_global_get (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at accepted
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ accepted
  exact ⟨compiler_core_tables ops law before after out (.globalGet value) callback,
    compiler_core_depths ops law before after out (.globalGet value) callback,
    compiler_core_code_mono ops law before after out (.globalGet value) callback,
    compiler_core_ordinary_result ops law before after out (.globalGet value) _ callback,
    compiler_core_capacity ops law before after out (.globalGet value) callback⟩

theorem reader_global_set_effects {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 36#u8 before = .ok (.Ok (),out,after)) :
    OrdinaryEffects before after out := by
  have dispatch := dispatch_global_set (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at accepted
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ accepted
  exact ⟨compiler_core_tables ops law before after out (.globalSet value) callback,
    compiler_core_depths ops law before after out (.globalSet value) callback,
    compiler_core_code_mono ops law before after out (.globalSet value) callback,
    compiler_core_ordinary_result ops law before after out (.globalSet value) _ callback,
    compiler_core_capacity ops law before after out (.globalSet value) callback⟩

theorem reader_f32_const_effects {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 67#u8 before = .ok (.Ok (),out,after)) :
    OrdinaryEffects before after out := by
  have dispatch := dispatch_f32_const (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at accepted
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ accepted
  change runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f32_const ops before out value = _ at callback
  rw [callback_float32_eq] at callback
  exact ⟨compiler_op65_tables ops law before after out _ _ _ callback,
    compiler_op65_depths ops law before after out _ _ _ callback,
    compiler_op65_code_mono ops law before after out _ _ _ callback,
    compiler_op65_ordinary_result ops law before after out _ _ _ _ callback,
    compiler_op65_capacity ops law before after out _ _ _ callback⟩

theorem reader_f64_const_effects {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 68#u8 before = .ok (.Ok (),out,after)) :
    OrdinaryEffects before after out := by
  have dispatch := dispatch_f64_const (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at accepted
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ accepted
  change runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f64_const ops before out value = _ at callback
  rw [callback_float64_eq] at callback
  exact ⟨compiler_op66_tables ops law before after out _ _ _ callback,
    compiler_op66_depths ops law before after out _ _ _ callback,
    compiler_op66_code_mono ops law before after out _ _ _ callback,
    compiler_op66_ordinary_result ops law before after out _ _ _ _ callback,
    compiler_op66_capacity ops law before after out _ _ _ callback⟩

theorem reader_memory_load_effects {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (op : SourceMachine.Memory.Load)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (memoryLoadOpcode op)) before = .ok (.Ok (),out,after)) :
    OrdinaryEffects before after out := by
  obtain ⟨meaning,_,_,_,_,_,_,_,_⟩ := memory_load_reader_facts ops before out op ⟨0#u32,0#u32⟩
  rw [code.step_memory.dispatch (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx before _ (memoryLoadMeaning op) meaning] at accepted
  obtain ⟨arg,read,callback⟩ := reader_run_success _ _ _ _ _ accepted
  obtain ⟨_,kind,ty,source,callbackEq,_,_,_,_⟩ := memory_load_reader_facts ops before out op arg
  rw [callbackEq] at callback
  exact ⟨compiler_core_tables ops law before after out (.load op arg.offset arg.align) callback,
    compiler_core_depths ops law before after out (.load op arg.offset arg.align) callback,
    compiler_core_code_mono ops law before after out (.load op arg.offset arg.align) callback,
    compiler_core_ordinary_result ops law before after out (.load op arg.offset arg.align) _ callback,
    compiler_core_capacity ops law before after out (.load op arg.offset arg.align) callback⟩

theorem reader_memory_store_effects {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (op : SourceMachine.Memory.Store)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (memoryStoreOpcode op)) before = .ok (.Ok (),out,after)) :
    OrdinaryEffects before after out := by
  obtain ⟨meaning,_,_,_,_,_,_,_,_⟩ := memory_store_reader_facts ops before out op ⟨0#u32,0#u32⟩
  rw [code.step_memory.dispatch (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx before _ (memoryStoreMeaning op) meaning] at accepted
  obtain ⟨arg,read,callback⟩ := reader_run_success _ _ _ _ _ accepted
  obtain ⟨_,kind,ty,source,callbackEq,_,_,_,_⟩ := memory_store_reader_facts ops before out op arg
  rw [callbackEq] at callback
  exact ⟨compiler_core_tables ops law before after out (.store op arg.offset arg.align) callback,
    compiler_core_depths ops law before after out (.store op arg.offset arg.align) callback,
    compiler_core_code_mono ops law before after out (.store op arg.offset arg.align) callback,
    compiler_core_ordinary_result ops law before after out (.store op arg.offset arg.align) _ callback,
    compiler_core_capacity ops law before after out (.store op arg.offset arg.align) callback⟩

theorem reader_numeric_base_effects {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (op : SourceMachine.Numeric.Instruction) (baseOpcode : (integerOpcode op).val < 192)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (integerOpcode op)) before = .ok (.Ok (),out,after)) :
    OrdinaryEffects before after out := by
  obtain ⟨operation,hook,meaning,handler,_,_,_,hookEq,_,_,_,_⟩ := integer_reader_facts ops before out op baseOpcode
  rw [dispatch_numeric (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx before _ operation hook meaning handler] at accepted
  obtain ⟨reply,read,callback⟩ := reader_run_success _ _ _ _ _ accepted
  cases reply
  rw [hookEq] at callback
  exact ⟨compiler_numeric_tables ops law before after out op callback,
    compiler_numeric_depths ops law before after out op callback,
    compiler_numeric_code_mono ops law before after out op callback,
    compiler_numeric_ordinary_result ops law before after out op _ callback,
    compiler_numeric_capacity ops law before after out op callback⟩

theorem reader_float_base_effects {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (op : SourceMachine.Float.Instruction) (baseOpcode : (floatOpcode op).val < 256)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (floatOpcode op)) before = .ok (.Ok (),out,after)) :
    OrdinaryEffects before after out := by
  obtain ⟨operation,hook,meaning,handler,_,_,_,hookEq,_,_,_,_⟩ := float_reader_facts ops before out op baseOpcode
  rw [dispatch_numeric (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx before _ operation hook meaning handler] at accepted
  obtain ⟨reply,read,callback⟩ := reader_run_success _ _ _ _ _ accepted
  cases reply
  rw [hookEq] at callback
  exact ⟨compiler_float_tables ops law before after out op callback,
    compiler_float_depths ops law before after out op callback,
    compiler_float_code_mono ops law before after out op callback,
    compiler_float_ordinary_result ops law before after out op _ callback,
    compiler_float_capacity ops law before after out op callback⟩

theorem reader_ordinary_base_effects {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (opcode : U8) (ordinary : opcode ∈ readerBaseOrdinaryOpcodes)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx opcode before = .ok (.Ok (),out,after)) :
    OrdinaryEffects before after out := by
  simp only [readerBaseOrdinaryOpcodes,List.mem_cons,List.not_mem_nil,or_false] at ordinary
  rcases ordinary with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reader_unreachable_effects ops law before after st out data env ctx accepted
  · exact reader_nop_effects ops law before after st out data env ctx accepted
  · simp [code.step, code.step_numeric.unrecognized _ _ _ _ (by decide : Numeric.opcodeMeaning 15#u8 = none)]
      at accepted
  · simp [code.step, code.step_numeric.unrecognized _ _ _ _ (by decide : Numeric.opcodeMeaning 16#u8 = none)]
      at accepted
  · exact reader_drop_effects ops law before after st out data env ctx accepted
  · exact reader_local_get_effects ops law before after st out data env ctx accepted
  · exact reader_local_set_effects ops law before after st out data env ctx accepted
  · exact reader_local_tee_effects ops law before after st out data env ctx accepted
  · exact reader_i32_const_effects ops law before after st out data env ctx accepted
  · exact reader_i64_const_effects ops law before after st out data env ctx accepted
  · exact reader_numeric_base_effects ops law before after st out data env ctx (.eqz .I32) (by decide) accepted
  · exact reader_numeric_base_effects ops law before after st out data env ctx (.compare .I32 .EQ) (by decide) accepted
  · exact reader_numeric_base_effects ops law before after st out data env ctx (.compare .I32 (.LT .U)) (by decide) accepted
  · exact reader_numeric_base_effects ops law before after st out data env ctx (.eqz .I64) (by decide) accepted
  · exact reader_numeric_base_effects ops law before after st out data env ctx (.compare .I64 .EQ) (by decide) accepted
  · exact reader_numeric_base_effects ops law before after st out data env ctx (.compare .I64 (.LT .U)) (by decide) accepted
  · exact reader_numeric_base_effects ops law before after st out data env ctx (.binary .I32 .ADD) (by decide) accepted
  · exact reader_numeric_base_effects ops law before after st out data env ctx (.binary .I32 .SUB) (by decide) accepted
  · exact reader_numeric_base_effects ops law before after st out data env ctx (.binary .I64 .ADD) (by decide) accepted
  · exact reader_numeric_base_effects ops law before after st out data env ctx (.binary .I64 .SUB) (by decide) accepted

theorem reader_scalar_effects {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (opcode : U8) (covered : opcode.val ∈ scalarOpcodeValues)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx opcode before = .ok (.Ok (),out,after)) :
    OrdinaryEffects before after out := by
  simp only [scalarOpcodeValues,List.mem_cons,List.mem_nil_iff,or_false] at covered
  rcases covered with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · obtain rfl : opcode = 27#u8 := (UScalar.eq_equiv _ _).mpr h
    exact reader_select_effects ops law before after st out data env ctx accepted
  · obtain rfl : opcode = 35#u8 := (UScalar.eq_equiv _ _).mpr h
    exact reader_global_get_effects ops law before after st out data env ctx accepted
  · obtain rfl : opcode = 36#u8 := (UScalar.eq_equiv _ _).mpr h
    exact reader_global_set_effects ops law before after st out data env ctx accepted
  · obtain rfl : opcode = 67#u8 := (UScalar.eq_equiv _ _).mpr h
    exact reader_f32_const_effects ops law before after st out data env ctx accepted
  · obtain rfl : opcode = 68#u8 := (UScalar.eq_equiv _ _).mpr h
    exact reader_f64_const_effects ops law before after st out data env ctx accepted
  · obtain rfl : opcode = 40#u8 := (UScalar.eq_equiv _ _).mpr h
    exact reader_memory_load_effects ops law before after st out data env ctx (.full .I32) accepted
  · obtain rfl : opcode = 41#u8 := (UScalar.eq_equiv _ _).mpr h
    exact reader_memory_load_effects ops law before after st out data env ctx (.full .I64) accepted
  · obtain rfl : opcode = 42#u8 := (UScalar.eq_equiv _ _).mpr h
    exact reader_memory_load_effects ops law before after st out data env ctx (.full .F32) accepted
  · obtain rfl : opcode = 43#u8 := (UScalar.eq_equiv _ _).mpr h
    exact reader_memory_load_effects ops law before after st out data env ctx (.full .F64) accepted
  · obtain rfl : opcode = 44#u8 := (UScalar.eq_equiv _ _).mpr h
    exact reader_memory_load_effects ops law before after st out data env ctx (.packed .I32 .byte .S) accepted
  · obtain rfl : opcode = 45#u8 := (UScalar.eq_equiv _ _).mpr h
    exact reader_memory_load_effects ops law before after st out data env ctx (.packed .I32 .byte .U) accepted
  · obtain rfl : opcode = 46#u8 := (UScalar.eq_equiv _ _).mpr h
    exact reader_memory_load_effects ops law before after st out data env ctx (.packed .I32 .half .S) accepted
  · obtain rfl : opcode = 47#u8 := (UScalar.eq_equiv _ _).mpr h
    exact reader_memory_load_effects ops law before after st out data env ctx (.packed .I32 .half .U) accepted
  · obtain rfl : opcode = 48#u8 := (UScalar.eq_equiv _ _).mpr h
    exact reader_memory_load_effects ops law before after st out data env ctx (.packed .I64 .byte .S) accepted
  · obtain rfl : opcode = 49#u8 := (UScalar.eq_equiv _ _).mpr h
    exact reader_memory_load_effects ops law before after st out data env ctx (.packed .I64 .byte .U) accepted
  · obtain rfl : opcode = 50#u8 := (UScalar.eq_equiv _ _).mpr h
    exact reader_memory_load_effects ops law before after st out data env ctx (.packed .I64 .half .S) accepted
  · obtain rfl : opcode = 51#u8 := (UScalar.eq_equiv _ _).mpr h
    exact reader_memory_load_effects ops law before after st out data env ctx (.packed .I64 .half .U) accepted
  · obtain rfl : opcode = 52#u8 := (UScalar.eq_equiv _ _).mpr h
    exact reader_memory_load_effects ops law before after st out data env ctx (.packed .I64 .word .S) accepted
  · obtain rfl : opcode = 53#u8 := (UScalar.eq_equiv _ _).mpr h
    exact reader_memory_load_effects ops law before after st out data env ctx (.packed .I64 .word .U) accepted
  · obtain rfl : opcode = 54#u8 := (UScalar.eq_equiv _ _).mpr h
    exact reader_memory_store_effects ops law before after st out data env ctx (.full .I32) accepted
  · obtain rfl : opcode = 55#u8 := (UScalar.eq_equiv _ _).mpr h
    exact reader_memory_store_effects ops law before after st out data env ctx (.full .I64) accepted
  · obtain rfl : opcode = 56#u8 := (UScalar.eq_equiv _ _).mpr h
    exact reader_memory_store_effects ops law before after st out data env ctx (.full .F32) accepted
  · obtain rfl : opcode = 57#u8 := (UScalar.eq_equiv _ _).mpr h
    exact reader_memory_store_effects ops law before after st out data env ctx (.full .F64) accepted
  · obtain rfl : opcode = 58#u8 := (UScalar.eq_equiv _ _).mpr h
    exact reader_memory_store_effects ops law before after st out data env ctx (.packed .I32 .byte) accepted
  · obtain rfl : opcode = 59#u8 := (UScalar.eq_equiv _ _).mpr h
    exact reader_memory_store_effects ops law before after st out data env ctx (.packed .I32 .half) accepted
  · obtain rfl : opcode = 60#u8 := (UScalar.eq_equiv _ _).mpr h
    exact reader_memory_store_effects ops law before after st out data env ctx (.packed .I64 .byte) accepted
  · obtain rfl : opcode = 61#u8 := (UScalar.eq_equiv _ _).mpr h
    exact reader_memory_store_effects ops law before after st out data env ctx (.packed .I64 .half) accepted
  · obtain rfl : opcode = 62#u8 := (UScalar.eq_equiv _ _).mpr h
    exact reader_memory_store_effects ops law before after st out data env ctx (.packed .I64 .word) accepted

/-- A successful Wasm 2 step on an opcode without profile-specific handling
is the shared scalar step. -/
theorem base_step_wasm2 {V : Type} (visitor : code.OpVisitor V)
    {st out : code.BodyState} {data : Slice U8} {env : module.Env} {ctx : code.Context}
    {index : U32} {opcode : U8} {before after : V}
    (ordinary : opcode.val ∉ Wasm2.controlOpcodes)
    (base : opcode.val ∉ [28, 37, 38, 208, 209, 210, 252, 253])
    (sign : Wasm2.NumericExtensions.signMeaning opcode = none) (misc : opcode ≠ code.OP_MISC_PREFIX)
    (accepted : code.step_profile visitor st data env ctx index .Wasm2 opcode before =
      .ok (.Ok (), out, after)) :
    code.step visitor st.core data env ctx opcode before = .ok (.Ok (), out.core, after) :=
  (profile_base_success_wasm2 visitor st out data env ctx ctx index opcode before after
    ordinary base sign misc rfl accepted).2

theorem reader_return_effects_wasm2 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.BodyState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 15#u8 before = .ok (.Ok (),out,after)) :
    OrdinaryEffects before after out.core := by
  rw [Wasm2.CallbackTrace.dispatch_return] at accepted
  obtain ⟨value,read,callback⟩ := reader_body_success _ _ _ _ _ _ accepted
  cases value
  exact ⟨compiler_return_tables ops law before after out.core callback,
    compiler_return_depths ops law before after out.core callback,
    compiler_return_code_mono ops law before after out.core callback,
    compiler_return_ordinary_result ops law before after out.core _ callback,
    compiler_return_capacity ops law before after out.core callback⟩

theorem reader_call_effects_wasm2 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.BodyState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 16#u8 before = .ok (.Ok (),out,after)) :
    OrdinaryEffects before after out.core := by
  rw [Wasm2.CallbackTrace.dispatch_call] at accepted
  obtain ⟨value,read,callback⟩ := reader_body_success _ _ _ _ _ _ accepted
  exact ⟨compiler_call_tables ops law before after out.core value callback,
    compiler_call_depths ops law before after out.core value callback,
    compiler_call_code_mono ops law before after out.core value callback,
    compiler_call_ordinary_result ops law before after out.core value _ callback,
    compiler_call_capacity ops law before after out.core value callback⟩

theorem reader_numeric_effects_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (op : SourceMachine.Numeric.Instruction)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (integerOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (integerOpcode op)) before = .ok (.Ok (),out,after)) :
    OrdinaryEffects before after out.core := by
  by_cases small : (integerOpcode op).val < 192
  · obtain ⟨_,_,_,_,_,_,_,_,ordinary,base,sign,misc⟩ := integer_reader_facts ops before out.core op small
    exact reader_numeric_base_effects ops law before after st.core out.core data env ctx op small
      (base_step_wasm2 _ ordinary base sign misc accepted)
  · obtain ⟨_,_,_,_,callback,_⟩ := reader_integer_sign_wasm2 p ops before after out ctx op (by omega) byte accepted
    exact ⟨compiler_numeric_tables ops law before after out.core op callback,
    compiler_numeric_depths ops law before after out.core op callback,
    compiler_numeric_code_mono ops law before after out.core op callback,
    compiler_numeric_ordinary_result ops law before after out.core op _ callback,
    compiler_numeric_capacity ops law before after out.core op callback⟩

theorem reader_saturating_effects_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (op : SourceMachine.Float.Instruction) (extension : 256 ≤ (floatOpcode op).val)
    (subopcode : U32) (next : Usize) (subopcodeEq : subopcode.val = (floatOpcode op).val - 256)
    (decoded : Leb128.Decoded data st.core.pos subopcode next)
    (byte : data.val[p.start.val]'p.inbounds = 252#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 252#u8 before = .ok (.Ok (),out,after)) :
    OrdinaryEffects before after out.core := by
  obtain ⟨_,_,_,_,callback,_⟩ :=
    reader_float_saturating_wasm2 p ops before after out ctx op extension subopcode next subopcodeEq decoded byte accepted
  exact ⟨compiler_float_tables ops law before after out.core op callback,
    compiler_float_depths ops law before after out.core op callback,
    compiler_float_code_mono ops law before after out.core op callback,
    compiler_float_ordinary_result ops law before after out.core op _ callback,
    compiler_float_capacity ops law before after out.core op callback⟩

theorem reader_ordinary_effects_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (opcode : U8) (ordinary : opcode ∈ readerOrdinaryOpcodes)
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 opcode before = .ok (.Ok (),out,after)) :
    OrdinaryEffects before after out.core := by
  rcases List.mem_append.mp ordinary with base | numeric
  · simp only [readerBaseOrdinaryOpcodes,List.mem_cons,List.not_mem_nil,or_false] at base
    rcases base with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact reader_return_effects_wasm2 ops law before after st out data env ctx index accepted
      | exact reader_call_effects_wasm2 ops law before after st out data env ctx index accepted
      | exact reader_ordinary_base_effects ops law before after st.core out.core data env ctx _ (by decide)
          (base_step_wasm2 _ (by decide) (by decide) rfl (by simp only [global_simps]; decide) accepted)
  · obtain ⟨op,rfl⟩ := integer_opcode_of_mem numeric
    exact reader_numeric_effects_wasm2 p ops law before after out ctx op byte accepted

private theorem scalar_base_conditions {opcode : U8} (covered : opcode.val ∈ scalarOpcodeValues) :
    opcode.val ∉ Wasm2.controlOpcodes ∧ opcode.val ∉ [28, 37, 38, 208, 209, 210, 252, 253] ∧
      Wasm2.NumericExtensions.signMeaning opcode = none ∧ opcode ≠ code.OP_MISC_PREFIX := by
  simp only [scalarOpcodeValues,List.mem_cons,List.mem_nil_iff,or_false] at covered
  rcases covered with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals exact ⟨by rw [h]; decide, by rw [h]; decide,
    by unfold Wasm2.NumericExtensions.signMeaning; split <;> simp_all,
    fun equal => by rw [equal] at h; simp [code.OP_MISC_PREFIX] at h⟩

theorem reader_scalar_effects_wasm2 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.BodyState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (opcode : U8) (covered : opcode.val ∈ scalarOpcodeValues)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 opcode before = .ok (.Ok (),out,after)) :
    OrdinaryEffects before after out.core :=
  have ⟨ordinary,base,sign,misc⟩ := scalar_base_conditions covered
  reader_scalar_effects ops law before after st.core out.core data env ctx opcode covered
    (base_step_wasm2 _ ordinary base sign misc accepted)

theorem reader_float_base_effects_wasm2 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.BodyState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (op : SourceMachine.Float.Instruction) (baseOpcode : (floatOpcode op).val < 256)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (floatOpcode op)) before = .ok (.Ok (),out,after)) :
    OrdinaryEffects before after out.core :=
  have ⟨_,_,_,_,_,_,_,_,ordinary,base,sign,misc⟩ := float_reader_facts ops before out.core op baseOpcode
  reader_float_base_effects ops law before after st.core out.core data env ctx op baseOpcode
    (base_step_wasm2 _ ordinary base sign misc accepted)

theorem reader_memory_load_effects_wasm2 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.BodyState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32) (op : SourceMachine.Memory.Load)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (memoryLoadOpcode op)) before = .ok (.Ok (),out,after)) :
    OrdinaryEffects before after out.core :=
  have ⟨_,_,_,_,_,ordinary,base,sign,misc⟩ := memory_load_reader_facts ops before out.core op ⟨0#u32,0#u32⟩
  reader_memory_load_effects ops law before after st.core out.core data env ctx op
    (base_step_wasm2 _ ordinary base sign misc accepted)

theorem reader_memory_store_effects_wasm2 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.BodyState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32) (op : SourceMachine.Memory.Store)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (memoryStoreOpcode op)) before = .ok (.Ok (),out,after)) :
    OrdinaryEffects before after out.core :=
  have ⟨_,_,_,_,_,ordinary,base,sign,misc⟩ := memory_store_reader_facts ops before out.core op ⟨0#u32,0#u32⟩
  reader_memory_store_effects ops law before after st.core out.core data env ctx op
    (base_step_wasm2 _ ordinary base sign misc accepted)

end Itasca.Runtime.Compiler
