import Itasca.Runtime.Compiler.Body.Reader.Local.LocalEffects
import Itasca.Wasm2.Scalar.MemoryReader
import Itasca.Runtime.Compiler.Body.Reader.Replay.Post
import Itasca.Runtime.Compiler.Local.Relations.Memory.MemoryOpcode
import Itasca.Runtime.Compiler.Body.Source.TypedLowering
import Itasca.Runtime.Compiler.Local.Relations.Memory.MemoryEmission
import Itasca.Runtime.Compiler.Local.Relations.Emission.CoreLoweringEffects
import Itasca.Runtime.Compiler.Body.Reader.Stacks.Values
import Itasca.Runtime.Compiler.Body.Reader.Replay.ProfileAgreement
import Itasca.Runtime.Compiler.Local.Lowering.Integer.NumericLowering
import Itasca.Runtime.Compiler.Local.Relations.Prefix.SuspendedPrefix

/-!
Sections, each formerly its own module: MemoryStacks, Instructions, MemoryTypes, MemoryEmissions.
-/

/-! ## MemoryStacks -/

section

/-!
Accepted load readers replace exactly the live i32 address with the specified numeric result type. Decoding the memory argument preserves operands.

Main declarations: `reader_memory_load_stack` and `reader_memory_store_stack`. A direct consumer is `Compiler.Body.Reader.Memory.Instructions`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Accepted load readers replace exactly the live i32 address with the
specified numeric result type. Decoding the memory argument preserves operands. -/
theorem reader_memory_load_stack (st out : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (ty : wasm_types.ValueType) (natural : U32) (arg : code.MemArg)
    (outer segment : List code.StackType)
    (values : st.vals.val = outer ++ segment) (base : (Control.base st).val = outer.length)
    (monomorphic : Control.polymorphic st = false) (known : ConcreteStack segment)
    (capacity : st.vals.val.length < Usize.max)
    (accepted : code.read_load st data env ty natural = .ok (.Ok arg,out)) :
    ∃ rest, segment = rest ++ [.Val .I32] ∧ out.vals.val = outer ++ rest ++ [.Val ty] ∧
      out.ctrls = st.ctrls ∧ code.check_memory_and_alignment env arg natural = .ok (.Ok ()) := by
  obtain ⟨⟨result,middle⟩,read,sameValues,controls,meaning⟩ := WP.spec_imp_exists (code.read_memarg.spec st data)
  dsimp only at sameValues controls meaning
  cases result with
  | Err error => simp [code.read_load,read,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok argument =>
    obtain ⟨checkResult,check,checked⟩ := WP.spec_imp_exists (code.check_memory_and_alignment.spec env argument natural)
    cases checkResult with
    | Err error => simp [code.read_load,read,check,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
    | Ok unit =>
      cases unit
      obtain ⟨⟨popResult,popped⟩,pop,popControls,_,rest,restValues,popEffect⟩ := WP.spec_imp_exists
        (code.pop_with_type.segment middle outer segment .I32 (by simpa [sameValues] using values)
          (by simpa [Control.base,controls] using base))
      dsimp only at popControls restValues popEffect
      cases popResult with
      | Err error => simp [code.read_load,read,check,pop,core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
      | Ok raw =>
        have poly : Control.polymorphic middle = false := by simpa [Control.polymorphic,controls] using monomorphic
        rw [poly] at popEffect
        have old := typed_pop_exact known popEffect
        have room : popped.vals.val.length < Usize.max := by
          simp only [values,old,List.length_append,List.length_singleton] at capacity
          simp only [restValues,List.length_append]
          omega
        obtain ⟨final,push,finalValues,finalControls,finalPos⟩ := WP.spec_imp_exists (code.push_val.spec popped (.Val ty) room)
        simp [code.read_load,read,check,pop,push,bind_ok,core.result.Result.Insts.CoreOpsTry.branch,
          Result.ok.injEq,Prod.mk.injEq,core.result.Result.Ok.injEq] at accepted
        obtain ⟨rfl,rfl⟩ := accepted
        exact ⟨rest,old,by simpa only [restValues] using finalValues,finalControls.trans (popControls.trans controls),check⟩

/-- Accepted stores remove the scalar value and i32 address without disturbing
the remaining current frame segment. -/
theorem reader_memory_store_stack (st out : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (ty : wasm_types.ValueType) (natural : U32) (arg : code.MemArg)
    (outer segment : List code.StackType)
    (values : st.vals.val = outer ++ segment) (base : (Control.base st).val = outer.length)
    (monomorphic : Control.polymorphic st = false) (known : ConcreteStack segment)
    (accepted : code.read_store st data env ty natural = .ok (.Ok arg,out)) :
    ∃ rest, segment = rest ++ [.Val .I32,.Val ty] ∧ out.vals.val = outer ++ rest ∧
      out.ctrls = st.ctrls ∧ code.check_memory_and_alignment env arg natural = .ok (.Ok ()) := by
  obtain ⟨⟨result,middle⟩,read,sameValues,controls,meaning⟩ := WP.spec_imp_exists (code.read_memarg.spec st data)
  dsimp only at sameValues controls meaning
  cases result with
  | Err error => simp [code.read_store,read,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok argument =>
    obtain ⟨checkResult,check,checked⟩ := WP.spec_imp_exists (code.check_memory_and_alignment.spec env argument natural)
    cases checkResult with
    | Err error => simp [code.read_store,read,check,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
    | Ok unit =>
      cases unit
      obtain ⟨⟨popResult,popped⟩,pop,popControls,_,remaining,remainingValues,popEffect⟩ := WP.spec_imp_exists
        (code.pop_with_type.segment middle outer segment ty (by simpa [sameValues] using values)
          (by simpa [Control.base,controls] using base))
      dsimp only at popControls remainingValues popEffect
      cases popResult with
      | Err error => simp [code.read_store,read,check,pop,core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
      | Ok raw =>
        have poly : Control.polymorphic middle = false := by simpa [Control.polymorphic,controls] using monomorphic
        rw [poly] at popEffect
        have old := typed_pop_exact known popEffect
        have remainingKnown : ConcreteStack remaining := (concrete_stack_append.mp (old ▸ known)).1
        obtain ⟨⟨addressResult,final⟩,addressPop,addressControls,_,rest,restValues,addressEffect⟩ := WP.spec_imp_exists
          (code.pop_with_type.segment popped outer remaining .I32 remainingValues
            (by simpa [Control.base,popControls,controls] using base))
        dsimp only at addressControls restValues addressEffect
        cases addressResult with
        | Err error => simp [code.read_store,read,check,pop,addressPop,core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
        | Ok address =>
          have addressPoly : Control.polymorphic popped = false := by simpa [Control.polymorphic,popControls] using poly
          rw [addressPoly] at addressEffect
          have remainingShape := typed_pop_exact remainingKnown addressEffect
          simp [code.read_store,read,check,pop,addressPop,bind_ok,core.result.Result.Insts.CoreOpsTry.branch,
            Result.ok.injEq,Prod.mk.injEq,core.result.Result.Ok.injEq] at accepted
          obtain ⟨rfl,rfl⟩ := accepted
          exact ⟨rest,by simpa only [remainingShape,List.append_assoc,List.cons_append,List.nil_append] using old,
            restValues,addressControls.trans (popControls.trans controls),check⟩
end Itasca.Runtime.Compiler

end

/-! ## Instructions -/

section

/-!
Accepted scalar-memory instructions and decoded opcode facts, used by safety, emission and acceptance.
-/

/-! ## Reader Memory -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- The actual memory reader selected by the independently defined binary row. -/
def memoryReader (operation : MemoryMeaning.Operation) (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) :=
  if operation.store then code.read_store st data env operation.ty operation.naturalAlign
  else code.read_load st data env operation.ty operation.naturalAlign

theorem reader_memory_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState) (opcode : U8) (operation : MemoryMeaning.Operation)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (meaning : MemoryMeaning.opcodeMeaning opcode = some operation)
    (accepted : code.step visitor st.core data env ⟨locals,p.ft.results⟩ opcode before = .ok (.Ok (),out,after)) :
    ∃ arg values, code.visit_memory visitor before out opcode arg = .ok (.Ok (),after) ∧
      memoryReader operation st.core data env = .ok (.Ok arg,out) ∧
      Wasm2.ReaderPost p out (operation.op arg) p.current.ctrl.polymorphic_base values := by
  rw [code.step_memory.dispatch visitor st.core data env ⟨locals,p.ft.results⟩ before opcode operation meaning] at accepted
  obtain ⟨arg,read,callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ accepted
  obtain ⟨C,outer,spine,header,base,typed,ctrls,blocks,vals⟩ := p.opened
  have poly : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by simp [Control.polymorphic,ctrls]
  have envMatches : EnvTranslation.Matches env ⟨locals,p.ft.results⟩ (Wasm2.Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (EnvTranslation.Matches.root env ⟨locals,p.ft.results⟩)).enter _
  have baseEq : (Control.base st.core).val = outer.length := by simpa [Control.base,ctrls] using base
  have effect : memoryReader operation st.core data env ⦃
      Wasm2.Scalar.MemoryPost ((p.current.form.params p.current.ins).map Translate.valueType) data st.core outer p.current.vals
        (Wasm2.Frames.enter C p.current.form p.current.ins p.current.outs) p.current.ops operation.op ⦄ := by
    cases hs : operation.store with
    | false =>
      simp only [memoryReader,hs,Bool.false_eq_true,↓reduceIte]
      exact code.read_load.wasm2_prefix st.core data env ⟨locals,p.ft.results⟩ outer p.current.vals vals baseEq
        capacity _ envMatches p.current.ops (by simpa [poly] using typed) opcode operation meaning hs
    | true =>
      simp only [memoryReader,hs,↓reduceIte]
      exact code.read_store.wasm2_prefix st.core data env ⟨locals,p.ft.results⟩ outer p.current.vals vals baseEq
        _ envMatches p.current.ops (by simpa [poly] using typed) opcode operation meaning hs
  change memoryReader operation st.core data env = .ok (.Ok arg,out) at read
  rw [read,WP.spec_ok] at effect
  obtain ⟨values, post⟩ := p.memory_reader_post C outer spine header base ctrls blocks
    opcode operation byte meaning arg out effect
  exact ⟨arg, values, callback, read, post⟩

end Itasca.Runtime.Compiler

end

/-! ## Memory Reader Facts -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

def memoryRawType : numtype → wasm_types.ValueType
  | .I32 => .I32 | .I64 => .I64 | .F32 => .F32 | .F64 => .F64

def memoryNatural : numtype → U32
  | .I32 | .F32 => 2#u32 | .I64 | .F64 => 3#u32

def memoryPackedNatural {ty} : SourceMachine.Memory.PackedWidth ty → U32
  | .byte => 0#u32 | .half => 1#u32 | .word => 2#u32

def memoryLoadMeaning : SourceMachine.Memory.Load → MemoryMeaning.Operation
  | .full ty => MemoryMeaning.fullLoad (memoryRawType ty) ty (memoryNatural ty)
  | .packed ty width sign => MemoryMeaning.packedLoad (memoryRawType (numtype_Inn ty)) ty width.bits sign (memoryPackedNatural width)

def memoryStoreMeaning : SourceMachine.Memory.Store → MemoryMeaning.Operation
  | .full ty => MemoryMeaning.fullStore (memoryRawType ty) ty (memoryNatural ty)
  | .packed ty width => MemoryMeaning.packedStore (memoryRawType (numtype_Inn ty)) ty width.bits (memoryPackedNatural width)

@[simp] theorem memory_raw_type_translate (ty : numtype) : Translate.valueType (memoryRawType ty) = valtype_numtype ty := by cases ty <;> rfl

 theorem memory_load_reader_facts {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : code.OpIterState)
    (op : SourceMachine.Memory.Load) (arg : code.MemArg) :
    MemoryMeaning.opcodeMeaning (UScalar.cast .U8 (memoryLoadOpcode op)) = some (memoryLoadMeaning op) ∧
    (memoryLoadMeaning op).store = false ∧
    (memoryLoadMeaning op).ty = memoryRawType op.type ∧
    (memoryLoadMeaning op).op arg = op.source (MemoryMeaning.memArg arg) ∧
    code.visit_memory (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler state (UScalar.cast .U8 (memoryLoadOpcode op)) arg =
      runtime.compiler.lower.FunctionCompiler.op ops compiler state (memoryLoadOpcode op) arg.offset arg.align 0#u128 ∧
    (UScalar.cast .U8 (memoryLoadOpcode op)).val ∉ Wasm2.controlOpcodes ∧
    (UScalar.cast .U8 (memoryLoadOpcode op)).val ∉ [28,37,38,208,209,210,252,253] ∧
    Wasm2.NumericExtensions.signMeaning (UScalar.cast .U8 (memoryLoadOpcode op)) = none ∧
    UScalar.cast .U8 (memoryLoadOpcode op) ≠ code.OP_MISC_PREFIX := by
  cases op with
  | full ty => cases ty <;> refine ⟨rfl,rfl,rfl,rfl,rfl,by decide,by decide,rfl,?_⟩ <;> simp only [global_simps] <;> decide
  | packed ty width sign => cases ty <;> cases width <;> cases sign <;>
      refine ⟨rfl,rfl,rfl,rfl,rfl,by decide,by decide,rfl,?_⟩ <;> simp only [global_simps] <;> decide

 theorem memory_store_reader_facts {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : code.OpIterState)
    (op : SourceMachine.Memory.Store) (arg : code.MemArg) :
    MemoryMeaning.opcodeMeaning (UScalar.cast .U8 (memoryStoreOpcode op)) = some (memoryStoreMeaning op) ∧
    (memoryStoreMeaning op).store = true ∧
    (memoryStoreMeaning op).ty = memoryRawType op.type ∧
    (memoryStoreMeaning op).op arg = op.source (MemoryMeaning.memArg arg) ∧
    code.visit_memory (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler state (UScalar.cast .U8 (memoryStoreOpcode op)) arg =
      runtime.compiler.lower.FunctionCompiler.op ops compiler state (memoryStoreOpcode op) arg.offset arg.align 0#u128 ∧
    (UScalar.cast .U8 (memoryStoreOpcode op)).val ∉ Wasm2.controlOpcodes ∧
    (UScalar.cast .U8 (memoryStoreOpcode op)).val ∉ [28,37,38,208,209,210,252,253] ∧
    Wasm2.NumericExtensions.signMeaning (UScalar.cast .U8 (memoryStoreOpcode op)) = none ∧
    UScalar.cast .U8 (memoryStoreOpcode op) ≠ code.OP_MISC_PREFIX := by
  cases op with
  | full ty => cases ty <;> refine ⟨rfl,rfl,rfl,rfl,rfl,by decide,by decide,rfl,?_⟩ <;> simp only [global_simps] <;> decide
  | packed ty width => cases ty <;> cases width <;>
      refine ⟨rfl,rfl,rfl,rfl,rfl,by decide,by decide,rfl,?_⟩ <;> simp only [global_simps] <;> decide
end Itasca.Runtime.Compiler

end

end

/-! ## MemoryTypes -/

section

/-!
Scalar memory operand-stack types and reader availability.

Main declarations: `memory_load_stack_types` and `memory_reader_available`. A direct consumer is `Compiler.Body.Reader.Memory.Acceptance`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem memory_load_stack_types {old next outer segment rest : List code.StackType} {ty : wasm_types.ValueType}
    (known : ConcreteStack old) (oldEq : old = outer ++ segment)
    (shape : segment = rest ++ [.Val .I32]) (nextEq : next = outer ++ rest ++ [.Val ty]) :
    ∃ (front : List valtype) (types : List Itasca.wasm_types.ValueType), Sequence.stackTypes old = front ++ [.I32] ∧
      next = types.map code.StackType.Val ∧ types.map Translate.valueType = front ++ [Translate.valueType ty] := by
  have oldShape : old = (outer ++ rest) ++ [.Val .I32] := by simp [oldEq,shape,List.append_assoc]
  have prefixKnown : ConcreteStack (outer ++ rest) := (concrete_stack_append.mp (oldShape ▸ known)).1
  obtain ⟨types,typesEq⟩ := (concrete_stack_iff _).mp prefixKnown
  refine ⟨types.map Translate.valueType,types ++ [ty],?_,?_,by simp⟩
  · simp [oldShape,typesEq,Sequence.stackTypes,List.map_map,Function.comp_def,Translate.valueType]
  · simpa [List.map_append] using nextEq.trans (by rw [typesEq])

theorem memory_store_stack_types {old next outer segment rest : List code.StackType} {ty : wasm_types.ValueType}
    (known : ConcreteStack old) (oldEq : old = outer ++ segment)
    (shape : segment = rest ++ [.Val .I32,.Val ty]) (nextEq : next = outer ++ rest) :
    ∃ (front : List valtype) (types : List Itasca.wasm_types.ValueType), Sequence.stackTypes old = front ++ [.I32,Translate.valueType ty] ∧
      next = types.map code.StackType.Val ∧ types.map Translate.valueType = front := by
  have oldShape : old = (outer ++ rest) ++ [.Val .I32,.Val ty] := by simp [oldEq,shape,List.append_assoc]
  have prefixKnown : ConcreteStack (outer ++ rest) := (concrete_stack_append.mp (oldShape ▸ known)).1
  obtain ⟨types,typesEq⟩ := (concrete_stack_iff _).mp prefixKnown
  refine ⟨types.map Translate.valueType,types,?_,nextEq.trans typesEq,rfl⟩
  simp [oldShape,typesEq,Sequence.stackTypes,List.map_map,Function.comp_def,Translate.valueType]

theorem memory_reader_available (env : metadata.Env) (arg : code.MemArg) (natural : U32)
    (C : context) (memories : C.MEMS = env.mem_types.val.map EnvTranslation.memType)
    (accepted : code.check_memory_and_alignment env arg natural = .ok (.Ok ())) :
    ∃ memory, C.MEMS[0]? = some memory := by
  have effect := code.check_memory_and_alignment.spec env arg natural
  rw [accepted,WP.spec_ok] at effect
  have bound : 0 < C.MEMS.length := by simpa [memories] using effect.1
  exact ⟨C.MEMS[0],List.getElem?_eq_getElem bound⟩
end Itasca.Runtime.Compiler

end

/-! ## MemoryEmissions -/

section

/-!
Scalar memory load/store emission from accepted reader steps.

Main declarations: `reader_emit_memory_load_wasm2` and `reader_emit_memory_store_wasm2`. A direct consumer is `Compiler.Body.Reader.Checking.CoreInstructionPrefix`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem reader_emit_memory_load_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (op : SourceMachine.Memory.Load) (C : context)
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
      st data env ctx index (UScalar.cast .U8 (memoryLoadOpcode op)) before = .ok (.Ok (),out,after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧ after.next_source = out.core.pos ∧
    ∃ arg front values, Sequence.stackTypes st.core.vals.val = front ++ [.I32] ∧
      Wasm2.ReaderPost p out.core (op.source (MemoryMeaning.memArg arg)) p.current.ctrl.polymorphic_base values ∧
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
  have currentKnown : ConcreteStack p.current.vals := (concrete_stack_append.mp (vals ▸ known)).2
  have poly : Control.polymorphic st.core = false := by simpa [Control.polymorphic,ctrls] using monomorphic
  have baseEq : (Control.base st.core).val = outer.length := by simpa [Control.base,ctrls] using base
  obtain ⟨rest,shape,stack,controls,checked⟩ := reader_memory_load_stack st.core out.core data env _ _ arg outer p.current.vals
    vals baseEq poly currentKnown capacity read
  obtain ⟨front,types,oldTypes,concrete,newTypes⟩ := memory_load_stack_types known vals shape stack
  simp only [memory_raw_type_translate] at oldTypes newTypes
  rw [oldTypes] at layout
  obtain ⟨memory,available⟩ := memory_reader_available env arg _ C contextMemories checked
  have lowered := compiler_memory_load_emission ops law before out.core types front op arg.offset arg.align
    C memory (MemoryMeaning.memArg arg) contextLocalsCode available rfl layout reachable concrete newTypes
    codeFits sourceFits coordinateFits
  rw [callback,WP.spec_ok] at lowered
  obtain ⟨emitted,lower,emission⟩ := lowered rfl
  exact ⟨arg,front,values,oldTypes,post,emitted,⟨lower,SourceStack.of_map types concrete newTypes⟩,emission⟩

theorem reader_emit_memory_store_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (op : SourceMachine.Memory.Store) (C : context)
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
      st data env ctx index (UScalar.cast .U8 (memoryStoreOpcode op)) before = .ok (.Ok (),out,after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧ after.next_source = out.core.pos ∧
    ∃ arg front values, Sequence.stackTypes st.core.vals.val = front ++ [.I32,valtype_numtype op.type] ∧
      Wasm2.ReaderPost p out.core (op.source (MemoryMeaning.memArg arg)) p.current.ctrl.polymorphic_base values ∧
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
  have currentKnown : ConcreteStack p.current.vals := (concrete_stack_append.mp (vals ▸ known)).2
  have poly : Control.polymorphic st.core = false := by simpa [Control.polymorphic,ctrls] using monomorphic
  have baseEq : (Control.base st.core).val = outer.length := by simpa [Control.base,ctrls] using base
  obtain ⟨rest,shape,stack,controls,checked⟩ := reader_memory_store_stack st.core out.core data env _ _ arg outer p.current.vals
    vals baseEq poly currentKnown read
  obtain ⟨front,types,oldTypes,concrete,newTypes⟩ := memory_store_stack_types known vals shape stack
  simp only [memory_raw_type_translate] at oldTypes newTypes
  rw [oldTypes] at layout
  obtain ⟨memory,available⟩ := memory_reader_available env arg _ C contextMemories checked
  have lowered := compiler_memory_store_emission ops law before out.core types front op arg.offset arg.align
    C memory (MemoryMeaning.memArg arg) contextLocalsCode available rfl layout reachable concrete newTypes
    codeFits sourceFits coordinateFits
  rw [callback,WP.spec_ok] at lowered
  obtain ⟨emitted,lower,emission⟩ := lowered rfl
  exact ⟨arg,front,values,oldTypes,post,emitted,⟨lower,SourceStack.of_map types concrete newTypes⟩,emission⟩
end Itasca.Runtime.Compiler

end
