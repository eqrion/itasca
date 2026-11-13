import Itasca.Runtime.Compiler.Body.Reader.Replay.BulkAndSaturatingAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Stacks.Values
import Itasca.Runtime.Compiler.Local.Capacity.UnreachableAvailability
import Itasca.Runtime.Compiler.Body.Reader.Scalar.Unreachable
import Itasca.Visitor.ReaderAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Replay.IndexedPreserved
import Itasca.Visitor.BodyReplay
import Itasca.Runtime.Compiler.Local.Demand.IndependentBodyDemand
import Itasca.Runtime.Compiler.Body.Reader.Float.FloatConstantEmissions
import Itasca.Visitor.EventDispatch
import Itasca.Runtime.Compiler.Local.Source.SourceStacks
import Itasca.Visitor.Erasure

/-!
Sections, each formerly its own module: ProfileAcceptance, SourceBoundNumericExtensionAcceptance, ReachedNumericAcceptance, ReachedReferenceDemand.
-/

/-! ## ProfileAcceptance -/

section

/-!
Lift available Wasm 2 scalar dispatch through its actual profile capacity guard, including extension and SIMD dispatch.

Main declarations: `profile_scalar_available_wasm2` and `profile_base_available_wasm2`. A direct consumer is `Compiler.Body.Reader.Acceptance.ReachedNumericAcceptance`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Lift available Wasm 2 scalar dispatch through its actual profile capacity
guard, including extension and SIMD dispatch. -/
theorem profile_scalar_available_wasm2 {V : Type} (visitor : code.OpVisitor V)
    (st : code.BodyState) (out : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (opcode : U8) (before : V) (post : V → Prop)
    (capacity : st.core.vals.val.length < Usize.max)
    (ordinary : opcode.val ∉ Wasm2.controlOpcodes)
    (accepted : code.step_wasm2 visitor st.core data env ctx opcode before ⦃ result =>
      result.1 = .Ok () ∧ result.2.1 = out ∧ post result.2.2 ⦄) :
    code.step_profile visitor st data env ctx index opcode before ⦃ result =>
      result.1 = .Ok () ∧ result.2.1 = {core := out} ∧ post result.2.2 ⦄ := by
  rw [profile_scalar_eq visitor st data env ctx index opcode before ordinary]
  have notFull : alloc.vec.Vec.len st.core.vals ≠ core.num.Usize.MAX := by
    intro full
    have same := congrArg UScalar.val full
    change st.core.vals.val.length = Usize.max at same
    omega
  rw [if_neg notFull]
  obtain ⟨⟨reply,state,after⟩,called,ok,same,held⟩ := WP.spec_imp_exists accepted
  dsimp only at ok same held
  subst reply state
  rw [called]
  simpa [core.result.Result.Insts.CoreOpsTry.branch] using held

/-- Acceptance of the actual scalar reader lifts through the Wasm 2 profile
capacity guard and source-context adapter. Only the locals are consulted by
ordinary base instructions. -/
theorem profile_base_available_wasm2 {V : Type} (visitor : code.OpVisitor V)
    (st : code.BodyState) (out : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (ctx sourceCtx : code.Context) (index : U32) (opcode : U8) (before : V) (post : V → Prop)
    (capacity : st.core.vals.val.length < Usize.max)
    (ordinary : opcode.val ∉ Wasm2.controlOpcodes)
    (base : opcode.val ∉ [28,37,38,208,209,210,252,253])
    (sign : Wasm2.NumericExtensions.signMeaning opcode = none)
    (misc : opcode ≠ code.OP_MISC_PREFIX) (locals : ctx.locals = sourceCtx.locals)
    (accepted : code.step visitor st.core data env sourceCtx opcode before ⦃ result =>
      result.1 = .Ok () ∧ result.2.1 = out ∧ post result.2.2 ⦄) :
    code.step_profile visitor st data env ctx index opcode before ⦃ result =>
      result.1 = .Ok () ∧ result.2.1 = {core := out} ∧ post result.2.2 ⦄ := by
  rw [profile_scalar_eq visitor st data env ctx index opcode before ordinary]
  have notFull : alloc.vec.Vec.len st.core.vals ≠ core.num.Usize.MAX := by
    intro full
    have same := congrArg UScalar.val full
    change st.core.vals.val.length = Usize.max at same
    omega
  rw [if_neg notFull,code.step_wasm2.base _ _ _ _ _ _ _ base,
    code.step_extended.base _ _ _ _ _ _ _ sign misc,
    Wasm2.scalar_context _ _ _ _ ctx sourceCtx _ _ ordinary locals]
  obtain ⟨⟨reply,state,after⟩,called,ok,same,held⟩ := WP.spec_imp_exists accepted
  dsimp only at ok same held
  subst reply state
  rw [called]
  simpa [core.result.Result.Insts.CoreOpsTry.branch] using held

end Itasca.Runtime.Compiler

end

/-! ## SourceBoundNumericExtensionAcceptance -/

section

/-!
Sign-extension and saturating reader replay from source-only bounds. Numeric postconditions and reached-step availability establish the final indexed replay theorem.
-/

/-! ## Numeric Post Acceptance -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- A source numeric effect and exact reader post supply the live operand
layout before the numeric callback runs, including extension opcodes. -/
theorem _root_.Itasca.Wasm2.ReaderPost.numeric_available {data env locals index st out instruction values}
    {p : Wasm2.Pending data env locals index st}
    (post : Wasm2.ReaderPost p out instruction p.current.ctrl.polymorphic_base values)
    {input : List wasm_types.ValueType} {output : wasm_types.ValueType}
    (effect : StackSemantics.NumericEffect p.current.ctrl.polymorphic_base p.current.vals input output values)
    {A : Type} (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (demand : CallbackDemand compiler out bound)
    (op : SourceMachine.Numeric.Instruction)
    (inputs : input.map Translate.valueType = List.replicate op.arity (integerType op.input))
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.core.vals.val)) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler out (integerOpcode op) 0#u32 0#u32 0#u128 ⦃ result =>
      result.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget result.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · rw [monomorphic live] at effect
    obtain ⟨old,new⟩ := post.values
    obtain ⟨front,_,oldTypes,_⟩ := numeric_full_stack_types (known live) old new effect
    rw [inputs] at oldTypes
    have layout := wholeLayout live
    rw [oldTypes] at layout
    exact compiler_numeric_available_effect ops bound available compiler out demand front op (fun _ => layout)
  · exact compiler_numeric_available_effect ops bound available compiler out demand [] op
      (fun impossible => False.elim (live impossible))

/-- A source numeric effect and exact reader post supply the live operand
layout before the float callback runs, including extension opcodes. -/
theorem _root_.Itasca.Wasm2.ReaderPost.float_available {data env locals index st out instruction values}
    {p : Wasm2.Pending data env locals index st}
    (post : Wasm2.ReaderPost p out instruction p.current.ctrl.polymorphic_base values)
    {input : List wasm_types.ValueType} {output : wasm_types.ValueType}
    (effect : StackSemantics.NumericEffect p.current.ctrl.polymorphic_base p.current.vals input output values)
    {A : Type} (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (demand : CallbackDemand compiler out bound)
    (op : SourceMachine.Float.Instruction)
    (inputs : input.map Translate.valueType = List.replicate op.arity (valtype_numtype op.input))
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.core.vals.val)) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler out (floatOpcode op) 0#u32 0#u32 0#u128 ⦃ result =>
      result.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget result.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · rw [monomorphic live] at effect
    obtain ⟨old,new⟩ := post.values
    obtain ⟨front,_,oldTypes,_⟩ := numeric_full_stack_types (known live) old new effect
    rw [inputs] at oldTypes
    have layout := wholeLayout live
    rw [oldTypes] at layout
    exact compiler_float_available_effect ops bound available compiler out demand front op (fun _ => layout)
  · exact compiler_float_available_effect ops bound available compiler out demand [] op
      (fun impossible => False.elim (live impossible))

end Itasca.Runtime.Compiler

end

/-! ## Reached Numeric Extension Acceptance -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace
set_option maxRecDepth 4096

/-- Every Wasm 2 sign extension accepts from the independently validated
reader effect and source-paid numeric demand. -/
theorem reached_profile_sign_available_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A V : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (op : SourceMachine.Numeric.Instruction) (extension : 192 ≤ (integerOpcode op).val)
    (demand : CallbackDemand compiler out.core bound)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.core.vals.val))
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (integerOpcode op))
    (reference : code.step_profile source st data env ctx index (UScalar.cast .U8 (integerOpcode op)) before =
      .ok (.Ok (),out,after)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index (UScalar.cast .U8 (integerOpcode op)) compiler ⦃ result =>
      result.1 = .Ok () ∧ result.2.1 = out ∧ CompilationBudgetEffect compiler.budget result.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨operation,hook,meaning,_,inputs,_,encoding,hookEq,ordinary,base⟩ :=
    integer_sign_reader_facts ops compiler out.core op extension
  obtain ⟨capacity,run⟩ := profile_scalar_success source st out data env ctx index _ before after ordinary reference
  rw [code.step_wasm2.base _ _ _ _ _ _ _ base] at run
  obtain ⟨_,_,converted,_,_,values,effect,post⟩ := reader_sign_wasm2 p source before after out.core ctx _ operation
    capacity byte meaning run
  have callback : code.visit_sign_extension (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      compiler out.core (UScalar.cast .U8 (integerOpcode op)) ⦃ result => result.1 = .Ok () ∧
        CompilationBudgetEffect compiler.budget result.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
    have dispatch := ExtendedNumericHook.dispatch (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      compiler out.core hook
    rw [encoding] at dispatch
    dsimp only at dispatch
    rw [dispatch,hookEq]
    exact post.numeric_available effect ops bound available compiler demand op inputs known monomorphic wholeLayout
  apply profile_scalar_available_wasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    st out.core data env ctx index _ compiler
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) capacity ordinary
  rw [code.step_wasm2.base _ _ _ _ _ _ _ base,code.step_extended.sign _ _ _ _ _ _ _ _ meaning]
  exact CoreVisitor.run.available_of_read (code.read_conversion st.core operation.input operation.output)
    (fun v state (_ : Unit) => code.visit_sign_extension
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) v state (UScalar.cast .U8 (integerOpcode op)))
    compiler () out.core
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) converted callback

/-- Every saturating conversion accepts through its real prefix decoder and
source-validated conversion reader. Compilation assumes no native FP law. -/
theorem reached_profile_saturating_available_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A V : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (op : SourceMachine.Float.Instruction) (extension : 256 ≤ (floatOpcode op).val)
    (subopcode : U32) (next : Usize) (subopcodeEq : subopcode.val = (floatOpcode op).val-256)
    (decoded : Leb128.Decoded data st.core.pos subopcode next)
    (demand : CallbackDemand compiler out.core bound)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.core.vals.val))
    (byte : data.val[p.start.val]'p.inbounds = 0xfc#u8)
    (reference : code.step_profile source st data env ctx index 0xfc#u8 before = .ok (.Ok (),out,after)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 0xfc#u8 compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨sub,operation,hook,subEq,small,meaning,_,inputs,_,encoding,hookEq⟩ :=
    float_saturating_reader_facts ops compiler out.core op extension
  have same : sub = subopcode := UScalar.eq_of_val_eq (subEq.trans subopcodeEq.symm)
  subst sub
  obtain ⟨capacity,run⟩ := profile_scalar_success source st out data env ctx index 0xfc#u8 before after (by decide) reference
  rw [code.step_wasm2.saturating _ _ _ _ _ _ _ _ decoded small] at run
  obtain ⟨_,_,converted,_,_,values,effect,post⟩ := reader_saturating_wasm2 p source before after out.core ctx subopcode next
    operation capacity byte decoded meaning run
  have callback : code.visit_saturating (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      compiler out.core subopcode ⦃ result => result.1 = .Ok () ∧
        CompilationBudgetEffect compiler.budget result.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
    have dispatch := ExtendedNumericHook.dispatch (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      compiler out.core hook
    rw [encoding] at dispatch
    dsimp only at dispatch
    rw [dispatch,hookEq]
    exact post.float_available effect ops bound available compiler demand op inputs known monomorphic wholeLayout
  apply profile_scalar_available_wasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    st out.core data env ctx index 0xfc#u8 compiler
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) capacity (by decide)
  rw [code.step_wasm2.saturating _ _ _ _ _ _ _ _ decoded small,code.step_extended.prefixed]
  have readLeb := reader.read_u32_leb.complete data st.core.pos subopcode next decoded
  simp only [Wasm2.prefixedStep,readLeb,bind_ok,meaning]
  exact CoreVisitor.run.available_of_read (code.read_conversion {st.core with pos := next} operation.input operation.output)
    (fun v state (_ : Unit) => code.visit_saturating
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) v state subopcode) compiler () out.core
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) converted callback

end Itasca.Runtime.Compiler

end

/-! ## Source Bound Numeric Extension Acceptance -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Independent source sign validation and source-byte room construct
the actual numeric-extension callback demand internally. -/
theorem IndexedTableReaderCompilerPointWasm2.sign_available_from_source {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns localTypes data env sourceLocals index ft st}
    (point : IndexedTableReaderCompilerPointWasm2 emit initial compiler types functions returns localTypes
      data env sourceLocals index ft st)
    (before after final : List Observation) (out : code.BodyState)
    (room : BodyResourceRoom initial data.length (observationDemand final).operands bound)
    (budget : SourceCompilationBudget initial.budget compiler.budget bodyResourceRate st.core.pos.val)
    (nonempty : st.core.ctrls.val ≠ []) (next : Usize)
    (advance : next.val = st.core.pos.val+1) (inbounds : st.core.pos.val<data.length)
    (op : SourceMachine.Numeric.Instruction) (extension : 192 ≤ (integerOpcode op).val)
    (byte : data.val[st.core.pos.val] = UScalar.cast .U8 (integerOpcode op))
    (reference : code.step_profile recorder {core := {st.core with pos := next}} data env
      ⟨sourceLocals,ft.results⟩ index data.val[st.core.pos.val] before = .ok (.Ok (),out,after))
    (suffix : code.body_loop_loop recorder data env ⟨sourceLocals,ft.results⟩ index before st =
      .ok (.Ok (),final)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ⟨sourceLocals,ft.results⟩ index
      data.val[st.core.pos.val] compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let pending := state.boundary.pending next advance inbounds
  have tail := code.body_loop_loop.accepted_tail recorder data env ⟨sourceLocals,ft.results⟩ index st out
    before after final nonempty inbounds next advance reference suffix
  have canonical := reference
  rw [byte] at canonical
  obtain ⟨operation,hook,meaning,_,_,_,encoding,_,ordinary,base⟩ :=
    integer_sign_reader_facts ops compiler out.core op extension
  obtain ⟨capacity,raw⟩ := profile_scalar_success recorder _ out data env ⟨sourceLocals,ft.results⟩ index _ before after
    ordinary canonical
  rw [code.step_wasm2.base _ _ _ _ _ _ _ base] at raw
  obtain ⟨callback,_⟩ := reader_sign_wasm2 pending recorder before after out.core ⟨sourceLocals,ft.results⟩ _ operation
    capacity byte meaning raw
  have dispatch := ExtendedNumericHook.dispatch recorder before out.core hook
  rw [encoding] at dispatch
  dsimp only at dispatch
  rw [dispatch] at callback
  have operands := (source_callback_demand before after final out.core (.extendedNumeric hook) (.Ok ()) out data env
    ⟨sourceLocals,ft.results⟩ index (.Ok ()) callback tail).1
  have demand := room.demand budget state.compiled.metadata state.compiled.codeBudget state.compiled.sources
    state.compiled.cursor inbounds out.core operands
  rw [byte]
  exact reached_profile_sign_available_wasm2 pending ops bound allocation recorder before after compiler out
    ⟨sourceLocals,ft.results⟩ op extension demand state.compiled.known state.reach.current
    (fun live => (state.compiled.live live).2.layout) byte canonical

/-- Independent source saturating validation and source-byte room construct
the actual numeric-extension callback demand internally. -/
theorem IndexedTableReaderCompilerPointWasm2.saturating_available_from_source {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns localTypes data env sourceLocals index ft st}
    (point : IndexedTableReaderCompilerPointWasm2 emit initial compiler types functions returns localTypes
      data env sourceLocals index ft st)
    (before after final : List Observation) (out : code.BodyState)
    (room : BodyResourceRoom initial data.length (observationDemand final).operands bound)
    (budget : SourceCompilationBudget initial.budget compiler.budget bodyResourceRate st.core.pos.val)
    (nonempty : st.core.ctrls.val ≠ []) (next : Usize)
    (advance : next.val = st.core.pos.val+1) (inbounds : st.core.pos.val<data.length)
    (op : SourceMachine.Float.Instruction) (extension : 256 ≤ (floatOpcode op).val)
    (subopcode : U32) (prefixEnd : Usize) (subopcodeEq : subopcode.val = (floatOpcode op).val-256)
    (decoded : Leb128.Decoded data next subopcode prefixEnd)
    (byte : data.val[st.core.pos.val] = 252#u8)
    (reference : code.step_profile recorder {core := {st.core with pos := next}} data env
      ⟨sourceLocals,ft.results⟩ index data.val[st.core.pos.val] before = .ok (.Ok (),out,after))
    (suffix : code.body_loop_loop recorder data env ⟨sourceLocals,ft.results⟩ index before st =
      .ok (.Ok (),final)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ⟨sourceLocals,ft.results⟩ index
      data.val[st.core.pos.val] compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let pending := state.boundary.pending next advance inbounds
  have tail := code.body_loop_loop.accepted_tail recorder data env ⟨sourceLocals,ft.results⟩ index st out
    before after final nonempty inbounds next advance reference suffix
  have canonical := reference
  rw [byte] at canonical
  obtain ⟨sub,operation,hook,subEq,small,meaning,_,_,_,encoding,_⟩ :=
    float_saturating_reader_facts ops compiler out.core op extension
  have same : sub = subopcode := UScalar.eq_of_val_eq (subEq.trans subopcodeEq.symm)
  subst sub
  obtain ⟨capacity,raw⟩ := profile_scalar_success recorder _ out data env ⟨sourceLocals,ft.results⟩ index 252#u8 before after
    (by decide) canonical
  rw [code.step_wasm2.saturating _ _ _ _ _ _ _ _ decoded small] at raw
  obtain ⟨callback,_⟩ := reader_saturating_wasm2 pending recorder before after out.core ⟨sourceLocals,ft.results⟩
    subopcode prefixEnd operation capacity byte decoded meaning raw
  have dispatch := ExtendedNumericHook.dispatch recorder before out.core hook
  rw [encoding] at dispatch
  dsimp only at dispatch
  rw [dispatch] at callback
  have operands := (source_callback_demand before after final out.core (.extendedNumeric hook) (.Ok ()) out data env
    ⟨sourceLocals,ft.results⟩ index (.Ok ()) callback tail).1
  have demand := room.demand budget state.compiled.metadata state.compiled.codeBudget state.compiled.sources
    state.compiled.cursor inbounds out.core operands
  rw [byte]
  exact reached_profile_saturating_available_wasm2 pending ops bound allocation recorder before after compiler out
    ⟨sourceLocals,ft.results⟩ op extension subopcode prefixEnd subopcodeEq decoded demand state.compiled.known state.reach.current
    (fun live => (state.compiled.live live).2.layout) byte canonical

end Itasca.Runtime.Compiler

end

end

/-! ## ReachedNumericAcceptance -/

section

/-!
Successful integer and floating-point reader replay at a reached source point. Local callback availability lifts to both accepted-reader and profile-filtered results.
-/

/-! ## Reader Numeric Acceptance -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace
set_option maxRecDepth 4096

/-- Replaying an independently accepted base numeric instruction retains the
reader's exact source state and pays at most one instruction charge. -/
theorem compiler_reader_numeric_available {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st final : code.OpIterState)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (demand : CallbackDemand compiler final bound) (front : List valtype)
    (op : SourceMachine.Numeric.Instruction) (base : (integerOpcode op).val < 192)
    (layout : compiler.reachable = true →
      CompilerLayout compiler (front ++ List.replicate op.arity (integerType op.input)))
    (reference : code.step source st data env ctx (UScalar.cast .U8 (integerOpcode op)) before =
      .ok (.Ok (),final,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (integerOpcode op)) compiler ⦃ out =>
      out.1 = .Ok () ∧ out.2.1 = final ∧ CompilationBudgetEffect compiler.budget out.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨operation,hook,meaning,handler,rest⟩ := integer_reader_facts ops compiler st op base
  rw [dispatch_numeric _ st data env ctx before _ operation hook meaning handler] at reference
  rw [dispatch_numeric _ st data env ctx compiler _ operation hook meaning handler]
  refine CoreVisitor.run.accepted_lift_on (Numeric.read operation st)
    (fun v s (_ : Unit) => invoke source v (.op s (.numeric hook)))
    (fun v s (_ : Unit) => invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      v (.op s (.numeric hook))) before after compiler final
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) reference ?_
  intro value _ _
  obtain ⟨operation',hook',meaning',handler',_,_,_,callback,_⟩ := integer_reader_facts ops compiler final op base
  have same : hook' = hook := Option.some.inj (handler'.symm.trans handler)
  subst hook'
  rw [callback]
  exact compiler_numeric_available_effect ops bound available compiler final demand front op layout

/-- Replaying an independently accepted base float instruction retains the
reader's exact source state and pays at most one instruction charge. -/
theorem compiler_reader_float_available {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st final : code.OpIterState)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (demand : CallbackDemand compiler final bound) (front : List valtype)
    (op : SourceMachine.Float.Instruction) (base : (floatOpcode op).val < 256)
    (layout : compiler.reachable = true →
      CompilerLayout compiler (front ++ List.replicate op.arity (valtype_numtype op.input)))
    (reference : code.step source st data env ctx (UScalar.cast .U8 (floatOpcode op)) before =
      .ok (.Ok (),final,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (floatOpcode op)) compiler ⦃ out =>
      out.1 = .Ok () ∧ out.2.1 = final ∧ CompilationBudgetEffect compiler.budget out.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨operation,hook,meaning,handler,rest⟩ := float_reader_facts ops compiler st op base
  rw [dispatch_numeric _ st data env ctx before _ operation hook meaning handler] at reference
  rw [dispatch_numeric _ st data env ctx compiler _ operation hook meaning handler]
  refine CoreVisitor.run.accepted_lift_on (Numeric.read operation st)
    (fun v s (_ : Unit) => invoke source v (.op s (.numeric hook)))
    (fun v s (_ : Unit) => invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      v (.op s (.numeric hook))) before after compiler final
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) reference ?_
  intro value _ _
  obtain ⟨operation',hook',meaning',handler',_,_,_,callback,_⟩ := float_reader_facts ops compiler final op base
  have same : hook' = hook := Option.some.inj (handler'.symm.trans handler)
  subst hook'
  rw [callback]
  exact compiler_float_available_effect ops bound available compiler final demand front op layout

end Itasca.Runtime.Compiler

end

/-! ## Reached Numeric Acceptance -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace
set_option maxRecDepth 4096

/-- The independently accepted Wasm 2 reader supplies the live operand
layout needed by numeric lowering. No accepted compiler callback is assumed. -/
theorem reached_reader_numeric_available_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (demand : CallbackDemand compiler out bound)
    (op : SourceMachine.Numeric.Instruction) (base : (integerOpcode op).val < 192)
    (capacity : st.core.vals.val.length < Usize.max)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.core.vals.val))
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (integerOpcode op))
    (reference : code.step source st.core data env ⟨locals,p.ft.results⟩ (UScalar.cast .U8 (integerOpcode op)) before =
      .ok (.Ok (),out,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st.core data env ⟨locals,p.ft.results⟩ (UScalar.cast .U8 (integerOpcode op)) compiler ⦃ result =>
      result.1 = .Ok () ∧ result.2.1 = out ∧ CompilationBudgetEffect compiler.budget result.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · obtain ⟨operation,hook,meaning,handler,_,inputs,_⟩ := integer_reader_facts ops compiler out op base
    obtain ⟨_,_,_,_,values,effect,post⟩ := reader_numeric_wasm2 p source before after out _ operation hook
      capacity byte meaning handler reference
    rw [monomorphic live] at effect
    obtain ⟨old,new⟩ := post.values
    obtain ⟨front,_,oldTypes,_⟩ := numeric_full_stack_types (known live) old new effect
    rw [inputs] at oldTypes
    have layout := wholeLayout live
    rw [oldTypes] at layout
    exact compiler_reader_numeric_available ops bound available source before after compiler st.core out data env
      ⟨locals,p.ft.results⟩ demand front op base (fun _ => layout) reference
  · exact compiler_reader_numeric_available ops bound available source before after compiler st.core out data env
      ⟨locals,p.ft.results⟩ demand [] op base (fun impossible => False.elim (live impossible)) reference

/-- The independently accepted Wasm 2 reader supplies the live operand
layout needed by float lowering. No accepted compiler callback is assumed. -/
theorem reached_reader_float_available_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (demand : CallbackDemand compiler out bound)
    (op : SourceMachine.Float.Instruction) (base : (floatOpcode op).val < 256)
    (capacity : st.core.vals.val.length < Usize.max)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.core.vals.val))
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (floatOpcode op))
    (reference : code.step source st.core data env ⟨locals,p.ft.results⟩ (UScalar.cast .U8 (floatOpcode op)) before =
      .ok (.Ok (),out,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st.core data env ⟨locals,p.ft.results⟩ (UScalar.cast .U8 (floatOpcode op)) compiler ⦃ result =>
      result.1 = .Ok () ∧ result.2.1 = out ∧ CompilationBudgetEffect compiler.budget result.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · obtain ⟨operation,hook,meaning,handler,_,inputs,_⟩ := float_reader_facts ops compiler out op base
    obtain ⟨_,_,_,_,values,effect,post⟩ := reader_numeric_wasm2 p source before after out _ operation hook
      capacity byte meaning handler reference
    rw [monomorphic live] at effect
    obtain ⟨old,new⟩ := post.values
    obtain ⟨front,_,oldTypes,_⟩ := numeric_full_stack_types (known live) old new effect
    rw [inputs] at oldTypes
    have layout := wholeLayout live
    rw [oldTypes] at layout
    exact compiler_reader_float_available ops bound available source before after compiler st.core out data env
      ⟨locals,p.ft.results⟩ demand front op base (fun _ => layout) reference
  · exact compiler_reader_float_available ops bound available source before after compiler st.core out data env
      ⟨locals,p.ft.results⟩ demand [] op base (fun impossible => False.elim (live impossible)) reference

/-- The complete Wasm 2 profile dispatcher accepts this reached numeric
step, deriving its capacity check from independent reference acceptance. -/
theorem reached_profile_numeric_available_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (demand : CallbackDemand compiler out.core bound)
    (op : SourceMachine.Numeric.Instruction) (base : (integerOpcode op).val < 192)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.core.vals.val))
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (integerOpcode op))
    (reference : code.step_profile source st data env ctx index
      (UScalar.cast .U8 (integerOpcode op)) before = .ok (.Ok (),out,after)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index (UScalar.cast .U8 (integerOpcode op)) compiler ⦃ result =>
      result.1 = .Ok () ∧ result.2.1 = out ∧ CompilationBudgetEffect compiler.budget result.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨_,_,_,_,_,_,_,_,ordinary,plain,sign,misc⟩ := integer_reader_facts ops compiler out.core op base
  obtain ⟨capacity,raw⟩ := profile_base_success_wasm2 source st out data env ctx ⟨locals,p.ft.results⟩
    index _ before after ordinary plain sign misc contextLocals reference
  exact profile_base_available_wasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    st out.core data env ctx ⟨locals,p.ft.results⟩ index _ compiler
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0))
    capacity ordinary plain sign misc contextLocals
    (reached_reader_numeric_available_wasm2 p ops bound available source before after compiler out.core demand
      op base capacity known monomorphic wholeLayout byte raw)

/-- The complete Wasm 2 profile dispatcher accepts this reached float
step, deriving its capacity check from independent reference acceptance. -/
theorem reached_profile_float_available_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (demand : CallbackDemand compiler out.core bound)
    (op : SourceMachine.Float.Instruction) (base : (floatOpcode op).val < 256)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.core.vals.val))
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (floatOpcode op))
    (reference : code.step_profile source st data env ctx index
      (UScalar.cast .U8 (floatOpcode op)) before = .ok (.Ok (),out,after)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index (UScalar.cast .U8 (floatOpcode op)) compiler ⦃ result =>
      result.1 = .Ok () ∧ result.2.1 = out ∧ CompilationBudgetEffect compiler.budget result.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨_,_,_,_,_,_,_,_,ordinary,plain,sign,misc⟩ := float_reader_facts ops compiler out.core op base
  obtain ⟨capacity,raw⟩ := profile_base_success_wasm2 source st out data env ctx ⟨locals,p.ft.results⟩
    index _ before after ordinary plain sign misc contextLocals reference
  exact profile_base_available_wasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    st out.core data env ctx ⟨locals,p.ft.results⟩ index _ compiler
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0))
    capacity ordinary plain sign misc contextLocals
    (reached_reader_float_available_wasm2 p ops bound available source before after compiler out.core demand
      op base capacity known monomorphic wholeLayout byte raw)

end Itasca.Runtime.Compiler

end

end

/-! ## ReachedReferenceDemand -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Construct actual callback demand from the independent reference reader and
its remaining source body. The caller supplies source validity evidence and
numeric room, not a target callback result or accepted compiler trace. -/
theorem reference_reader_demand {A R : Type}
    {initial compiler : runtime.compiler.FunctionCompiler A} {length bound position}
    (final : List Observation)
    (room : BodyResourceRoom initial length (observationDemand final).operands bound)
    (budget : SourceCompilationBudget initial.budget compiler.budget bodyResourceRate position)
    (stable : CompilerStable initial compiler) (codeBudget : SourceCodeBudget compiler position)
    (sources : SourceAligned compiler) (cursor : compiler.next_source.val ≤ position)
    (remaining : position < length)
    (read : Result (core.result.Result R error.OpError × code.OpIterState))
    (action : R → Action) (before after : List Observation) (out : code.BodyState)
    (reference : CoreVisitor.run read (fun log state value => invoke recorder log (.op state (action value))) before =
      .ok (.Ok (),out.core,after))
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
    (tail : code.body_loop_loop recorder data env ctx index after out = .ok (.Ok (),final)) :
    CallbackDemand compiler out.core bound := by
  obtain ⟨value,_,called⟩ := CoreVisitor.run.accepted _ _ _ _ _ reference
  have vectors := source_callback_demand before after final out.core (action value) (.Ok ()) out data env ctx index
    (.Ok ()) called tail
  exact room.demand budget stable codeBudget sources cursor remaining out.core vectors.1

end Itasca.Runtime.Compiler

end
