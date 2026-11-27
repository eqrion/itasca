import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableFrames
import Itasca.Body.Visitor.BrTable
import Itasca.Binary.LebReaders
import Itasca.Binary.Scalar.Encoding
import Itasca.Binary.Scalar.MemoryMeaning
import Itasca.Visitor.BodyReplay
import Itasca.Visitor.RunTrace
import Itasca.Handler.ScalarCompleteness
import Itasca.Runtime.Compiler.Body.Reader.Control.EndCompilation
import Itasca.Body.Control.BranchComplete
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTable
import Itasca.Visitor.Total
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CallbackRetention
import Itasca.Runtime.Compiler.Local.Capacity.ControlCapacity
import Itasca.Runtime.Compiler.Local.Capacity.ControlAvailability
import Itasca.Runtime.Compiler.Local.Lowering.Literal.SourceEffects
import Itasca.Runtime.Compiler.Local.Source.SourceTactics
import Itasca.Runtime.Compiler.Local.Lowering.Integer.Lowering
import Itasca.Runtime.Compiler.Local.Lowering.LoweringLocal
import Itasca.Runtime.Compiler.Body.CapacityTrace
import Itasca.Runtime.Compiler.Local.Callbacks.MetadataPreservation
import Itasca.Runtime.Compiler.Body.Reader.Scalar.ScalarEffects
import Itasca.Runtime.Compiler.Body.Reader.Control.Reachability
import Itasca.Runtime.Compiler.Local.Relations.Syntax.ReaderOpcode
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ScopeEffects
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ScopeFrames
import Itasca.Runtime.Compiler.Local.Relations.Stacks.ConcretePops
import Itasca.Runtime.Compiler.Body.Relations.Entry.EntryLayout
import Itasca.Runtime.Compiler.Body.Reader.Replay.ReaderCompilerState
import Itasca.Runtime.Compiler.Local.Callbacks.Observation.Bounds
import Itasca.Body.LoopDispatch
import Itasca.Body.Trace.BytesDispatch
import Itasca.Body.Trace.ControlRecords

/-!
Proofs for Runtime / Compiler / Body / Reader / Control.

This module collects BranchAndScopeEffects, ControlKind.
Each section documents its contracts and consumers.
-/

/-! ## BranchAndScopeEffects -/

section

/-!
# Branch-table reader effects

Collected labels, targets, source suffixes and operand inputs retain their exact repeated-
reader effects. The final postcondition composes label callbacks with the distinct
terminal branch-table callback.
-/

/-! ## BranchTable -/

section

/-!
br_table reader inversion through label-vector body and loop execution. The final theorem identifies the decoded branch-table source instruction.
-/

/-! ## Reader Table Rest -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Computation Itasca.Body.Visitor

 theorem table_rest_cont {V : Type} (visitor : code.OpVisitor V)
    (st : code.BodyState) (env : metadata.Env) (count index depth : U32)
    (types : signature.ResultType) (arity : Option Usize)
    (before after : V) (next : code.OpIterState) (nextArity : Option Usize)
     (nextIndex : U32)
    (accepted : tableRest visitor st env count index depth types arity before =
      .ok (.cont (next,after,nextArity,nextIndex))) :
    next = st.core ∧ after = before ∧ index ≠ count ∧
      nextIndex.val = index.val + 1 := by
  unfold tableRest at accepted
  obtain ⟨checked,_,rest⟩ := bind_ok_inv _ _ _ accepted
  cases checked with
  | Err error => simp at rest
  | Ok newArity =>
    by_cases final : index = count
    · simp only [final,ite_true] at rest
      obtain ⟨marked,_,rest⟩ := bind_ok_inv _ _ _ rest
      obtain ⟨⟨reply,result⟩,_,rest⟩ := bind_ok_inv _ _ _ rest
      cases reply <;> simp [code.visit] at rest
    · simp only [final,ite_false] at rest
      obtain ⟨incremented,increment,rest⟩ := bind_ok_inv _ _ _ rest
      simp only [Result.ok.injEq,ControlFlow.cont.injEq,Prod.mk.injEq] at rest
      obtain ⟨rfl,rfl,rfl,rfl⟩ := rest
      have arithmetic := UScalar.add_equiv index 1#u32
      rw [increment] at arithmetic
      exact ⟨rfl,rfl,final,by simpa using arithmetic.2.1⟩

theorem table_rest_done {V : Type} (visitor : code.OpVisitor V)
    (st final : code.BodyState) (env : metadata.Env) (count index depth : U32)
    (types : signature.ResultType) (arity : Option Usize)
    (before after : V)
    (accepted : tableRest visitor st env count index depth types arity before =
      .ok (.done (.Ok (),final,after))) :
    index = count ∧
    code.mark_unreachable st.core = .ok final.core ∧
    visitor.on_br_table before final.core depth types = .ok (.Ok (),after) := by
  unfold tableRest at accepted
  obtain ⟨checked,_,rest⟩ := bind_ok_inv _ _ _ accepted
  cases checked with
  | Err error => simp at rest
  | Ok newArity =>
    by_cases isLast : index = count
    · simp only [isLast,ite_true] at rest
      obtain ⟨marked,markedCall,rest⟩ := bind_ok_inv _ _ _ rest
      obtain ⟨⟨reply,result⟩,callback,rest⟩ := bind_ok_inv _ _ _ rest
      cases reply with
      | Err error => simp [code.visit] at rest
      | Ok unit =>
        cases unit
        simp [code.visit] at rest
        rcases rest with ⟨stateEq,visitorEq⟩
        cases final
        simp only [code.BodyState.mk.injEq] at stateEq
        subst after
        cases stateEq
        exact ⟨isLast,markedCall,callback⟩
    · simp only [isLast,ite_false] at rest
      obtain ⟨_,_,rest⟩ := bind_ok_inv _ _ _ rest
      simp at rest
end Itasca.Compiler

end

/-! ## Reader Table Body -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Computation Itasca.Body.Visitor
set_option maxRecDepth 4096

 theorem table_label_bytes (before after : code.BodyState) (data : Slice U8)
    (depth : U32) (types : signature.ResultType)
    (accepted : code.read_label_info before data = .ok (.Ok (depth,types),after)) :
    after.core.vals = before.core.vals ∧ after.core.ctrls = before.core.ctrls ∧
    Binary.Leb128.Decoded data before.core.pos depth after.core.pos := by
  unfold code.read_label_info at accepted
  obtain ⟨read,readCall,readSpec⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data before.core.pos)
  rw [readCall] at accepted
  cases read with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok pair =>
    obtain ⟨decoded,next⟩ := pair
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at accepted
    obtain ⟨label,_,rest⟩ := bind_ok_inv _ _ _ accepted
    cases label with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok ts =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Result.ok.injEq,
        Prod.mk.injEq,core.result.Result.Ok.injEq] at rest
      obtain ⟨⟨rfl,rfl⟩,rfl⟩ := rest
      exact ⟨rfl,rfl,readSpec⟩

theorem compiler_table_body_cont {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st : code.BodyState) (next : code.OpIterState) (data : Slice U8) (env : metadata.Env)
     (count index nextIndex : U32) (arity nextArity : Option Usize)

    (accepted : tableBody (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env count st before arity index =
        .ok (.cont (next,after,nextArity,nextIndex))) :
    ∃ depth budget buffer,
      after = {before with budget,table_depths := buffer} ∧
      buffer.val = before.table_depths.val ++ [depth] ∧
      Binary.Leb128.Decoded data st.core.pos depth next.pos ∧
      next.vals = st.core.vals ∧ next.ctrls = st.core.ctrls ∧
      index ≠ count ∧ nextIndex.val = index.val+1 := by
  unfold tableBody at accepted
  obtain ⟨⟨read,s⟩,readCall,rest⟩ := bind_ok_inv _ _ _ accepted
  cases read with
  | Err error => simp at rest
  | Ok pair =>
    obtain ⟨depth,types⟩ := pair
    have bytes := table_label_bytes st s data depth types readCall
    simp only [uncurry_apply_pair] at rest
    by_cases isLast : index = count
    · simp only [isLast,bne_self_eq_false,Bool.false_eq_true,ite_false] at rest
      exact False.elim ((table_rest_cont _ s env count count depth types arity before after next
        nextArity nextIndex rest).2.2.1 rfl)
    · simp only [bne_iff_ne,if_pos isLast] at rest
      obtain ⟨⟨reply,middle⟩,callback,rest⟩ := bind_ok_inv _ _ _ rest
      cases reply with
      | Err error => simp [code.visit] at rest
      | Ok unit =>
        cases unit
        simp only [code.visit,bind_ok,uncurry_apply_pair] at rest
        obtain ⟨rfl,rfl,_,nextEq⟩ := table_rest_cont _ s env count index depth types arity middle
          after next nextArity nextIndex rest
        obtain ⟨budget,buffer,same,appended⟩ := compiler_table_label_success ops law before _ s.core depth callback
        exact ⟨depth,budget,buffer,same,appended,bytes.2.2,bytes.1,bytes.2.1,isLast,nextEq⟩

theorem compiler_table_body_done {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A)
    (st final : code.BodyState) (data : Slice U8) (env : metadata.Env)
     (count index : U32) (arity : Option Usize)

    (accepted : tableBody (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env count st before arity index = .ok (.done (.Ok (),final,after))) :
    ∃ (depth : U32) (types : signature.ResultType) (readState : code.BodyState),
      index = count ∧
      Binary.Leb128.Decoded data st.core.pos depth readState.core.pos ∧
      code.mark_unreachable readState.core = .ok final.core ∧
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
        ops before final.core depth types = .ok (.Ok (),after) := by
  unfold tableBody at accepted
  obtain ⟨⟨read,s⟩,readCall,rest⟩ := bind_ok_inv _ _ _ accepted
  cases read with
  | Err error => simp at rest
  | Ok pair =>
    obtain ⟨depth,types⟩ := pair
    have bytes := table_label_bytes st s data depth types readCall
    simp only [uncurry_apply_pair] at rest
    by_cases isLast : index = count
    · simp only [isLast,bne_self_eq_false,Bool.false_eq_true,ite_false] at rest
      obtain ⟨_,marked,callback⟩ := table_rest_done _ s final env count count depth types arity
        before after rest
      exact ⟨depth,types,s,isLast,bytes.2.2,marked,callback⟩
    · simp only [bne_iff_ne,if_pos isLast] at rest
      obtain ⟨⟨reply,middle⟩,callback,rest⟩ := bind_ok_inv _ _ _ rest
      cases reply with
      | Err error => simp [code.visit] at rest
      | Ok unit =>
        cases unit
        simp only [code.visit,bind_ok,uncurry_apply_pair] at rest
        exact False.elim (isLast (table_rest_done _ s final env count index depth types arity middle
          after rest).1)
end Itasca.Compiler

end

/-! ## Reader Table Loop -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Computation Itasca.Body.Visitor
set_option maxRecDepth 4096

/-- The accepted target loop collects exactly its decoded nondefault
labels, then invokes the final callback once with the separately decoded default. -/
theorem compiler_table_loop {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st final : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (count index : U32) (arity : Option Usize)
    (indexBound : index.val ≤ count.val)
    (accepted : code.branch_table_with_loop (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st.core data env before count arity index = .ok (.Ok (),final,after)) :
    ∃ (depths : List U32) (default : U32) (types : signature.ResultType)
      (defaultStart : Usize) (readState : code.BodyState) (budget : runtime.compiler.Budget A)
      (buffer : alloc.vec.Vec U32),
      buffer.val = before.table_depths.val ++ depths ∧
      Body.BrTable.LabelsDecoded data st.core.pos depths defaultStart ∧
      Binary.Leb128.Decoded data defaultStart default readState.core.pos ∧
      index.val + depths.length = count.val ∧
      code.mark_unreachable readState.core = .ok final.core ∧
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
        ops {before with budget,table_depths := buffer} final.core default types = .ok (.Ok (),after) := by
  generalize measure : count.val - index.val = n
  induction n using Nat.strong_induction_on generalizing before st index arity with
  | h n ih =>
    unfold code.branch_table_with_loop at accepted
    rw [loop] at accepted
    simp only [table_body_eq (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env count st before arity index] at accepted
    obtain ⟨flow,bodyCall,tail⟩ := bind_ok_inv _ _ _ accepted
    cases flow with
    | done result =>
      obtain ⟨status,next,out⟩ := result
      simp only [Result.ok.injEq,Prod.mk.injEq] at tail
      obtain ⟨rfl,rfl,rfl⟩ := tail
      obtain ⟨default,types,readState,last,decoded,marked,callback⟩ :=
        compiler_table_body_done ops before _ st _ data env count index arity bodyCall
      exact ⟨[],default,types,st.core.pos,readState,before.budget,before.table_depths,
        by simp,.nil,decoded,by simp [last],marked,callback⟩
    | cont next =>
      obtain ⟨nextState,middle,nextArity,nextIndex⟩ := next
      obtain ⟨depth,budget,buffer,rfl,appended,decoded,values,controls,nonLast,indexEq⟩ :=
        compiler_table_body_cont ops law before middle st nextState data env count index
          nextIndex arity nextArity bodyCall
      have nextBound : nextIndex.val ≤ count.val := by
        have ne : index.val ≠ count.val := fun same => nonLast (UScalar.eq_of_val_eq same)
        omega
      have recursive : code.branch_table_with_loop (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
          nextState data env {before with budget,table_depths := buffer} count nextArity
            nextIndex =
          .ok (.Ok (),final,after) := tail
      obtain ⟨depths,default,types,defaultStart,readState,nextBudget,nextBuffer,bufferEq,
        remaining,defaultDecoded,countEq,marked,callback⟩ :=
        ih (count.val-nextIndex.val) (by omega) (before := _) (st := ⟨nextState⟩)
          (index := nextIndex) (arity := nextArity) nextBound recursive rfl
      refine ⟨depth::depths,default,types,defaultStart,readState,nextBudget,nextBuffer,?_,?_,
        defaultDecoded,?_,marked,callback⟩
      · simpa only [appended,List.append_assoc,List.singleton_append] using bufferEq
      · exact (Body.BrTable.LabelsDecoded.snoc .nil decoded).append remaining
      · simp only [List.length_cons]
        omega
end Itasca.Compiler

end

/-! ## Reader Table Body -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Computation
set_option maxRecDepth 4096

/-- Accepted reader decomposition with exact decoded count/targets and
actual selector-pop/final-callback equations. No replacement visitor is assumed. -/
theorem compiler_read_br_table {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st final : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (accepted : code.branch_table_with (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env before = .ok (.Ok (),final,after)) :
    ∃ (count : U32) (first : Usize) (selector : code.StackType) (popped : code.OpIterState)
      (depths : List U32) (default : U32) (types : signature.ResultType)
      (defaultStart : Usize) (readState : code.BodyState) (budget : runtime.compiler.Budget A)
      (buffer : alloc.vec.Vec U32),
      Binary.Leb128.Decoded data st.core.pos count first ∧
      code.pop_with_type {st.core with pos := first} .I32 = .ok (.Ok selector,popped) ∧
      buffer.val = before.table_depths.val ++ depths ∧
      Body.BrTable.LabelsDecoded data popped.pos depths defaultStart ∧
      Binary.Leb128.Decoded data defaultStart default readState.core.pos ∧
      depths.length = count.val ∧
      code.mark_unreachable readState.core = .ok final.core ∧
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
        ops {before with budget,table_depths := buffer} final.core default types = .ok (.Ok (),after) := by
  unfold code.branch_table_with at accepted
  obtain ⟨read,readCall,readSpec⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.core.pos)
  rw [readCall] at accepted
  cases read with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok pair =>
    obtain ⟨count,first⟩ := pair
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,uncurry_apply_pair] at accepted
    obtain ⟨⟨result,popped⟩,popCall,rest⟩ := bind_ok_inv _ _ _ accepted
    cases result with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok selector =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,uncurry_apply_pair] at rest
      obtain ⟨depths,default,types,defaultStart,readState,budget,buffer,bufferEq,
        decoded,defaultDecoded,countEq,marked,callback⟩ :=
        compiler_table_loop ops law before after ⟨popped⟩ final data env count 0#u32 none
          (by scalar_tac) rest
      exact ⟨count,first,selector,popped,depths,default,types,defaultStart,readState,budget,buffer,
        readSpec,popCall,bufferEq,decoded,defaultDecoded,by simpa using countEq,marked,callback⟩
end Itasca.Compiler

end

end

/-! ## BranchTableSource -/

section

/-!
Canonical independent immediate decoding determines every collected Wasm 2 target and the exact accepted final callback.

Main declarations: `compiler_table_source`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Canonical independent immediate decoding determines every collected Wasm 2
target and the exact accepted final callback. -/
theorem compiler_table_source {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st final : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (shape : Body.Control.Shape st.core) (depths : List U32) (fallback : U32) (next : Usize)
    (encoded : Body.BrTable.Decoded data st.core.pos depths fallback next)
    (accepted : code.branch_table_with (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env before = .ok (.Ok (),final,after)) :
    ∃ budget buffer types,
      buffer.val = before.table_depths.val ++ depths ∧
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
        ops {before with budget,table_depths := buffer} final.core fallback types = .ok (.Ok (),after) := by
  obtain ⟨count,first,selector,popped,actual,default,types,last,readState,budget,buffer,
    countDecoded,popCall,bufferEq,labelsDecoded,defaultDecoded,lengthEq,marked,callback⟩ :=
    compiler_read_br_table ops law before after st final data env accepted
  have movedShape : Body.Control.Shape {st.core with pos := first} := ⟨shape.ordered,shape.bounded⟩
  have poppedSpec := code.pop_with_type.total {st.core with pos := first} .I32 movedShape
  rw [popCall,WP.spec_ok] at poppedSpec
  have position : popped.pos = first := poppedSpec.2.2.1
  rw [position] at labelsDecoded
  have decoded : Body.BrTable.Decoded data st.core.pos actual default readState.core.pos :=
    ⟨count,first,last,countDecoded,lengthEq,labelsDecoded,defaultDecoded⟩
  obtain ⟨rfl,rfl,_⟩ := decoded.unique encoded
  exact ⟨budget,buffer,types,bufferEq,callback⟩
end Itasca.Compiler

end

/-! ## BranchTableSuffix -/

section

/-!
A successful suffix check on a live concrete segment determines the exact source types, rather than only their shared slot widths.

Main declarations: `table_suffix_concrete`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

private theorem concrete_fits_prefix (actual expected : List wasm_types.ValueType)
    (fits : Body.Fits false (actual.map code.StackType.Val) expected) :
    ∃ rest, actual=expected++rest := by
  induction expected generalizing actual with
  | nil => exact ⟨actual,rfl⟩
  | cons expected tail ih =>
    cases actual with
    | nil => simp [Body.Fits] at fits
    | cons actual rest =>
      have same : expected=actual := Translation.value_type_injective fits.1
      subst actual
      obtain ⟨remaining,rfl⟩ := ih rest fits.2
      exact ⟨remaining,rfl⟩

/-- A successful suffix check on a live concrete segment determines the exact
source types, rather than only their shared slot widths. -/
theorem table_suffix_concrete (st : code.OpIterState) (outer segment : List code.StackType)
    (expected : List wasm_types.ValueType) (values : st.vals.val=outer++segment)
    (base : (Body.Control.base st).val=outer.length)
    (monomorphic : Body.Control.polymorphic st=false) (known : ConcreteStack segment)
    (suffix : Body.Suffix st expected) :
    ∃ front, Body.Stack.stackTypes segment=front++expected.map Translation.valueType := by
  obtain ⟨actual,rfl⟩ := (concrete_stack_iff segment).mp known
  have fits : Body.Fits false (actual.reverse.map code.StackType.Val) expected.reverse := by
    simpa only [Body.Suffix,values,base,List.drop_left,monomorphic,List.map_reverse] using suffix
  obtain ⟨rest,same⟩ := concrete_fits_prefix actual.reverse expected.reverse fits
  have actualEq : actual=rest.reverse++expected := by
    have reversed := congrArg List.reverse same
    simpa only [List.reverse_reverse,List.reverse_append] using reversed
  refine ⟨rest.reverse.map Translation.valueType,?_⟩
  simp only [Body.Stack.stackTypes,List.map_map,Function.comp_def,actualEq,List.map_append]
end Itasca.Compiler

end

/-! ## BranchTableEffects -/

section

/-!
Complete instruction effects at reader boundaries, after the private label buffer has been consumed. Applies to live and unreachable paths.

Main declarations: `TableReaderEffect`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Complete instruction effects at reader boundaries, after the private label
buffer has been consumed. Applies to live and unreachable paths. -/
def TableReaderEffect {A : Type} (before after : runtime.compiler.FunctionCompiler A)
    (position : Usize) (depths : List U32) : Prop :=
  TableFixed before after ∧ SourceProgress before after ∧ after.next_source=position ∧
  CompilerTableBoundary after ∧ after.reachable=false ∧
  after.function.code.val.length≤before.function.code.val.length+1+2*(depths.length+1)

theorem compiler_reader_table_effect {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st final : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (shape : Body.Control.Shape st.core) (depths : List U32) (fallback : U32) (next : Usize)
    (encoded : Body.BrTable.Decoded data st.core.pos depths fallback next)
    (boundary : CompilerTableBoundary before)
    (accepted : code.branch_table_with (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env before=.ok (.Ok (),final,after)) :
    TableReaderEffect before after final.core.pos depths := by
  obtain ⟨budget,buffer,types,bufferEq,callback⟩ := compiler_table_source ops law before after st final data env
    shape depths fallback next encoded accepted
  obtain ⟨fixed,source,cursor,afterBoundary,dead,growth⟩ := compiler_br_table_effects ops law
    {before with budget,table_depths := buffer} after final.core fallback types boundary.targets callback
  refine ⟨⟨⟨fixed.stable.metadata,fixed.stable.capacity⟩,fixed.controls,fixed.indirect,fixed.simd,fixed.constants⟩,
    source,cursor,afterBoundary,dead,?_⟩
  simpa only [bufferEq,boundary.depths,List.nil_append] using growth

end Itasca.Compiler

end

/-! ## BranchTableTargets -/

section

/-!
Canonical accepted target checks retain a suffix obligation for every label, independently of the compiler visitor's implementation.

Main declarations: `reader_table_targets`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Computation
set_option maxRecDepth 4096

/-- Canonical accepted target checks retain a suffix obligation for every
label, independently of the compiler visitor's implementation. -/
theorem reader_table_targets {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (st final : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (cs : List code.Ctrl) (c : code.Ctrl)
    (controls : st.core.ctrls.val=cs++[c]) (shape : Body.Control.Shape st.core)
    (accepted : code.branch_table_with visitor st data env before=.ok (.Ok (),final,after)) :
    ∃ (count : U32) (first : Usize) (selector : code.StackType) (popped : code.OpIterState)
      (all : List U32) (arity : Usize),
      Binary.Leb128.Decoded data st.core.pos count first ∧
      code.pop_with_type {st.core with pos := first} .I32=.ok (.Ok selector,popped) ∧
      popped.ctrls=st.core.ctrls ∧ popped.pos=first ∧
      all.length=count.val+1 ∧ Body.BrTable.LabelsDecoded data first all final.core.pos ∧
      Body.TableTargets env ⟨popped⟩ all (some arity) := by
  obtain ⟨unit,erased⟩ := code.branch_table_with.accepted_transfer visitor
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor Visitor.empty_accepts st data env before () final after accepted
  cases unit
  unfold code.branch_table_with at erased
  obtain ⟨read,readCall,readSpec⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.core.pos)
  rw [readCall] at erased
  cases read with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at erased
  | Ok pair =>
    obtain ⟨count,first⟩ := pair
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,uncurry_apply_pair] at erased
    obtain ⟨⟨reply,popped⟩,popCall,rest⟩ := bind_ok_inv _ _ _ erased
    have popSpec := code.pop_with_type.total {st.core with pos := first} .I32
      (show Body.Control.Shape {st.core with pos := first} from ⟨shape.ordered,shape.bounded⟩)
    rw [popCall,WP.spec_ok] at popSpec
    dsimp only at popSpec
    cases reply with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok selector =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,uncurry_apply_pair] at rest
      have loopCall : Body.branchTableLoop popped data env count none 0#u32=.ok (.Ok (),final) := by
        simp only [Body.branchTableLoop,rest,bind_ok,uncurry_apply_pair]
      have checked := Body.branchTableLoop.spec ⟨popped⟩ data env count cs c
        (by simpa only [popSpec.2.1] using controls) popSpec.1
      rw [loopCall,WP.spec_ok] at checked
      obtain ⟨all,arity,length,decoded,targets,_,_,_⟩ := checked rfl
      exact ⟨count,first,selector,popped,all,arity,readSpec,popCall,popSpec.2.1,popSpec.2.2.1,
        length,by simpa only [popSpec.2.2.1] using decoded,targets⟩
end Itasca.Compiler

end

/-! ## BranchTableInputs -/

section

/-!
Source scopes and input signatures of decoded br_table reader steps.
-/

/-! ## Reader Table Scopes Body -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Canonical target checks and the saved source zipper discharge every static
branch-table operand obligation on a live path. -/
theorem reader_table_scopes {data env locals index st}
    (p : Body.Pending data env locals index st) {parents current}
    (same : ReaderScopeZipper parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Body.Frames.Saved.vals))
    (chain : SourceEntryChain parents current) (entered : current.entered=true)
    (popped : code.OpIterState) (segment : List code.StackType)
    (values : popped.vals.val=(p.parents.map Body.Frames.Saved.vals).flatten++segment)
    (controls : popped.ctrls=st.core.ctrls) (known : ConcreteStack segment)
    (monomorphic : p.current.ctrl.polymorphic_base=false)
    (depths : List U32) (arity : Option Usize)
    (targets : Body.TableTargets env ⟨popped⟩ depths arity) :
    TableOperandScopes (parents++[current]) (Body.Stack.stackTypes popped.vals.val) depths := by
  intro depth member
  obtain ⟨view,types,n,selected,resolved,_,_,suffix⟩ := targets depth member
  have blocks : (code.BodyState.mk popped).blocks=st.blocks := code.BodyState.blocks_eq_of_ctrls controls
  have originalSelected : Body.labelAt st depth.val=some view := by
    simpa only [Body.labelAt,blocks,controls] using selected
  obtain ⟨scope,actual,scopeAt,actualResolved,branchTypes⟩ := same.label p.opened depth.val view originalSelected
  have typeEq : actual=types := by rw [resolved] at actualResolved; exact Option.some.inj actualResolved.symm
  subst actual
  obtain ⟨C,outer,spine,header,base,typed,savedControls,_,originalValues⟩ := p.opened
  have outerEq : outer=(p.parents.map Body.Frames.Saved.vals).flatten := by
    simpa only [List.flatMap_def] using spine_values spine
  have poppedBase : (Body.Control.base popped).val=(p.parents.map Body.Frames.Saved.vals).flatten.length := by
    simpa [Body.Control.base,controls,savedControls,outerEq] using base
  have poppedMono : Body.Control.polymorphic popped=false := by
    simpa [Body.Control.polymorphic,controls,savedControls] using monomorphic
  obtain ⟨front,arguments⟩ := table_suffix_concrete popped _ segment types values poppedBase poppedMono known suffix
  obtain ⟨discarded,whole⟩ := fronts.branch depth.val scope scopeAt segment front
    (by simpa only [branchTypes] using arguments)
  have selected' : (parents++[current]).reverse[depth.val]?=some scope := by
    simpa only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.singleton_append] using scopeAt
  refine ⟨scope,discarded,selected',chain.all_entered entered scope ?_,?_⟩
  · simpa only [List.mem_reverse] using List.mem_of_getElem? selected'
  · simpa only [values] using whole
end Itasca.Compiler

end

/-! ## Reader Table Inputs Body -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- Every live canonical Wasm 2 BR_TABLE read supplies the source scope and
operand suffix certificate required by actual table lowering. -/
theorem reader_table_inputs {V : Type} (visitor : code.OpVisitor V)
    {data env locals index st} (p : Body.Pending data env locals index st)
    {parents current}
    (same : ReaderScopeZipper parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Body.Frames.Saved.vals))
    (chain : SourceEntryChain parents current) (entered : current.entered=true)
    (known : ConcreteStack st.core.vals.val)
    (monomorphic : p.current.ctrl.polymorphic_base=false)
    (before after : V) (final : code.BodyState) (depths : List U32) (fallback : U32) (next : Usize)
    (encoded : Body.BrTable.Decoded data st.core.pos depths fallback next)
    (accepted : code.branch_table_with visitor st data env before=.ok (.Ok (),final,after)) :
    ∃ stack, Body.Stack.stackTypes st.core.vals.val=stack++[.I32] ∧
      TableOperandScopes (parents++[current]) stack (depths++[fallback]) := by
  obtain ⟨C,outer,spine,header,base,typed,controls,_,values⟩ := p.opened
  obtain ⟨count,first,selector,popped,all,arity,countDecoded,popCall,popControls,popPos,
    countEq,labelsDecoded,targets⟩ := reader_table_targets visitor before after st final data env
      _ p.current.ctrl controls p.opened.shape.core accepted
  obtain ⟨sourceCount,sourceFirst,defaultStart,countSource,lengthSource,labelsSource,defaultSource⟩ := encoded
  obtain ⟨rfl,rfl⟩ := countDecoded.unique countSource
  have allEq : all=depths++[fallback] := (labelsDecoded.unique (labelsSource.snoc defaultSource)
    (by simp only [List.length_append,List.length_singleton]; omega)).1
  rw [allEq] at targets
  have wholeKnown : ConcreteStack (outer++p.current.vals) := values ▸ known
  have segmentKnown := (concrete_stack_append.mp wholeKnown).2
  have popSpec := code.pop_with_type.segment {st.core with pos := first} outer p.current.vals .I32
    values (by simpa [Body.Control.base,controls] using base)
  rw [popCall,WP.spec_ok] at popSpec
  obtain ⟨_,_,remaining,poppedValues,popEffect⟩ := popSpec
  dsimp only at poppedValues popEffect
  have poly : Body.Control.polymorphic {st.core with pos := first}=false := by
    simpa [Body.Control.polymorphic,controls] using monomorphic
  rw [poly] at popEffect
  have segmentEq := typed_pop_exact segmentKnown popEffect
  have remainingKnown := (concrete_stack_append.mp (segmentEq ▸ segmentKnown)).1
  have outerEq : outer=(p.parents.map Body.Frames.Saved.vals).flatten := by
    simpa only [List.flatMap_def] using spine_values spine
  have scopes := reader_table_scopes p same fronts chain entered popped remaining
    (by simpa only [outerEq] using poppedValues) popControls remainingKnown monomorphic
    (depths++[fallback]) (some arity) targets
  refine ⟨Body.Stack.stackTypes popped.vals.val,?_,scopes⟩
  simp only [values,segmentEq,poppedValues,Body.Stack.stackTypes,List.map_append,List.map_cons,List.map_nil,
    Translation.valueType,List.append_assoc]
end Itasca.Compiler

end

end

/-! ## BranchTablePost -/

section

/-!
The postcondition of a br_table reader step.

Main declarations: `reader_table_post`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

theorem reader_table_post {V : Type} (visitor : code.OpVisitor V)
    {data env locals index st} (p : Body.Pending data env locals index st)
    (before after : V) (final : code.BodyState) (depths : List U32) (fallback : U32) (next : Usize)
    (byte : data.val[p.start.val]'p.inbounds=0x0e#u8)
    (encoded : Body.BrTable.Decoded data st.core.pos depths fallback next)
    (accepted : code.branch_table_with visitor st data env before=.ok (.Ok (),final,after)) :
    Body.ReaderPost p final.core (Body.BrTable.instruction depths fallback) true [] := by
  obtain ⟨unit,empty⟩ := code.branch_table_with.accepted_transfer visitor
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor Visitor.empty_accepts st data env before () final after accepted
  cases unit
  have erased : code.branch_table st data env =.ok (.Ok (),final) := by
    simp only [code.branch_table,empty,bind_ok,uncurry_apply_pair]
  have effect := p.branch_table_reader byte
  rw [erased, WP.spec_ok] at effect
  obtain ⟨actualDepths, actual, decoded, post⟩ := effect rfl
  obtain ⟨rfl, rfl, _⟩ := decoded.unique encoded
  exact post

end Itasca.Compiler

end

/-! ## ControlEffects -/

section

/-!
Every successful structured-control reader step is one control compiler
callback with `ControlEffects`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

theorem reader_block_effects {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 2#u8 before = .ok (.Ok (), out, after)) :
    ControlEffects before after out.core := by
  rw [Body.CallbackTrace.dispatch_block] at accepted
  obtain ⟨value, _, called⟩ := Body.CallbackTrace.bodyRun.accepted _ _ _ _ _ _ accepted
  exact compiler_block_effects ops law before after out.core value called

theorem reader_loop_effects {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 3#u8 before = .ok (.Ok (), out, after)) :
    ControlEffects before after out.core := by
  rw [Body.CallbackTrace.dispatch_loop] at accepted
  obtain ⟨value, _, called⟩ := Body.CallbackTrace.bodyRun.accepted _ _ _ _ _ _ accepted
  exact compiler_loop_effects ops law before after out.core value called

theorem reader_if_effects {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 4#u8 before = .ok (.Ok (), out, after)) :
    ControlEffects before after out.core := by
  rw [Body.CallbackTrace.dispatch_if] at accepted
  obtain ⟨value, _, called⟩ := Body.CallbackTrace.bodyRun.accepted _ _ _ _ _ _ accepted
  exact compiler_if_effects ops law before after out.core value called

theorem reader_else_effects {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 5#u8 before = .ok (.Ok (), out, after)) :
    ControlEffects before after out.core := by
  rw [Body.CallbackTrace.dispatch_else] at accepted
  obtain ⟨value, _, called⟩ := Body.CallbackTrace.bodyRun.accepted _ _ _ _ _ _ accepted
  exact compiler_else_effects ops law before after out.core value.2 called

theorem reader_end_effects {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 11#u8 before = .ok (.Ok (), out, after)) :
    ControlEffects before after out.core := by
  rw [Body.CallbackTrace.dispatch_end] at accepted
  obtain ⟨value, _, called⟩ := Body.CallbackTrace.bodyRun.accepted _ _ _ _ _ _ accepted
  exact compiler_end_effects ops law before after out.core value.1 value.2 called

theorem reader_br_effects {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 12#u8 before = .ok (.Ok (), out, after)) :
    ControlEffects before after out.core := by
  rw [Body.CallbackTrace.dispatch_br] at accepted
  obtain ⟨value, _, called⟩ := Body.CallbackTrace.bodyRun.accepted _ _ _ _ _ _ accepted
  exact compiler_br_effects ops law before after out.core value.1 value.2 called

theorem reader_br_if_effects {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 13#u8 before = .ok (.Ok (), out, after)) :
    ControlEffects before after out.core := by
  rw [Body.CallbackTrace.dispatch_br_if] at accepted
  obtain ⟨value, _, called⟩ := Body.CallbackTrace.bodyRun.accepted _ _ _ _ _ _ accepted
  exact compiler_br_if_effects ops law before after out.core value.1 value.2 called

theorem reader_control_effects {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
    (opcode : U8) (control : ScopeOpcode opcode ∨ opcode = 5#u8 ∨ opcode = 11#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index opcode before = .ok (.Ok (), out, after)) :
    ControlEffects before after out.core := by
  rcases control with scope | rfl | rfl
  · simp only [ScopeOpcode, List.mem_cons, List.not_mem_nil, or_false] at scope
    rcases scope with h | h | h | h | h
    · obtain rfl : opcode = 2#u8 := (UScalar.eq_equiv _ _).mpr h
      exact reader_block_effects ops law before after st out data env ctx index accepted
    · obtain rfl : opcode = 3#u8 := (UScalar.eq_equiv _ _).mpr h
      exact reader_loop_effects ops law before after st out data env ctx index accepted
    · obtain rfl : opcode = 4#u8 := (UScalar.eq_equiv _ _).mpr h
      exact reader_if_effects ops law before after st out data env ctx index accepted
    · obtain rfl : opcode = 12#u8 := (UScalar.eq_equiv _ _).mpr h
      exact reader_br_effects ops law before after st out data env ctx index accepted
    · obtain rfl : opcode = 13#u8 := (UScalar.eq_equiv _ _).mpr h
      exact reader_br_if_effects ops law before after st out data env ctx index accepted
  · exact reader_else_effects ops law before after st out data env ctx index accepted
  · exact reader_end_effects ops law before after st out data env ctx index accepted
end Itasca.Compiler

end

end

/-! ## ControlKind -/

section

open Itasca.Representation

/-!
# Control Kind

Root and entered reader frames determine their control kind and initial boundary. Stack-pop and entry safety facts establish the corresponding compiler state.
-/

/-! ## RootFrame -/

section

/-!
The root control frame retained by reader execution.

Main declarations: `reader_root_frame`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

private theorem paired_head_right {α β : Type} {R : α → β → Prop} {left right}
    (paired : List.Forall₂ R left right) (value : β) (found : right.head? = some value) :
    ∃ item, left.head? = some item ∧ R item value := by
  cases paired with
  | nil => simp at found
  | cons head tail =>
    simp only [List.head?_cons, Option.some.injEq] at found
    subst value
    exact ⟨_, rfl, head⟩

private theorem head_member {α : Type} {items : List α} {item}
    (found : items.head? = some item) : item ∈ items := by
  cases items with
  | nil => simp at found
  | cons first rest => simp only [List.head?_cons, Option.some.injEq] at found; subst item; simp

theorem reader_root_frame {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (compiler : runtime.compiler.FunctionCompiler A) {locals parents current}
    (physical : ScopeFrameStack locals compiler parents current)
    (same : ReaderScopeZipper parents current p.parents p.current) :
    ∃ frame, compiler.frames.val[0]? = some frame ∧
      frame.results.val = slots (p.ft.results.val.map Translation.valueType) := by
  have bodyType := p.bodyType
  unfold Body.Frames.bodyType at bodyType
  obtain ⟨saved, savedHead, savedType⟩ := Option.map_eq_some_iff.mp bodyType
  have sources := List.rel_append same.parents (.cons same.current .nil)
  obtain ⟨scope, scopeHead, matched⟩ := paired_head_right sources saved savedHead
  obtain ⟨frame, frameHead, framed⟩ := paired_head_right (List.Forall₂.flip physical.frames) scope scopeHead
  obtain ⟨C, outer, spine, header, _⟩ := p.opened
  have savedHeader : ∃ C, Body.Frames.Header env C saved := by
    have member := head_member savedHead
    rcases List.mem_append.mp member with member | member
    · exact spine.headers saved member
    · have eq : saved = p.current := by simpa using member
      subst saved
      exact ⟨C, header⟩
  obtain ⟨D, savedHeader⟩ := savedHeader
  have outs := savedHeader.outputs
  rw [savedType] at outs
  have outputs : saved.outs = p.ft.results.val := by
    simpa [Body.outputs, Body.resolve, p.signature] using outs.symm
  refine ⟨frame, ?_, ?_⟩
  · simpa only [List.head?_eq_getElem?] using frameHead
  · rw [framed.results, matched.results, outputs]

end Itasca.Compiler

end

/-! ## EnterSafety -/

section

/-!
Typed-pop prefixes and safe control-scope entry. EntryPrefix carries the parameter/argument bounds consumed by the entering reader callback.
-/

/-! ## Reader Pop Prefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem popped_prefix {poly before value after}
    (popped : Body.Stack.Semantics.Popped poly before value after) : after <+: before := by
  cases popped with
  | explicit => exact ⟨_, rfl⟩
  | implicit => exact ⟨[], by simp⟩

theorem typed_pop_prefix {poly before expected result after}
    (effect : Body.Stack.Semantics.TypedPopResult poly before expected result after) : after <+: before := by
  cases result with
  | Ok value => exact popped_prefix effect.1
  | Err error =>
    rcases effect with ⟨_, _, _, rfl⟩ | ⟨_, value, popped, _⟩
    · exact List.nil_prefix
    · exact popped_prefix popped

@[step] theorem pop_with_type_prefix (st : code.OpIterState) (outer segment : List code.StackType)
    (expected : wasm_types.ValueType) (values : st.vals.val = outer ++ segment)
    (base : (Body.Control.base st).val = outer.length) :
    code.pop_with_type st expected ⦃ out => out.2.ctrls = st.ctrls ∧ out.2.pos = st.pos ∧
      ∃ rest, out.2.vals.val = outer ++ rest ∧ rest <+: segment ⦄ := by
  apply WP.spec_mono (code.pop_with_type.segment st outer segment expected values base)
  rintro ⟨result, after⟩ ⟨controls, position, rest, afterValues, effect⟩
  exact ⟨controls, position, rest, afterValues, typed_pop_prefix effect⟩

@[step] theorem pop_types_prefix (st : code.OpIterState) (outer segment : List code.StackType)
    (expected : Slice wasm_types.ValueType) (values : st.vals.val = outer ++ segment)
    (base : (Body.Control.base st).val = outer.length) :
    code.pop_types st expected ⦃ out => out.2.ctrls = st.ctrls ∧ out.2.pos = st.pos ∧
      ∃ rest, out.2.vals.val = outer ++ rest ∧ rest <+: segment ⦄ := by
  unfold code.pop_types code.pop_types_loop
  apply loop.spec_decr_nat (fun p => p.2.val)
    (fun p => p.2.val ≤ expected.val.length ∧ p.1.ctrls = st.ctrls ∧ p.1.pos = st.pos ∧
      ∃ rest, p.1.vals.val = outer ++ rest ∧ rest <+: segment)
  · rintro ⟨current, index⟩ ⟨bound, controls, position, currentSegment, currentValues, currentPrefix⟩
    dsimp only at bound controls position currentValues currentPrefix
    unfold code.pop_types_loop.body
    dsimp only
    split
    · simp only [WP.spec_ok]
      exact ⟨controls, position, currentSegment, currentValues, currentPrefix⟩
    · step as ⟨next, decrement⟩
      have inBounds : next.val < expected.val.length := by scalar_tac
      step as ⟨ty, tyEq⟩
      have currentBase : (Body.Control.base current).val = outer.length := by
        simpa only [Body.Control.base, controls] using base
      step with pop_with_type_prefix current outer currentSegment ty currentValues currentBase
        as ⟨result, after, afterControls, afterPosition, rest, afterValues, afterPrefix⟩
      cases result with
      | Err error =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
        exact ⟨afterControls.trans controls, afterPosition.trans position, rest, afterValues,
          afterPrefix.trans currentPrefix⟩
      | Ok value =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, WP.spec_ok]
        exact ⟨by scalar_tac, afterControls.trans controls, afterPosition.trans position,
          ⟨rest, afterValues, afterPrefix.trans currentPrefix⟩, by scalar_tac⟩
  · exact ⟨by simp, rfl, rfl, segment, values, ⟨[], by simp⟩⟩

@[step] theorem pop_results_prefix (st : code.OpIterState) (env : metadata.Env)
    (view : signature.ResultType) (outer segment : List code.StackType)
    (values : st.vals.val = outer ++ segment) (base : (Body.Control.base st).val = outer.length) :
    code.pop_results st env view ⦃ out => out.2.ctrls = st.ctrls ∧ out.2.pos = st.pos ∧
      ∃ rest, out.2.vals.val = outer ++ rest ∧ rest <+: segment ⦄ := by
  cases view with
  | Empty =>
    simp only [code.pop_results, WP.spec_ok]
    exact ⟨trivial, trivial, segment, values, ⟨[], by simp⟩⟩
  | One ty =>
    unfold code.pop_results
    step with pop_with_type_prefix st outer segment ty values base
      as ⟨result, after, controls, position, rest, afterValues, afterPrefix⟩
    cases result <;> simp_all [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | «Type» index part =>
    unfold code.pop_results
    step as ⟨i, castEq⟩
    split
    · simp only [WP.spec_ok]
      exact ⟨trivial, trivial, segment, values, ⟨[], by simp⟩⟩
    · cases part <;> step as ⟨ty, tyEq⟩
      all_goals exact pop_types_prefix st outer segment _ values base
end Itasca.Compiler

end

/-! ## Reader Enter Prefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Body Itasca.Computation

/-- The newly opened frame begins at an unchanged prefix of the old raw operands. -/
def EntryPrefix (before after : code.OpIterState) : Prop :=
  ∃ prior ctrl, after.ctrls.val = prior ++ [ctrl] ∧
    ctrl.value_stack_base.val ≤ after.vals.val.length ∧
    after.vals.val.take ctrl.value_stack_base.val <+: before.vals.val

@[step] theorem enter_params_prefix (st : code.BodyState) (env : metadata.Env)
    (form : Frames.Form) (bt : signature.BlockType) (outer segment : List code.StackType)
    (values : st.core.vals.val = outer ++ segment) (base : (Body.Control.base st.core).val = outer.length)
    (shape : Body.Control.Shape st.core) (capacity : st.blocks.val.length < Usize.max) :
    enterParams st env form.kind bt ⦃ out => out.1 = .Ok () → EntryPrefix st.core out.2.core ⦄ := by
  unfold enterParams
  simp only [signature.BlockType.params.spec, bind_ok]
  step with pop_results_prefix st.core env (inputs bt) outer segment values base
    as ⟨result, middle, controls, position, rest, middleValues, restPrefix⟩
  have middleShape : Body.Control.Shape middle := shape.replace_operands controls (by simp [base, middleValues])
  step
  split
  · step with code.push_frame.spec {st with core := middle} form.kind bt (by simpa [controls] using capacity)
      as ⟨framed, frameControls, frameValues, framePosition, frameBlocks⟩
    have framedShape := shape_push middleShape form.kind bt frameControls frameValues
    step with code.push_results.total framed.core env (inputs bt) framedShape
      as ⟨reply, final, finalShape, finalControls, finalPosition, pushed⟩
    intro success
    obtain ⟨types, resolved, appended⟩ := pushed success
    refine ⟨middle.ctrls.val, frame middle form.kind bt, ?_, ?_, ?_⟩
    · rw [finalControls, frameControls]
    · simp [Body.frame, alloc.vec.Vec.len, appended, frameValues]
    · simp only [Body.frame, alloc.vec.Vec.len]
      rw [appended, frameValues]
      change (middle.vals.val ++ types.map code.StackType.Val).take middle.vals.val.length <+: st.core.vals.val
      rw [List.take_left]
      rcases restPrefix with ⟨suffix, suffixEq⟩
      exact ⟨suffix, by rw [middleValues, values, ← suffixEq, List.append_assoc]⟩
  · step*

@[step] theorem enter_args_prefix (st : code.BodyState) (env : metadata.Env)
    (form : Frames.Form) (bt : signature.BlockType) (outer segment : List code.StackType)
    (initial : form.Initial)
    (values : st.core.vals.val = outer ++ segment) (base : (Body.Control.base st.core).val = outer.length)
    (shape : Body.Control.Shape st.core) (capacity : st.blocks.val.length < Usize.max) :
    enterArgs st env form.kind bt ⦃ out => out.1 = .Ok () → EntryPrefix st.core out.2.core ⦄ := by
  rcases initial with rfl | rfl | rfl
  · exact enter_params_prefix st env .block bt outer segment values base shape capacity
  · exact enter_params_prefix st env .loop bt outer segment values base shape capacity
  · simp only [enterArgs, Frames.Form.kind]
    step with pop_with_type_prefix st.core outer segment .I32 values base
      as ⟨result, middle, controls, position, rest, middleValues, restPrefix⟩
    step
    split
    · have middleShape := shape.replace_operands controls (by simp [base, middleValues])
      apply WP.spec_mono (enter_params_prefix {st with core := middle} env .then_ bt outer rest middleValues
        (by simpa [Body.Control.base, controls] using base) middleShape (by simpa [controls] using capacity))
      rintro ⟨status,after⟩ effect success
      obtain ⟨prior,ctrl,afterControls,bound,kept⟩ := effect success
      refine ⟨prior,ctrl,afterControls,bound,kept.trans ?_⟩
      rcases restPrefix with ⟨suffix,suffixEq⟩
      exact ⟨suffix, by rw [middleValues,values,← suffixEq,List.append_assoc]⟩
    · step*
end Itasca.Compiler
namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Body Itasca.Computation

theorem reader_enter_prefix {data env locals index st out bt} {form : Frames.Form}
    (p : Body.Pending data env locals index st) (initial : form.Initial)
    (accepted : code.enter_info st data env form.kind = .ok (.Ok bt, out)) :
    EntryPrefix st.core out.core := by
  have erased : code.enter st data env form.kind = .ok (.Ok (), out) := by
    simp [code.enter, accepted, core.result.Result.Insts.CoreOpsTry.branch]
  rw [enter_eq] at erased
  obtain ⟨readResult, readCall, rest⟩ := bind_ok_inv _ _ _ erased
  cases readResult with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok pair =>
    obtain ⟨decoded, next⟩ := pair
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    obtain ⟨checked, checkCall, rest⟩ := bind_ok_inv _ _ _ rest
    cases checked with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok unitValue =>
      cases unitValue
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      obtain ⟨C, outer, spine, header, position, typed, controls, blocks, values⟩ := p.opened
      have base : (Body.Control.base st.core).val = outer.length := by simp [Body.Control.base, controls, position]
      have capacity : st.blocks.val.length < Usize.max := by
        have size := p.size
        have inside := p.inbounds
        have count := p.ctrls
        have room := limits.MAX_FUNCTION_BYTES.room
        omega
      have effect := enter_args_prefix {st with core := {st.core with pos := next}} env form decoded outer p.current.vals
        initial values base ⟨p.opened.shape.core.ordered, p.opened.shape.core.bounded⟩ capacity
      rw [rest, WP.spec_ok] at effect
      exact effect rfl
end Itasca.Compiler

end

/-! ## Reader Enter Safety -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Body

theorem reader_enter_signature {data env locals index st out bt} {form : Frames.Form}
    (p : Body.Pending data env locals index st) (initial : form.Initial)
    (accepted : code.enter_info st data env form.kind = .ok (.Ok bt, out)) :
    ∃ ins outs, resolve env (inputs bt) = some ins ∧ resolve env (outputs bt) = some outs := by
  have erased : code.enter st data env form.kind = .ok (.Ok (), out) := by
    simp [code.enter, accepted, core.result.Result.Insts.CoreOpsTry.branch]
  obtain ⟨C, outer, spine, header, parentBase, typed, ctrls, blocks, vals⟩ := p.opened
  have capacity : st.blocks.val.length < Usize.max := by
    have := p.ctrls; have := p.inbounds; have := p.size; have := limits.MAX_FUNCTION_BYTES.room
    omega
  have effect := code.enter.sound st data env form initial outer p.current.vals vals
    (by simp [Body.Control.base, ctrls, parentBase]) p.opened.shape.core capacity
  rw [erased, WP.spec_ok] at effect
  obtain ⟨sourceBt, ins, outs, decoded, inputs, outputs, _⟩ := effect rfl
  have info := code.enter_info.bytes st data env form.kind p.opened.shape.core capacity
  rw [accepted, WP.spec_ok] at info
  obtain ⟨rfl, _⟩ := (info bt rfl).unique decoded
  exact ⟨ins,outs,inputs,outputs⟩

theorem EntryPrefix.height_bound {A} {compiler : runtime.compiler.FunctionCompiler A}
    {before after : code.OpIterState}
    (kept : EntryPrefix before after) (observed : ObservedStack compiler before.vals.val) :
    ∃ prior ctrl, after.ctrls.val = prior ++ [ctrl] ∧
      ctrl.value_stack_base.val ≤ after.vals.val.length ∧
      compiler.function.local_slots.val + stackWords (after.vals.val.take ctrl.value_stack_base.val) ≤ U32.max := by
  obtain ⟨prior,ctrl,controls,bound,suffix,eq⟩ := kept
  refine ⟨prior,ctrl,controls,bound,?_⟩
  have limited := observed.prefix_bound (after.vals.val.take ctrl.value_stack_base.val).length
  rw [← eq,List.take_left] at limited
  exact limited

theorem compiler_enter_reader_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    {data env locals index st} (p : Body.Pending data env locals index st)
    (form : Frames.Form) (initial : form.Initial)
    (signatures : SignatureSequence compiler.signatures.val env.types.val)
    (observed : ObservedStack compiler st.core.vals.val)
    (coordinate : compiler.function.body_start.val+compiler.next_source.val ≤ Usize.max)
    (pcBound : compiler.function.code.val.length+1 < 2^32)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (mapsFit : compiler.function.controls.val.length < Usize.max)
    (framesFit : compiler.frames.val.length < Usize.max) :
    CallbackTrace.bodyRun (code.enter_info st data env form.kind)
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) (enterAction form) compiler ⦃ out =>
        out.1 = .Ok () → ObservedStack out.2.2 out.2.1.core.vals.val ⦄ := by
  have capacity : st.blocks.val.length < Usize.max := by
    have := p.ctrls; have := p.inbounds; have := p.size; have := limits.MAX_FUNCTION_BYTES.room
    omega
  apply reader_body_run_reached _ _ _ compiler (fun s c => ObservedStack c s.core.vals.val)
  · exact WP.spec_mono (code.enter_info.total st data env form.kind p.opened.shape.core capacity) (by simp)
  · intro out bt read
    obtain ⟨ins,outs,inputs,outputs⟩ := reader_enter_signature p initial read
    obtain ⟨signature,selected,_⟩ := signatures.select inputs outputs
    obtain ⟨prior,ctrl,controls,bound,height⟩ :=
      (reader_enter_prefix p initial read).height_bound observed
    have normal := compiler_enter_total ops law compiler out.core ctrl prior form.kind bt signature
      controls selected bound height coordinate pcBound codeFits sourceFits mapsFit framesFit
      (by rcases initial with rfl | rfl | rfl <;> simp [Frames.Form.kind])
    rcases initial with rfl | rfl | rfl <;> exact normal
end Itasca.Compiler

end

end

/-! ## BoundaryInitial -/

section

/-!
The initial reader boundary before body compilation.

Main declarations: `ReaderBoundary.initial`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem ReaderBoundary.initial (data : Slice U8) (env : metadata.Env)
    (locals : alloc.vec.Vec wasm_types.ValueType) (index : U32) (ft : wasm_types.FuncType)
    (signature : env.types.val[index.val]? = some ft)
    (size : data.length ≤ limits.MAX_FUNCTION_BYTES.val) :
    ReaderBoundary data env locals index ft (Body.initial index) []
      (Body.Frames.Saved.fresh 0#usize .body (.TypeIndex index) ft.params.val ft.results.val) := by
  refine ⟨signature, ?_, ?_, rfl, ?_, ?_⟩
  · constructor <;> simp [Body.initial, size]
  · apply Body.Frames.Open.start env _ (Translation.Environment.context_wf env ⟨locals, ft.results⟩)
    · simp [Body.resolve, Body.inputs, signature]
    · simp [Body.resolve, Body.outputs, signature]
    · rfl
    · rfl
    · rfl
  · simpa [Body.Frames.trace, Body.Frames.Saved.trace, Body.Frames.Saved.fresh,
      Body.Frames.Form.opening, Body.initial] using Body.Consumed.nil (data := data) 0#usize (by simp)
  · simp [Body.Frames.trace, Body.Frames.Saved.trace, Body.Frames.Saved.fresh, Body.Frames.Form.opening]
end Itasca.Compiler

end

/-! ## ControlKind -/

section

/-!
Checked metadata-producing body readers, excluding the streamed table reader, which has a separate source-count replay proof.

Main declarations: `ControlReaderKind` and `opcode`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

/-- Checked metadata-producing body readers, excluding the streamed table
reader, which has a separate source-count replay proof. -/
inductive ControlReaderKind where
  | block
  | loop
  | if_
  | else_
  | end_
  | br
  | br_if
  | return_
  | call
  | call_indirect

namespace ControlReaderKind

def opcode : ControlReaderKind → U8
  | .block => 2#u8
  | .loop => 3#u8
  | .if_ => 4#u8
  | .else_ => 5#u8
  | .end_ => 11#u8
  | .br => 12#u8
  | .br_if => 13#u8
  | .return_ => 15#u8
  | .call => 16#u8
  | .call_indirect => 17#u8

/-- Every control opcode belongs to the shared reader inventory. -/
theorem of_opcode_mem (opcode : U8)
    (member : opcode.val ∈ [2,3,4,5,11,12,13,15,16,17]) : ∃ kind : ControlReaderKind, opcode = kind.opcode := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with equal | equal | equal | equal | equal | equal | equal | equal | equal | equal
  · exact ⟨.block,UScalar.eq_of_val_eq equal⟩
  · exact ⟨.loop,UScalar.eq_of_val_eq equal⟩
  · exact ⟨.if_,UScalar.eq_of_val_eq equal⟩
  · exact ⟨.else_,UScalar.eq_of_val_eq equal⟩
  · exact ⟨.end_,UScalar.eq_of_val_eq equal⟩
  · exact ⟨.br,UScalar.eq_of_val_eq equal⟩
  · exact ⟨.br_if,UScalar.eq_of_val_eq equal⟩
  · exact ⟨.return_,UScalar.eq_of_val_eq equal⟩
  · exact ⟨.call,UScalar.eq_of_val_eq equal⟩
  · exact ⟨.call_indirect,UScalar.eq_of_val_eq equal⟩

def Parameter : ControlReaderKind → Type
  | .block => signature.BlockType
  | .loop => signature.BlockType
  | .if_ => signature.BlockType
  | .else_ => code.LabelKind × signature.BlockType
  | .end_ => code.LabelKind × signature.BlockType
  | .br => U32 × signature.ResultType
  | .br_if => U32 × signature.ResultType
  | .return_ => Unit
  | .call => U32
  | .call_indirect => U32 × U32

def read (kind : ControlReaderKind) (st : code.BodyState) (data : Slice U8)
    (env : metadata.Env) (index : U32) : Result (core.result.Result kind.Parameter error.OpError × code.BodyState) :=
  match kind with
  | .block => code.enter_info st data env .Block
  | .loop => code.enter_info st data env .Loop
  | .if_ => code.enter_info st data env .Then
  | .else_ => code.end_frame_info st env true
  | .end_ => code.end_frame_info st env false
  | .br => code.branch_info st data env false
  | .br_if => code.branch_info st data env true
  | .return_ => Body.returnStep st env index
  | .call => code.call_info st data env
  | .call_indirect => code.call_indirect_info st data env

def action : (kind : ControlReaderKind) → kind.Parameter → Action
  | .block => .block
  | .loop => .loop
  | .if_ => .if_
  | .else_ => fun arg => .else_ arg.2
  | .end_ => fun arg => .end_ arg.1 arg.2
  | .br => fun arg => .br arg.1 arg.2
  | .br_if => fun arg => .br_if arg.1 arg.2
  | .return_ => fun _ => .return_
  | .call => .call
  | .call_indirect => fun arg => .call_indirect arg.1 arg.2

/-- Every inventory entry agrees with actual complete dispatch. -/
theorem dispatch {V : Type} (kind : ControlReaderKind) (visitor : code.OpVisitor V)
    (st : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32) (before : V) :
    code.step_profile visitor st data env ctx index kind.opcode before =
      Body.CallbackTrace.bodyRun (kind.read st data env index) visitor kind.action before := by
  cases kind
  · exact Body.CallbackTrace.dispatch_block visitor st data env ctx index before
  · exact Body.CallbackTrace.dispatch_loop visitor st data env ctx index before
  · exact Body.CallbackTrace.dispatch_if visitor st data env ctx index before
  · exact Body.CallbackTrace.dispatch_else visitor st data env ctx index before
  · exact Body.CallbackTrace.dispatch_end visitor st data env ctx index before
  · exact Body.CallbackTrace.dispatch_br visitor st data env ctx index before
  · exact Body.CallbackTrace.dispatch_br_if visitor st data env ctx index before
  · exact Body.CallbackTrace.dispatch_return visitor st data env ctx index before
  · exact Body.CallbackTrace.dispatch_call visitor st data env ctx index before
  · exact Body.CallbackTrace.dispatch_call_indirect visitor st data env ctx index before

/-- Source byte provenance for every metadata-producing reader in this
inventory. This also bounds its accepted final cursor by input length. -/
theorem records {data env locals index st} (kind : ControlReaderKind)
    (pending : Body.Pending data env locals index st) {V : Type}
    (visitor : code.OpVisitor V) (observe : V → List Observation)
    (recorded : Records visitor observe) (ctx : code.Context)
    (byte : data.val[pending.start.val]'pending.inbounds = kind.opcode) :
    Body.CallbackTrace.StepRecords pending visitor observe ctx kind.opcode := by
  cases kind
  · exact Body.CallbackTrace.step_block pending visitor observe recorded ctx byte
  · exact Body.CallbackTrace.step_loop pending visitor observe recorded ctx byte
  · exact Body.CallbackTrace.step_if pending visitor observe recorded ctx byte
  · exact Body.CallbackTrace.step_else pending visitor observe recorded ctx byte
  · exact Body.CallbackTrace.step_end pending visitor observe recorded ctx byte
  · exact Body.CallbackTrace.step_br pending visitor observe recorded ctx byte
  · exact Body.CallbackTrace.step_br_if pending visitor observe recorded ctx byte
  · exact Body.CallbackTrace.step_return pending visitor observe recorded ctx byte
  · exact Body.CallbackTrace.step_call pending visitor observe recorded ctx byte
  · exact Body.CallbackTrace.step_call_indirect pending visitor observe recorded ctx byte

end ControlReaderKind
end Itasca.Compiler

end

end
