import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableMetadata
import Itasca.Wasm2.Visitor.BrTable
import Itasca.Binary.Leb128
import Itasca.Binary.Wasm1.EncodingComplete
import Itasca.Binary.Wasm1.EncodingUnique
import Itasca.Visitor.BodyReplay
import Itasca.Visitor.RunTrace
import Itasca.Handler.RawControl
import Itasca.Runtime.Compiler.Body.Reader.Control.FrontTransitions
import Itasca.Wasm2.Control.BrTableSound
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableSafetyEffects
import Itasca.Visitor.Accepts
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CompilerCodeMonotoneCallbacks
import Itasca.Runtime.Compiler.Local.Capacity.ControlCapacity
import Itasca.Runtime.Compiler.Local.Capacity.LiteralCapacity
import Itasca.Runtime.Compiler.Local.Lowering.Literal.LiteralSources
import Itasca.Runtime.Compiler.Local.Source.SourceLengthsTactic
import Itasca.Runtime.Compiler.Local.Lowering.Integer.NumericLowering
import Itasca.Runtime.Compiler.Local.Lowering.Local.LoweringLocal
import Itasca.Runtime.Compiler.Local.Source.SourceCursorTactic
import Itasca.Runtime.Compiler.Body.Source.TypedLowering
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerTerminalMetadata
import Itasca.Runtime.Compiler.Body.Reader.Scalar.Unreachable
import Itasca.Runtime.Compiler.Body.Reader.Control.Return
import Itasca.Runtime.Compiler.Local.Relations.Syntax.ReaderOpcode
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CloseMapEffect

/-!
Sections, each formerly its own module: BranchTableWasm2, BranchTableSource, BranchTableSuffix, BranchTableEffects, BranchTableTargetsWasm2, BranchTableInputsWasm2, BranchTablePost, ControlEffects.
-/

/-! ## BranchTableWasm2 -/

section

/-!
br_table reader inversion through label-vector body and loop execution. The final theorem identifies the decoded branch-table source instruction.
-/

/-! ## Reader Table Rest -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.ResultFacts Itasca.Wasm2.Visitor

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
end Itasca.Runtime.Compiler

end

/-! ## Reader Table Body -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.ResultFacts Itasca.Wasm2.Visitor
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

 theorem table_label_bytes (before after : code.BodyState) (data : Slice U8)
    (depth : U32) (types : signature.ResultType)
    (accepted : code.read_label_info before data = .ok (.Ok (depth,types),after)) :
    after.core.vals = before.core.vals ∧ after.core.ctrls = before.core.ctrls ∧
    Leb128.Decoded data before.core.pos depth after.core.pos := by
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
      Leb128.Decoded data st.core.pos depth next.pos ∧
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
      Leb128.Decoded data st.core.pos depth readState.core.pos ∧
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
end Itasca.Runtime.Compiler

end

/-! ## Reader Table Loop -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.ResultFacts Itasca.Wasm2.Visitor
set_option maxHeartbeats 2000000
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
      BrTable.LabelsDecoded data st.core.pos depths defaultStart ∧
      Leb128.Decoded data defaultStart default readState.core.pos ∧
      index.val + depths.length = count.val ∧
      code.mark_unreachable readState.core = .ok final.core ∧
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
        ops {before with budget,table_depths := buffer} final.core default types = .ok (.Ok (),after) := by
  generalize measure : count.val - index.val = n
  induction n using Nat.strong_induction_on generalizing before st index arity with
  | h n ih =>
    unfold code.branch_table_with_loop at accepted
    rw [loop] at accepted
    simp only [tableBody_eq (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
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
      · exact (BrTable.LabelsDecoded.snoc .nil decoded).append remaining
      · simp only [List.length_cons]
        omega
end Itasca.Runtime.Compiler

end

/-! ## Reader Table Wasm2 -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.ResultFacts
set_option maxHeartbeats 2000000
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
      Leb128.Decoded data st.core.pos count first ∧
      code.pop_with_type {st.core with pos := first} .I32 = .ok (.Ok selector,popped) ∧
      buffer.val = before.table_depths.val ++ depths ∧
      BrTable.LabelsDecoded data popped.pos depths defaultStart ∧
      Leb128.Decoded data defaultStart default readState.core.pos ∧
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
end Itasca.Runtime.Compiler

end

end

/-! ## BranchTableSource -/

section

/-!
Canonical independent immediate decoding determines every collected Wasm 2 target and the exact accepted final callback.

Main declarations: `compiler_table_source_wasm2`. A direct consumer is `Compiler.Body.Reader.Control.BranchTableCapacity`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Canonical independent immediate decoding determines every collected Wasm 2
target and the exact accepted final callback. -/
theorem compiler_table_source_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st final : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (shape : Control.Shape st.core) (depths : List U32) (fallback : U32) (next : Usize)
    (encoded : BrTable.Decoded data st.core.pos depths fallback next)
    (accepted : code.branch_table_with (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env before = .ok (.Ok (),final,after)) :
    ∃ budget buffer types,
      buffer.val = before.table_depths.val ++ depths ∧
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
        ops {before with budget,table_depths := buffer} final.core fallback types = .ok (.Ok (),after) := by
  obtain ⟨count,first,selector,popped,actual,default,types,last,readState,budget,buffer,
    countDecoded,popCall,bufferEq,labelsDecoded,defaultDecoded,lengthEq,marked,callback⟩ :=
    compiler_read_br_table ops law before after st final data env accepted
  have movedShape : Control.Shape {st.core with pos := first} := ⟨shape.ordered,shape.bounded⟩
  have poppedSpec := code.pop_with_type.total {st.core with pos := first} .I32 movedShape
  rw [popCall,WP.spec_ok] at poppedSpec
  have position : popped.pos = first := poppedSpec.2.2.1
  rw [position] at labelsDecoded
  have decoded : BrTable.Decoded data st.core.pos actual default readState.core.pos :=
    ⟨count,first,last,countDecoded,lengthEq,labelsDecoded,defaultDecoded⟩
  obtain ⟨rfl,rfl,_⟩ := decoded.unique encoded
  exact ⟨budget,buffer,types,bufferEq,callback⟩
end Itasca.Runtime.Compiler

end

/-! ## BranchTableSuffix -/

section

/-!
A successful suffix check on a live concrete segment determines the exact source types, rather than only their shared slot widths.

Main declarations: `table_suffix_concrete`. A direct consumer is `Compiler.Body.Reader.Control.BranchTableCapacity`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

private theorem concrete_fits_prefix (actual expected : List wasm_types.ValueType)
    (fits : Wasm2.Fits false (actual.map code.StackType.Val) expected) :
    ∃ rest, actual=expected++rest := by
  induction expected generalizing actual with
  | nil => exact ⟨actual,rfl⟩
  | cons expected tail ih =>
    cases actual with
    | nil => simp [Wasm2.Fits] at fits
    | cons actual rest =>
      have same : expected=actual := Translate.valueType_injective fits.1
      subst actual
      obtain ⟨remaining,rfl⟩ := ih rest fits.2
      exact ⟨remaining,rfl⟩

/-- A successful suffix check on a live concrete segment determines the exact
source types, rather than only their shared slot widths. -/
theorem table_suffix_concrete (st : code.OpIterState) (outer segment : List code.StackType)
    (expected : List wasm_types.ValueType) (values : st.vals.val=outer++segment)
    (base : (Control.base st).val=outer.length)
    (monomorphic : Control.polymorphic st=false) (known : ConcreteStack segment)
    (suffix : Wasm2.Suffix st expected) :
    ∃ front, Sequence.stackTypes segment=front++expected.map Translate.valueType := by
  obtain ⟨actual,rfl⟩ := (concrete_stack_iff segment).mp known
  have fits : Wasm2.Fits false (actual.reverse.map code.StackType.Val) expected.reverse := by
    simpa only [Wasm2.Suffix,values,base,List.drop_left,monomorphic,List.map_reverse] using suffix
  obtain ⟨rest,same⟩ := concrete_fits_prefix actual.reverse expected.reverse fits
  have actualEq : actual=rest.reverse++expected := by
    have reversed := congrArg List.reverse same
    simpa only [List.reverse_reverse,List.reverse_append] using reversed
  refine ⟨rest.reverse.map Translate.valueType,?_⟩
  simp only [Sequence.stackTypes,List.map_map,Function.comp_def,actualEq,List.map_append]
end Itasca.Runtime.Compiler

end

/-! ## BranchTableEffects -/

section

/-!
Complete instruction effects at reader boundaries, after the private label buffer has been consumed. Applies to live and unreachable paths.

Main declarations: `TableReaderEffect`. A direct consumer is `Compiler.Body.Reader.Control.BranchTableIndexed`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Complete instruction effects at reader boundaries, after the private label
buffer has been consumed. Applies to live and unreachable paths. -/
def TableReaderEffect {A : Type} (before after : runtime.compiler.FunctionCompiler A)
    (position : Usize) (depths : List U32) : Prop :=
  TableFixed before after ∧ SourceProgress before after ∧ after.next_source=position ∧
  CompilerTableBoundary after ∧ after.reachable=false ∧
  after.function.code.val.length≤before.function.code.val.length+1+2*(depths.length+1)

theorem compiler_reader_table_effect_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st final : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (shape : Control.Shape st.core) (depths : List U32) (fallback : U32) (next : Usize)
    (encoded : BrTable.Decoded data st.core.pos depths fallback next)
    (boundary : CompilerTableBoundary before)
    (accepted : code.branch_table_with (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env before=.ok (.Ok (),final,after)) :
    TableReaderEffect before after final.core.pos depths := by
  obtain ⟨budget,buffer,types,bufferEq,callback⟩ := compiler_table_source_wasm2 ops law before after st final data env
    shape depths fallback next encoded accepted
  obtain ⟨fixed,source,cursor,afterBoundary,dead,growth⟩ := compiler_br_table_effects ops law
    {before with budget,table_depths := buffer} after final.core fallback types boundary.targets callback
  refine ⟨⟨⟨fixed.stable.metadata,fixed.stable.capacity⟩,fixed.controls,fixed.indirect,fixed.simd,fixed.constants⟩,
    source,cursor,afterBoundary,dead,?_⟩
  simpa only [bufferEq,boundary.depths,List.nil_append] using growth

end Itasca.Runtime.Compiler

end

/-! ## BranchTableTargetsWasm2 -/

section

/-!
Canonical accepted target checks retain a suffix obligation for every label, independently of the compiler visitor's implementation.

Main declarations: `reader_table_targets_wasm2`. A direct consumer is `Compiler.Body.Reader.Control.BranchTableInputsWasm2`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.ResultFacts
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-- Canonical accepted target checks retain a suffix obligation for every
label, independently of the compiler visitor's implementation. -/
theorem reader_table_targets_wasm2 {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (st final : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (cs : List code.Ctrl) (c : code.Ctrl)
    (controls : st.core.ctrls.val=cs++[c]) (shape : Control.Shape st.core)
    (accepted : code.branch_table_with visitor st data env before=.ok (.Ok (),final,after)) :
    ∃ (count : U32) (first : Usize) (selector : code.StackType) (popped : code.OpIterState)
      (all : List U32) (arity : Usize),
      Leb128.Decoded data st.core.pos count first ∧
      code.pop_with_type {st.core with pos := first} .I32=.ok (.Ok selector,popped) ∧
      popped.ctrls=st.core.ctrls ∧ popped.pos=first ∧
      all.length=count.val+1 ∧ BrTable.LabelsDecoded data first all final.core.pos ∧
      Wasm2.TableTargets env ⟨popped⟩ all (some arity) := by
  obtain ⟨unit,erased⟩ := code.branch_table_with.accepted_transfer visitor
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_accepts st data env before () final after accepted
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
      (show Control.Shape {st.core with pos := first} from ⟨shape.ordered,shape.bounded⟩)
    rw [popCall,WP.spec_ok] at popSpec
    dsimp only at popSpec
    cases reply with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok selector =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,uncurry_apply_pair] at rest
      have loopCall : Wasm2.branchTableLoop popped data env count none 0#u32=.ok (.Ok (),final) := by
        simp only [Wasm2.branchTableLoop,rest,bind_ok,uncurry_apply_pair]
      have checked := Wasm2.branchTableLoop.spec ⟨popped⟩ data env count cs c
        (by simpa only [popSpec.2.1] using controls) popSpec.1
      rw [loopCall,WP.spec_ok] at checked
      obtain ⟨all,arity,length,decoded,targets,_,_,_⟩ := checked rfl
      exact ⟨count,first,selector,popped,all,arity,readSpec,popCall,popSpec.2.1,popSpec.2.2.1,
        length,by simpa only [popSpec.2.2.1] using decoded,targets⟩
end Itasca.Runtime.Compiler

end

/-! ## BranchTableInputsWasm2 -/

section

/-!
Source scopes and input signatures of decoded br_table reader steps.
-/

/-! ## Reader Table Scopes Wasm2 -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Canonical target checks and the saved source zipper discharge every static
branch-table operand obligation on a live path. -/
theorem reader_table_scopes_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {parents current}
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm2.Frames.Saved.vals))
    (chain : SourceEntryChain parents current) (entered : current.entered=true)
    (popped : code.OpIterState) (segment : List code.StackType)
    (values : popped.vals.val=(p.parents.map Wasm2.Frames.Saved.vals).flatten++segment)
    (controls : popped.ctrls=st.core.ctrls) (known : ConcreteStack segment)
    (monomorphic : p.current.ctrl.polymorphic_base=false)
    (depths : List U32) (arity : Option Usize)
    (targets : Wasm2.TableTargets env ⟨popped⟩ depths arity) :
    TableOperandScopes (parents++[current]) (Sequence.stackTypes popped.vals.val) depths := by
  intro depth member
  obtain ⟨view,types,n,selected,resolved,_,_,suffix⟩ := targets depth member
  have blocks : (code.BodyState.mk popped).blocks=st.blocks := code.BodyState.blocks_eq_of_ctrls controls
  have originalSelected : Wasm2.labelAt st depth.val=some view := by
    simpa only [Wasm2.labelAt,blocks,controls] using selected
  obtain ⟨scope,actual,scopeAt,actualResolved,branchTypes⟩ := same.label p.opened depth.val view originalSelected
  have typeEq : actual=types := by rw [resolved] at actualResolved; exact Option.some.inj actualResolved.symm
  subst actual
  obtain ⟨C,outer,spine,header,base,typed,savedControls,_,originalValues⟩ := p.opened
  have outerEq : outer=(p.parents.map Wasm2.Frames.Saved.vals).flatten := by
    simpa only [List.flatMap_def] using wasm2_spine_values spine
  have poppedBase : (Control.base popped).val=(p.parents.map Wasm2.Frames.Saved.vals).flatten.length := by
    simpa [Control.base,controls,savedControls,outerEq] using base
  have poppedMono : Control.polymorphic popped=false := by
    simpa [Control.polymorphic,controls,savedControls] using monomorphic
  obtain ⟨front,arguments⟩ := table_suffix_concrete popped _ segment types values poppedBase poppedMono known suffix
  obtain ⟨discarded,whole⟩ := fronts.branch depth.val scope scopeAt segment front
    (by simpa only [branchTypes] using arguments)
  have selected' : (parents++[current]).reverse[depth.val]?=some scope := by
    simpa only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.singleton_append] using scopeAt
  refine ⟨scope,discarded,selected',chain.all_entered entered scope ?_,?_⟩
  · simpa only [List.mem_reverse] using List.mem_of_getElem? selected'
  · simpa only [values] using whole
end Itasca.Runtime.Compiler

end

/-! ## Reader Table Inputs Wasm2 -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- Every live canonical Wasm 2 BR_TABLE read supplies the source scope and
operand suffix certificate required by actual table lowering. -/
theorem reader_table_inputs_wasm2 {V : Type} (visitor : code.OpVisitor V)
    {data env locals index st} (p : Wasm2.Pending data env locals index st)
    {parents current}
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm2.Frames.Saved.vals))
    (chain : SourceEntryChain parents current) (entered : current.entered=true)
    (known : ConcreteStack st.core.vals.val)
    (monomorphic : p.current.ctrl.polymorphic_base=false)
    (before after : V) (final : code.BodyState) (depths : List U32) (fallback : U32) (next : Usize)
    (encoded : BrTable.Decoded data st.core.pos depths fallback next)
    (accepted : code.branch_table_with visitor st data env before=.ok (.Ok (),final,after)) :
    ∃ stack, Sequence.stackTypes st.core.vals.val=stack++[.I32] ∧
      TableOperandScopes (parents++[current]) stack (depths++[fallback]) := by
  obtain ⟨C,outer,spine,header,base,typed,controls,_,values⟩ := p.opened
  obtain ⟨count,first,selector,popped,all,arity,countDecoded,popCall,popControls,popPos,
    countEq,labelsDecoded,targets⟩ := reader_table_targets_wasm2 visitor before after st final data env
      _ p.current.ctrl controls p.opened.shape.core accepted
  obtain ⟨sourceCount,sourceFirst,defaultStart,countSource,lengthSource,labelsSource,defaultSource⟩ := encoded
  obtain ⟨rfl,rfl⟩ := countDecoded.unique countSource
  have allEq : all=depths++[fallback] := (labelsDecoded.unique (labelsSource.snoc defaultSource)
    (by simp only [List.length_append,List.length_singleton]; omega)).1
  rw [allEq] at targets
  have wholeKnown : ConcreteStack (outer++p.current.vals) := values ▸ known
  have segmentKnown := (concrete_stack_append.mp wholeKnown).2
  have popSpec := code.pop_with_type.segment {st.core with pos := first} outer p.current.vals .I32
    values (by simpa [Control.base,controls] using base)
  rw [popCall,WP.spec_ok] at popSpec
  obtain ⟨_,_,remaining,poppedValues,popEffect⟩ := popSpec
  dsimp only at poppedValues popEffect
  have poly : Control.polymorphic {st.core with pos := first}=false := by
    simpa [Control.polymorphic,controls] using monomorphic
  rw [poly] at popEffect
  have segmentEq := typed_pop_exact segmentKnown popEffect
  have remainingKnown := (concrete_stack_append.mp (segmentEq ▸ segmentKnown)).1
  have outerEq : outer=(p.parents.map Wasm2.Frames.Saved.vals).flatten := by
    simpa only [List.flatMap_def] using wasm2_spine_values spine
  have scopes := reader_table_scopes_wasm2 p same fronts chain entered popped remaining
    (by simpa only [outerEq] using poppedValues) popControls remainingKnown monomorphic
    (depths++[fallback]) (some arity) targets
  refine ⟨Sequence.stackTypes popped.vals.val,?_,scopes⟩
  simp only [values,segmentEq,poppedValues,Sequence.stackTypes,List.map_append,List.map_cons,List.map_nil,
    Translate.valueType,List.append_assoc]
end Itasca.Runtime.Compiler

end

end

/-! ## BranchTablePost -/

section

/-!
The postcondition of a br_table reader step.

Main declarations: `reader_table_post_wasm2`. A direct consumer is `Compiler.Body.Reader.Control.BranchTableIndexed`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

theorem reader_table_post_wasm2 {V : Type} (visitor : code.OpVisitor V)
    {data env locals index st} (p : Wasm2.Pending data env locals index st)
    (before after : V) (final : code.BodyState) (depths : List U32) (fallback : U32) (next : Usize)
    (byte : data.val[p.start.val]'p.inbounds=0x0e#u8)
    (encoded : BrTable.Decoded data st.core.pos depths fallback next)
    (accepted : code.branch_table_with visitor st data env before=.ok (.Ok (),final,after)) :
    Wasm2.ReaderPost p final.core (BrTable.instruction depths fallback) true [] := by
  obtain ⟨unit,empty⟩ := code.branch_table_with.accepted_transfer visitor
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_accepts st data env before () final after accepted
  cases unit
  have erased : code.branch_table st data env =.ok (.Ok (),final) := by
    simp only [code.branch_table,empty,bind_ok,uncurry_apply_pair]
  have effect := p.branch_table_reader byte
  rw [erased, WP.spec_ok] at effect
  obtain ⟨actualDepths, actual, decoded, post⟩ := effect rfl
  obtain ⟨rfl, rfl, _⟩ := decoded.unique encoded
  exact post

end Itasca.Runtime.Compiler

end

/-! ## ControlEffects -/

section

/-!
Every successful structured-control reader step is one control compiler
callback with `ControlEffects`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

theorem reader_block_effects_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 2#u8 before = .ok (.Ok (), out, after)) :
    ControlEffects before after out.core := by
  rw [Wasm2.CallbackTrace.dispatch_block] at accepted
  obtain ⟨value, _, called⟩ := Wasm2.CallbackTrace.bodyRun.accepted _ _ _ _ _ _ accepted
  exact compiler_block_effects ops law before after out.core value called

theorem reader_loop_effects_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 3#u8 before = .ok (.Ok (), out, after)) :
    ControlEffects before after out.core := by
  rw [Wasm2.CallbackTrace.dispatch_loop] at accepted
  obtain ⟨value, _, called⟩ := Wasm2.CallbackTrace.bodyRun.accepted _ _ _ _ _ _ accepted
  exact compiler_loop_effects ops law before after out.core value called

theorem reader_if_effects_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 4#u8 before = .ok (.Ok (), out, after)) :
    ControlEffects before after out.core := by
  rw [Wasm2.CallbackTrace.dispatch_if] at accepted
  obtain ⟨value, _, called⟩ := Wasm2.CallbackTrace.bodyRun.accepted _ _ _ _ _ _ accepted
  exact compiler_if_effects ops law before after out.core value called

theorem reader_else_effects_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 5#u8 before = .ok (.Ok (), out, after)) :
    ControlEffects before after out.core := by
  rw [Wasm2.CallbackTrace.dispatch_else] at accepted
  obtain ⟨value, _, called⟩ := Wasm2.CallbackTrace.bodyRun.accepted _ _ _ _ _ _ accepted
  exact compiler_else_effects ops law before after out.core value.2 called

theorem reader_end_effects_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 11#u8 before = .ok (.Ok (), out, after)) :
    ControlEffects before after out.core := by
  rw [Wasm2.CallbackTrace.dispatch_end] at accepted
  obtain ⟨value, _, called⟩ := Wasm2.CallbackTrace.bodyRun.accepted _ _ _ _ _ _ accepted
  exact compiler_end_effects ops law before after out.core value.1 value.2 called

theorem reader_br_effects_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 12#u8 before = .ok (.Ok (), out, after)) :
    ControlEffects before after out.core := by
  rw [Wasm2.CallbackTrace.dispatch_br] at accepted
  obtain ⟨value, _, called⟩ := Wasm2.CallbackTrace.bodyRun.accepted _ _ _ _ _ _ accepted
  exact compiler_br_effects ops law before after out.core value.1 value.2 called

theorem reader_br_if_effects_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 13#u8 before = .ok (.Ok (), out, after)) :
    ControlEffects before after out.core := by
  rw [Wasm2.CallbackTrace.dispatch_br_if] at accepted
  obtain ⟨value, _, called⟩ := Wasm2.CallbackTrace.bodyRun.accepted _ _ _ _ _ _ accepted
  exact compiler_br_if_effects ops law before after out.core value.1 value.2 called

theorem reader_control_effects_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
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
      exact reader_block_effects_wasm2 ops law before after st out data env ctx index accepted
    · obtain rfl : opcode = 3#u8 := (UScalar.eq_equiv _ _).mpr h
      exact reader_loop_effects_wasm2 ops law before after st out data env ctx index accepted
    · obtain rfl : opcode = 4#u8 := (UScalar.eq_equiv _ _).mpr h
      exact reader_if_effects_wasm2 ops law before after st out data env ctx index accepted
    · obtain rfl : opcode = 12#u8 := (UScalar.eq_equiv _ _).mpr h
      exact reader_br_effects_wasm2 ops law before after st out data env ctx index accepted
    · obtain rfl : opcode = 13#u8 := (UScalar.eq_equiv _ _).mpr h
      exact reader_br_if_effects_wasm2 ops law before after st out data env ctx index accepted
  · exact reader_else_effects_wasm2 ops law before after st out data env ctx index accepted
  · exact reader_end_effects_wasm2 ops law before after st out data env ctx index accepted
end Itasca.Runtime.Compiler

end
