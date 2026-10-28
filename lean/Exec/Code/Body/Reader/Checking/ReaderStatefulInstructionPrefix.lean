import Exec.Code.Body.Control.Table.StructuredCompilerPrefix
import Exec.Code.Body.Reader.Common.StatefulReaderEmission
import Exec.Code.Body.Relations.Common.ExecutableInstructionPrefix
import Exec.Code.Local.Checking.BranchCallbackInstructionPrefix
import Exec.Code.Local.Checking.BranchCallbackExitSlots
import Exec.Code.Local.Callbacks.Table.CompilerPairTableAppend
import Exec.Code.Local.Relations.Table.StatefulAuxiliaryTables
import Exec.Code.Body.Control.Table.CumulativeTableExclusion

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Source-typed stateful metadata readers check every newly emitted word and
retain both pending instruction checks and the slots of recorded exits. -/
theorem StatefulReaderPost.instruction_prefix {jumpTables : List U32} {data env sourceLocals index st}
    {p : Wasm2.Pending data env .Wasm2 sourceLocals index st} {out : code.OpIterState} {op : Abs.Stateful.Instruction}
    (post : StatefulReaderPost p out op) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (C : context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (matched : EnvTranslation.Matches env ⟨sourceLocals,p.ft.results⟩ C)
    (contextLocals : C.LOCALS = locals)
    (a b : U32) (arguments : StatefulArguments op a b)
    (callback : runtime.compiler.lower.FunctionCompiler.op ops before out (statefulOpcode op) a b 0#u128 = .ok (.Ok (),after))
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val+data.length ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  cases reachable : before.reachable with
  | false =>
    have checked := compiler_dead_op_open_instructions ops law before after out (statefulOpcode op) a b 0#u128
      reachable held callback
    unfold runtime.compiler.lower.FunctionCompiler.op at callback
    rw [if_neg (by simp [reachable])] at callback
    exact ⟨checked,compiler_observe_exit_slots ops law before after out exits callback⟩
  | true =>
    obtain ⟨entered,retained⟩ := invariant.live reachable
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits,sourceFits,_,_⟩ := invariant.capacities bound
    have coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max := by
      have cursor := invariant.cursor
      have position := p.inbounds
      omega
    obtain ⟨ordinary,sources,cursor,⟨extra,pairs⟩,values,emitted,output,reader,lowered,emission⟩ :=
      post.emission ops law before after C a b arguments callback matched
        (contextLocals.trans retained.localsEq.symm) (invariant.known reachable) (monomorphic reachable)
        retained.layout reachable codeFits sourceFits coordinateFits
    have tables := compiler_tables_pair_append before.function after.function extra pairs
      (compiler_stateful_auxiliary_tables ops law before after out op a b (.Ok ()) callback)
    have growth := instruction_check_extends_of_tables_append before.function after.function _ tables
      ordinary.capacity (by change before.function.code.val.length ≤ after.function.code.val.length; rw [lowered.1.1,List.length_append,List.length_singleton]; omega)
    exact ⟨lowered.1.executableInstructionPrefix retained.layout reachable (contextLocals.trans retained.localsEq.symm)
      (.stateful emission) emission.not_branchTable growth held ordinary.frames,
      exits.retained (congrArg alloc.vec.Vec.val ordinary.frames) ordinary.capacity⟩

end Itasca.Runtime.Code
