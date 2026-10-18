import Exec.Code.Body.Callbacks.Common.CompilerPrefix
import Exec.Code.Local.Control.Calls.UniversalCall
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem CompilerPrefix.ordinary_empty {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals parents current raw position nextRaw nextPosition instruction output}
    (invariant : CompilerPrefix initial before types functions returns locals parents current raw position)
    (reachable : before.reachable = true)
    (ordinary : CompilerOrdinaryStable before after)
    (lowered : TypedLoweredEmpty before after nextRaw output)
    (emission : LinearEmission locals (Sequence.stackTypes raw) instruction [] output)
    (sources : SourceProgress before after) (consumed : position < nextPosition)
    (cursor : after.next_source.val ≤ nextPosition) :
    CompilerPrefix initial after types functions returns locals parents (current.advance instruction) nextRaw nextPosition := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  have code : after.function.code.val = before.function.code.val ++ [] := by simpa using congrArg (fun code => code.val) lowered.1.1
  have frames := (invariant.frames.extend (congrArg (fun fs => fs.val) ordinary.frames) []
    code (by rw [ordinary.controls])).advance instruction
  have next := lowered.1.universal_advance ordinary.frames retained emission
  have growth : after.function.code.val.length ≤ before.function.code.val.length + 3 := by rw [lowered.1.1]; omega
  refine ⟨invariant.metadata.trans ordinary.stable, frames, invariant.entryChain.advance instruction,
    (by simpa only [ordinary.frames] using invariant.dormant), invariant.conditions.advance instruction, lowered.2.concrete,
    .live (lowered.1.2.2.2.1.trans reachable) entered ?_,
    invariant.arms.append retained.sites [] instruction code ordinary.frames,
    sources.aligned invariant.sources, invariant.codeBudget.advance growth consumed,
    (invariant.controlBudget.transport (congrArg (fun maps => maps.val.length) ordinary.controls)
      (by rw [ordinary.frames])).advance (Nat.le_of_lt consumed), cursor⟩
  simpa only [lowered.2.decoded] using next

theorem CompilerPrefix.call {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals parents current raw position nextRaw nextPosition front params results index base}
    (invariant : CompilerPrefix initial before types functions returns locals parents current raw position)
    (reachable : before.reachable = true)
    (ordinary : CompilerOrdinaryStable before after)
    (lowered : TypedLowered before after nextRaw (.Call index base) (front ++ results))
    (stack : Sequence.stackTypes raw = front ++ params)
    (signature : functions[index.val]? = some ⟨.mk_list params, .mk_list results⟩)
    (arguments : base.val = slots locals + slots front)
    (sources : SourceProgress before after) (consumed : position < nextPosition)
    (cursor : after.next_source.val ≤ nextPosition) :
    CompilerPrefix initial after types functions returns locals parents
      (current.advance (.CALL (.mk_uN index.val))) nextRaw nextPosition := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  have frames := (invariant.frames.extend (congrArg (fun fs => fs.val) ordinary.frames) [.Call index base]
    lowered.1.1 (by rw [ordinary.controls])).advance (.CALL (.mk_uN index.val))
  have next := lowered.1.universal_call ordinary.frames (stack ▸ retained) signature arguments
  have growth : after.function.code.val.length ≤ before.function.code.val.length + 3 := by
    rw [lowered.1.1, List.length_append, List.length_singleton]; omega
  refine ⟨invariant.metadata.trans ordinary.stable, frames, invariant.entryChain.advance (.CALL (.mk_uN index.val)),
    (by simpa only [ordinary.frames] using invariant.dormant), invariant.conditions.advance (.CALL (.mk_uN index.val)), lowered.2.concrete,
    .live (lowered.1.2.2.2.1.trans reachable) entered ?_,
    invariant.arms.append retained.sites [.Call index base] (.CALL (.mk_uN index.val)) lowered.1.1 ordinary.frames,
    sources.aligned invariant.sources, invariant.codeBudget.advance growth consumed,
    (invariant.controlBudget.transport (congrArg (fun maps => maps.val.length) ordinary.controls)
      (by rw [ordinary.frames])).advance (Nat.le_of_lt consumed), cursor⟩
  simpa only [lowered.2.decoded] using next

end Exec.Code
