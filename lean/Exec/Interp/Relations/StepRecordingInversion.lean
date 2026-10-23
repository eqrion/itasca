import Exec.Interp.Relations.StepRecordingLookup
import Exec.Code.Body.Relations.Common.RecordingEmission
namespace Exec.Interp
open Aeneas Aeneas.Std

theorem hostInstructionAddress_callTag {M : Type} (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (instruction : runtime.bytecode.Instr)
    (address : runtime.FuncAddr) (selected : hostInstructionAddress exec store raw inst compiled instruction=some address) :
    Code.callTag instruction≠0 := by
  cases instruction <;> first | (simp [Code.callTag]; done) | (simp only [hostInstructionAddress,Bind.bind,Option.bind] at selected; cases selected)

theorem hostInstructionAddress_direct_inv {M : Type} (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (index offset : U32)
    (address : runtime.FuncAddr) (selected : hostInstructionAddress exec store raw inst compiled (.Call index offset)=some address) :
    ∃function host, inst.funcs.val[index.val]?=some address ∧
      store.funcs.val[address.index.val]?=some function ∧ function.code=.Host host := by
  cases addressAt : inst.funcs.val[index.val]? with
  | none => simp [hostInstructionAddress,addressAt,Bind.bind,Option.bind] at selected
  | some actual =>
    cases functionAt : store.funcs.val[actual.index.val]? with
    | none => simp [hostInstructionAddress,addressAt,functionAt,Bind.bind,Option.bind] at selected
    | some function =>
      cases hostCode : function.code with
      | Wasm => simp [hostInstructionAddress,addressAt,functionAt,hostCode,Bind.bind,Option.bind] at selected
      | Host host =>
        have same : actual=address := by simpa [hostInstructionAddress,addressAt,functionAt,hostCode,Bind.bind,Option.bind] using selected
        subst actual
        exact ⟨function,host,rfl,functionAt,hostCode⟩

theorem hostInstructionAddress_indirect_inv {M : Type} (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (entry selector offset table type : U32)
    (tableAddress : runtime.TableAddr) (object : runtime.store.TableInst) (word : U64) (signature : Usize)
    (pairAt : compiled.indirect.val[entry.val]?=some (table,type))
    (tableAt : inst.tables.val[table.val]?=some tableAddress)
    (objectAt : store.tables.val[tableAddress.index.val]?=some object)
    (wordAt : exec.slots.val[raw.base.val+selector.val]?=some word)
    (signatureAt : inst.types.val[type.val]?=some signature)
    (address : runtime.FuncAddr) (selected : hostInstructionAddress exec store raw inst compiled (.CallIndirect entry selector offset)=some address) :
    ∃ reference function host,
      object.elements.val[(UScalar.cast .U32 word).val]?=some reference ∧ reference≠0#u64 ∧
      (UScalar.cast .Usize reference).val=address.index.val+1 ∧ address.store=store.id ∧
      store.funcs.val[address.index.val]?=some function ∧ function.signature=signature ∧ function.code=.Host host := by
  simp only [hostInstructionAddress,pairAt,Bind.bind,Option.bind,tableAt,objectAt,wordAt] at selected
  cases referenceAt : object.elements.val[(UScalar.cast .U32 word).val]? with
  | none => simp only [referenceAt,Option.bind] at selected; cases selected
  | some reference =>
    simp only [referenceAt] at selected
    split at selected
    · simp at selected
    · rename_i nonzero
      split at selected
      · simp at selected
      · rename_i positive
        let target : Usize := UScalar.ofNatCore ((UScalar.cast .Usize reference).val-1) (by have := (UScalar.cast .Usize reference).hBounds;omega)
        change (Option.bind (store.funcs.val[target.val]?) (fun (function : runtime.store.FuncInst) =>
          Option.bind (inst.types.val[type.val]?) (fun wanted => if function.signature=wanted then
            Option.bind (store.funcs.val[target.val]?) (fun (function : runtime.store.FuncInst) =>
              match function.code with | .Host _ => some (⟨store.id,target⟩ : runtime.FuncAddr) | .Wasm .. => none)
            else none)))=some address at selected
        cases functionAt : store.funcs.val[target.val]? with
        | none => simp [functionAt] at selected
        | some function =>
          simp only [functionAt,Option.bind,signatureAt] at selected
          split at selected
          · rename_i same
            cases hostCode : function.code with
            | Wasm => simp [hostCode] at selected
            | Host host =>
              have equal : (⟨store.id,target⟩ : runtime.FuncAddr)=address := by simpa [hostCode] using selected
              subst address
              refine ⟨reference,function,host,rfl,nonzero,?_,rfl,functionAt,same,hostCode⟩
              change (UScalar.cast .Usize reference).val=(UScalar.cast .Usize reference).val-1+1
              omega
          · simp at selected
theorem hostStepAddress_instruction {M : Type} (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (last : index.val+1=exec.frames.length) (frameAt : exec.frames.val[index.val]?=some raw)
    (instanceAt : store.instances.val[raw.instance.val]?=some inst)
    (compiledAt : inst.module.functions.val[raw.function.val]?=some compiled)
    (address : runtime.FuncAddr) (selected : hostStepAddress exec store=some address) :
    ∃instruction, compiled.code.val[raw.pc.val]?=some instruction ∧
      hostInstructionAddress exec store raw inst compiled instruction=some address := by
  have indexEq : exec.frames.length-1=index.val := by omega
  simp only [hostStepAddress,indexEq,frameAt,instanceAt,compiledAt,Bind.bind,Option.bind] at selected
  cases found : compiled.code.val[raw.pc.val]? with
  | none => simp [found] at selected
  | some instruction => exact ⟨instruction,rfl,by simpa only [found,Option.bind] using selected⟩
end Exec.Interp
