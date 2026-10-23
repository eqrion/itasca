import Exec.Interp.Relations.StepRecording
namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt

theorem hostStepAddress_at {M : Type} (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction) (instruction : runtime.bytecode.Instr)
    (last : index.val+1=exec.frames.length) (frameAt : exec.frames.val[index.val]?=some raw)
    (instanceAt : store.instances.val[raw.instance.val]?=some inst)
    (compiledAt : inst.module.functions.val[raw.function.val]?=some compiled)
    (fetched : compiled.code.val[raw.pc.val]?=some instruction) :
    hostStepAddress exec store = hostInstructionAddress exec store raw inst compiled instruction := by
  have indexEq : exec.frames.length-1=index.val := by omega
  simp [hostStepAddress,indexEq,frameAt,instanceAt,compiledAt,fetched,Bind.bind,Option.bind]

theorem hostInstructionAddress_direct {M : Type} (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (index offset : U32)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst) (host : U64)
    (addressAt : inst.funcs.val[index.val]?=some address)
    (functionAt : store.funcs.val[address.index.val]?=some function) (hostCode : function.code=.Host host) :
    hostInstructionAddress exec store raw inst compiled (.Call index offset)=some address := by
  simp [hostInstructionAddress,addressAt,Bind.bind,Option.bind,functionAt,hostCode]

theorem hostInstructionAddress_indirect {M : Type} (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (entry selector offset table type : U32)
    (tableAddress : runtime.TableAddr) (object : runtime.store.TableInst) (word reference : U64)
    (address : Usize) (function : runtime.store.FuncInst) (signature : Usize) (host : U64)
    (pairAt : compiled.indirect.val[entry.val]?=some (table,type))
    (tableAt : inst.tables.val[table.val]?=some tableAddress)
    (objectAt : store.tables.val[tableAddress.index.val]?=some object)
    (wordAt : exec.slots.val[raw.base.val+selector.val]?=some word)
    (referenceAt : object.elements.val[(UScalar.cast .U32 word).val]?=some reference)
    (nonzero : reference≠0#u64) (indexEq : (UScalar.cast .Usize reference).val=address.val+1)
    (functionAt : store.funcs.val[address.val]?=some function)
    (signatureAt : inst.types.val[type.val]?=some signature) (same : function.signature=signature)
    (hostCode : function.code=.Host host) :
    hostInstructionAddress exec store raw inst compiled (.CallIndirect entry selector offset)=some ⟨store.id,address⟩ := by
  have nz : ¬(UScalar.cast .Usize reference).val=0 := by omega
  simp only [hostInstructionAddress,pairAt,Bind.bind,Option.bind,tableAt,objectAt,wordAt,referenceAt,nonzero,ite_false,nz]
  have sub : (UScalar.cast .Usize reference).val-1=address.val := by omega
  have equal (bound : (UScalar.cast .Usize reference).val-1<2^UScalarTy.Usize.numBits) :
      UScalar.ofNatCore ((UScalar.cast .Usize reference).val-1) bound=address := by
    apply UScalar.eq_of_val_eq
    simpa only [UScalar.ofNatCore_val_eq] using sub
  simp only [equal,functionAt,Bind.bind,Option.bind,signatureAt,same,ite_true,hostCode]
end Exec.Interp
