import Itasca.Wasm2.Scalar.MemoryReader
import Itasca.Runtime.Compiler.Body.Reader.Replay.Post
import Itasca.Runtime.Compiler.Body.Reader.Memory.MemoryStacks
import Itasca.Runtime.Compiler.Local.Relations.Memory.MemoryOpcode

/-!
Accepted scalar-memory instructions and decoded opcode facts, used by safety, emission and acceptance.
-/

/-! ## Reader Memory -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- The actual memory reader selected by the independently defined binary row. -/
def memoryReader (operation : MemoryMeaning.Operation) (st : code.OpIterState) (data : Slice U8) (env : module.Env) :=
  if operation.store then code.read_store st data env operation.ty operation.naturalAlign
  else code.read_load st data env operation.ty operation.naturalAlign

theorem reader_memory_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {V : Type} (visitor : code.OpVisitor V)
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

def memoryRawType : numtype → types.ValueType
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
