import Itasca.Runtime.Interp.Memory.MemorySize
import Itasca.Runtime.Interp.Relations.ReferenceSource
import Itasca.Runtime.SourceMachine.Memory.Decode
import Itasca.Runtime.Interp.Relations.FrameStoreMetadata
import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission
import Itasca.Runtime.Compiler.Local.Control.Segments.Structured
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredComposition
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels
import Itasca.Runtime.Interp.Control.StructuredLinear
import Itasca.Runtime.SourceMachine.Measure
import Itasca.Runtime.SourceMachine.Numeric.Decode
import Itasca.Runtime.Interp.Relations.Regions
import Itasca.Runtime.Compiler.Local.Relations.Memory.MemoryOpcode
import Itasca.Runtime.SourceMachine.Core.Trap
import Itasca.Runtime.Interp.Relations.SuspendedPoint
import Itasca.Runtime.SourceMachine.Core.SelectPositive

/-!
Sections, each formerly its own module: MemoryDescriptor, MemoryMutation, MemoryCoreEmission, MemoryValueSlots, MemoryCore, MemoryCoreStore, MemoryCoreOperandBounds, MemoryCoreResult, MemoryCoreStep.
-/

/-! ## MemoryDescriptor -/

section

namespace Itasca.Runtime.Interp.MemoryDescriptor
open Aeneas Aeneas.Std SpecExt
open Itasca.Runtime.Store

/-- The abstract indexed widths and the independent source helper enumerate the
same legal packed instructions. No execution relation is assumed by this map. -/
def packed {ty : Inn} (width : SourceMachine.Memory.PackedWidth ty) : Spec.PackedMemory :=
  match ty,width with
  | .I32,.byte => .i32x8
  | .I32,.half => .i32x16
  | .I64,.byte => .i64x8
  | .I64,.half => .i64x16
  | .I64,.word => .i64x32

theorem packed_bytes {ty : Inn} (width : SourceMachine.Memory.PackedWidth ty) :
    (packed width).bytes = width.bits / 8 := by cases ty <;> cases width <;> rfl

def loadOpcode : SourceMachine.Memory.Load → U16
  | .full ty => numericLoadOpcode ty
  | .packed _ width sign => PackedMemory.loadOpcode (packed width) sign

def storeOpcode : SourceMachine.Memory.Store → U16
  | .full ty => numericStoreOpcode ty
  | .packed _ width => PackedMemory.storeOpcode (packed width)

theorem load_width (op : SourceMachine.Memory.Load) : (scalarLoadWidth (loadOpcode op)).val = op.bytes := by
  cases op with
  | full ty => cases ty <;> rfl
  | packed ty width sign => exact (PackedMemory.load_width _ _).trans (packed_bytes width)

theorem store_width (op : SourceMachine.Memory.Store) : (scalarStoreWidth (storeOpcode op)).val = op.bytes := by
  cases op with
  | full ty => cases ty <;> rfl
  | packed ty width => exact (PackedMemory.store_width _).trans (packed_bytes width)

end Itasca.Runtime.Interp.MemoryDescriptor

end

/-! ## MemoryMutation -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt
open Itasca.Runtime.Store

/-- A scalar memory instruction changes only the selected opaque buffer and
retains its byte length. This includes bounds failures whose writeback callback
chooses a different representation of the same bytes. -/
def MemoryMutation {M : Type} (view : M → Slice U8) (before after : runtime.store.Store M)
    (address : runtime.MemoryAddr) (object : runtime.store.MemInst M) : Prop :=
  ∃ buffer, after = {before with memories := before.memories.set address.index {object with buf := buffer}} ∧
    (view buffer).length = (view object.buf).length

theorem MemoryMutation.frame_metadata {M : Type} {view : M → Slice U8}
    {before after : runtime.store.Store M} {address object}
    (mutation : MemoryMutation view before after address object) : FrameStoreMetadata before after := by
  obtain ⟨buffer,rfl,lengthEq⟩ := mutation
  exact ⟨rfl,rfl,rfl,rfl⟩

end Itasca.Runtime.Interp

end

/-! ## MemoryCoreEmission -/

section

namespace Itasca.Runtime.Interp.MemoryDescriptor
open Aeneas Aeneas.Std

theorem load_source_injective (left right : SourceMachine.Memory.Load) (a b : memarg)
    (equal : left.source a = right.source b) : left = right ∧ a = b := by
  cases left with
  | full ty =>
    cases right with
    | full other => simp_all [SourceMachine.Memory.Load.source,SourceMachine.Memory.Load.type,SourceMachine.Memory.Load.operation]
    | packed other width sign => simp [SourceMachine.Memory.Load.source,SourceMachine.Memory.Load.type,SourceMachine.Memory.Load.operation] at equal
  | packed ty width sign =>
    cases right with
    | full other => simp [SourceMachine.Memory.Load.source,SourceMachine.Memory.Load.type,SourceMachine.Memory.Load.operation] at equal
    | packed other width' sign' =>
      cases ty <;> cases other <;> cases width <;> cases width' <;> cases sign <;> cases sign' <;>
        simp_all [SourceMachine.Memory.Load.source,SourceMachine.Memory.Load.type,SourceMachine.Memory.Load.operation,SourceMachine.Memory.PackedWidth.size,SourceMachine.Memory.PackedWidth.bits,numtype_Inn]

theorem store_source_injective (left right : SourceMachine.Memory.Store) (a b : memarg)
    (equal : left.source a = right.source b) : left = right ∧ a = b := by
  cases left with
  | full ty =>
    cases right with
    | full other => simp_all [SourceMachine.Memory.Store.source,SourceMachine.Memory.Store.type,SourceMachine.Memory.Store.operation]
    | packed other width => simp [SourceMachine.Memory.Store.source,SourceMachine.Memory.Store.type,SourceMachine.Memory.Store.operation] at equal
  | packed ty width =>
    cases right with
    | full other => simp [SourceMachine.Memory.Store.source,SourceMachine.Memory.Store.type,SourceMachine.Memory.Store.operation] at equal
    | packed other width' =>
      cases ty <;> cases other <;> cases width <;> cases width' <;>
        simp_all [SourceMachine.Memory.Store.source,SourceMachine.Memory.Store.type,SourceMachine.Memory.Store.operation,SourceMachine.Memory.PackedWidth.size,SourceMachine.Memory.PackedWidth.bits,numtype_Inn]

theorem linear_emission_not_load {locals before after emitted ty packed argument}
    (emission : Compiler.LinearEmission locals before (.LOAD ty packed argument) emitted after) : False := by
  generalize equality : instr.LOAD ty packed argument = instruction at emission
  cases emission with
  | binary stack ty op a b left right => cases op <;> simp [Compiler.IntegerBinary.source] at equality
  | numeric stack op a b left right =>
    have decoded := congrArg SourceMachine.Numeric.decodeInstruction equality
    rw [SourceMachine.Numeric.decode_instruction_source] at decoded
    simp [SourceMachine.Numeric.decodeInstruction] at decoded
  | _ => cases equality

theorem linear_emission_not_store {locals before after emitted ty packed argument}
    (emission : Compiler.LinearEmission locals before (.STORE ty packed argument) emitted after) : False := by
  generalize equality : instr.STORE ty packed argument = instruction at emission
  cases emission with
  | binary stack ty op a b left right => cases op <;> simp [Compiler.IntegerBinary.source] at equality
  | numeric stack op a b left right =>
    have decoded := congrArg SourceMachine.Numeric.decodeInstruction equality
    rw [SourceMachine.Numeric.decode_instruction_source] at decoded
    simp [SourceMachine.Numeric.decodeInstruction] at decoded
  | _ => cases equality

theorem scalar_emission_load_inv {C before after emitted} (op : SourceMachine.Memory.Load) (argument : memarg)
    (emission : Compiler.ScalarEmission C before (op.source argument) emitted after) :
    ∃ stack address offset, before = stack ++ [.I32] ∧
      emitted = [Compiler.memoryLoadInstruction op address address offset] ∧ after = stack ++ [valtype_numtype op.type] ∧
      argument.OFFSET = .mk_uN offset.val ∧ address.val = Compiler.slots C.LOCALS + Compiler.slots stack := by
  generalize equality : op.source argument = instruction at emission
  cases emission with
  | linear pure =>
    rw [←equality] at pure
    exact False.elim (linear_emission_not_load pure)
  | load stack other arg address offset memory available sourceOffset position =>
    obtain ⟨rfl,rfl⟩ := load_source_injective op other argument arg equality
    exact ⟨stack,address,offset,rfl,rfl,rfl,sourceOffset,position⟩
  | float stack other => cases other <;> simp [SourceMachine.Float.Instruction.source,SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source] at equality
  | _ => simp [SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source] at equality

theorem scalar_emission_store_inv {C before after emitted} (op : SourceMachine.Memory.Store) (argument : memarg)
    (emission : Compiler.ScalarEmission C before (op.source argument) emitted after) :
    ∃ stack address value offset, before = stack ++ [.I32,valtype_numtype op.type] ∧
      emitted = [Compiler.memoryStoreInstruction op address value offset] ∧ after = stack ∧
      argument.OFFSET = .mk_uN offset.val ∧ address.val = Compiler.slots C.LOCALS + Compiler.slots stack ∧ value.val = address.val+1 := by
  generalize equality : op.source argument = instruction at emission
  cases emission with
  | linear pure =>
    rw [←equality] at pure
    exact False.elim (linear_emission_not_store pure)
  | store stack other arg address value offset memory available sourceOffset addressPosition valuePosition =>
    obtain ⟨rfl,rfl⟩ := store_source_injective op other argument arg equality
    exact ⟨_,address,value,offset,rfl,rfl,rfl,sourceOffset,addressPosition,valuePosition⟩
  | float stack other => cases other <;> simp [SourceMachine.Float.Instruction.source,SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source] at equality
  | _ => simp [SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source] at equality
end Itasca.Runtime.Interp.MemoryDescriptor

end

/-! ## MemoryValueSlots -/

section

/-!
Scalar memory values represented in machine words. Descriptor-specific bounds connect decoded load values to word encoding and the destination slots.
-/

/-! ## Memory Descriptor Values -/

section

namespace Itasca.Runtime.Interp.MemoryDescriptor
open Aeneas Aeneas.Std SpecExt

 theorem load_word_value (op : SourceMachine.Memory.Load) (bytes : List U8) (start : Nat)
    (inside : start + op.bytes ≤ bytes.length) :
    Store.decodeWords (numericMemoryType op.type)
      (scalarLoadedWord (loadOpcode op) (scalarLoadBytes bytes start 0#u64 0 op.bytes)) 0#u64 =
      op.value (Store.decodeBytes ((bytes.drop start).take op.bytes)) := by
  cases op with
  | full ty =>
    have decoded := numeric_load_word_decodes ty bytes start (by cases ty <;> exact inside)
    cases ty <;> exact decoded
  | packed ty width sign =>
    have decoded := PackedMemory.load_word_decodes (packed width) sign bytes start
      (by simpa only [packed_bytes,SourceMachine.Memory.Load.bytes] using inside)
    cases ty <;> cases width <;> exact decoded

 theorem store_payload (op : SourceMachine.Memory.Store) (word : U64) :
    op.payload (numericStoreValue op.type word) = Builtins.integerBytes op.bytes word.val := by
  cases op with
  | full ty =>
    have payload := numeric_store_value_bytes ty word
    cases ty <;> exact payload
  | packed ty width =>
    cases ty with
    | I32 =>
      cases width <;> simp only [SourceMachine.Memory.Store.payload,SourceMachine.Memory.Store.type,
        numericStoreValue,numtype_Inn,proj_num__0,Option.get!,proj_uN_0,SourceMachine.Memory.PackedWidth.bits,
        Nat.reduceDiv,SourceMachine.Memory.Store.bytes]
      · exact PackedMemory.store_bytes .i32x8 word
      · exact PackedMemory.store_bytes .i32x16 word
    | I64 => cases width <;> rfl

 theorem execute_store_value {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (instanceIndex base : Usize)
    (op : SourceMachine.Memory.Store) (address value offset : U32) (inst : runtime.store.ModuleInst)
    (memoryAddress : runtime.MemoryAddr) (object : runtime.store.MemInst M) (addressWord valueWord : U64)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.memories.val[0]? = some memoryAddress)
    (issued : store.memories.val[memoryAddress.index.val]? = some object)
    (input : exec.slots.val[base.val+address.val]? = some addressWord)
    (inputValue : exec.slots.val[base.val+value.val]? = some valueWord) :
    runtime.interp.execute_store memory exec store instanceIndex base (storeOpcode op) address value offset ⦃ out =>
      MemoryMutation view store out.2 memoryAddress object ∧
      if (UScalar.cast .U32 addressWord).val + offset.val + op.bytes ≤ (view object.buf).length then
        out.1 = .Ok () ∧ Store.decodeStore view code out.2 =
          Spec.memoryPayloadWrite (Store.decodeStore view code store) ⟨[],Store.decodeInstance store inst⟩
            ((UScalar.cast .U32 addressWord).val+offset.val) (op.payload (numericStoreValue op.type valueWord))
      else out.1 = .Err (.Trap .MemoryOutOfBounds) ∧ Store.decodeStore view code out.2 = Store.decodeStore view code store ⦄ := by
  apply WP.spec_mono (execute_store_effect memory view laws exec store instanceIndex base (storeOpcode op) address value offset
    inst memoryAddress object addressWord valueWord found mapped issued input inputValue)
  intro out effect
  obtain ⟨buffer,after,effect⟩ := effect
  unfold ScalarStoreEffect at effect
  rw [store_width] at effect
  split at effect
  · rename_i inside
    obtain ⟨status,written⟩ := effect
    have lengthEq : (view buffer).length = (view object.buf).length := by
      change (view buffer).val.length = (view object.buf).val.length
      rw [written,scalar_store_bytes_length]
    refine ⟨⟨buffer,after,lengthEq⟩,?_⟩
    rw [if_pos inside]
    refine ⟨status,?_⟩
    rw [after]
    apply memory_write_decodes view code store inst ⟨[],Store.decodeInstance store inst⟩ memoryAddress object buffer
      _ _ rfl mapped issued
    · simpa only [store_payload,Builtins.integerBytes_length] using inside
    · rw [written,scalar_store_bytes_source _ _ _ _ inside,store_payload]
  · rename_i outside
    have status := congrArg Prod.fst effect
    have unchanged : view buffer = view object.buf := congrArg Prod.snd effect
    refine ⟨⟨buffer,after,by rw [unchanged]⟩,?_⟩
    rw [if_neg outside]
    refine ⟨status,?_⟩
    rw [after]
    exact memory_unchanged_decodes view code store memoryAddress object buffer issued unchanged
end Itasca.Runtime.Interp.MemoryDescriptor

end

/-! ## Memory Value Slots -/

section

namespace Itasca.Runtime.Interp.MemoryDescriptor
open Aeneas Aeneas.Std SpecExt

theorem scalar_load_bytes_bound (bytes : List U8) (start width : Nat)
    (widthBound : width ≤ 8) (inside : start+width ≤ bytes.length) :
    (scalarLoadBytes bytes start 0#u64 0 width).val < 256^width := by
  rw [scalar_load_bytes_source bytes start width widthBound inside]
  have valid : Forall wf_byte (Store.decodeBytes ((bytes.drop start).take width)) := by
    intro b member
    obtain ⟨raw,_,rfl⟩ := List.mem_map.mp member
    constructor
    scalar_tac
  have lengthEq : (Store.decodeBytes ((bytes.drop start).take width)).length = width := by
    simp only [Store.decodeBytes,List.length_map,List.length_take,List.length_drop]
    omega
  simpa only [lengthEq] using Spec.integer_of_bytes_bound _ valid

theorem load_word_small (op : SourceMachine.Memory.Load) (word : U64)
    (bounded : word.val < 256^op.bytes) :
    op.type = .I32 ∨ op.type = .F32 → (scalarLoadedWord (loadOpcode op) word).val < 2^32 := by
  intro small
  cases op with
  | full ty =>
    cases ty <;> simp only [SourceMachine.Memory.Load.type] at small
    · change word.val < 2^32
      exact bounded
    · simp at small
    · change word.val < 2^32
      exact bounded
    · simp at small
  | packed ty width sign =>
    cases ty with
    | I64 => simp [SourceMachine.Memory.Load.type,numtype_Inn] at small
    | I32 =>
      cases width with
      | byte =>
        cases sign with
        | U => change word.val < 2^32; norm_num [SourceMachine.Memory.Load.bytes,SourceMachine.Memory.PackedWidth.bits] at bounded; omega
        | S =>
          change (UScalar.cast .U64 (IScalar.hcast .U32 (IScalar.cast .I32 (UScalar.hcast .I8 word)))).val < 2^32
          scalar_tac
      | half =>
        cases sign with
        | U => change word.val < 2^32; norm_num [SourceMachine.Memory.Load.bytes,SourceMachine.Memory.PackedWidth.bits] at bounded; omega
        | S =>
          change (UScalar.cast .U64 (IScalar.hcast .U32 (IScalar.cast .I32 (UScalar.hcast .I16 word)))).val < 2^32
          scalar_tac

theorem numeric_word_encode (ty : numtype) (word : U64)
    (small : ty = .I32 ∨ ty = .F32 → word.val < 2^32) :
    Compiler.encodeValue (Store.decodeWords (numericMemoryType ty) word 0#u64) = [word.val] := by
  cases ty
  · change [word.val % 2^32] = [word.val]
    rw [Nat.mod_eq_of_lt (small (Or.inl rfl))]
  · rfl
  · change [Builtins.floatBits 32 (Builtins.floatOfBits 32 (word.val % 2^32))] = [word.val]
    have bound := small (Or.inr rfl)
    rw [Nat.mod_eq_of_lt bound,Builtins.Float.float_bits_roundtrip_32 word.val bound]
  · change [Builtins.floatBits 64 (Builtins.floatOfBits 64 word.val)] = [word.val]
    rw [Builtins.Float.float_bits_roundtrip_64 word.val (by scalar_tac)]

theorem load_word_encode (op : SourceMachine.Memory.Load) (bytes : List U8) (start : Nat)
    (inside : start + op.bytes ≤ bytes.length) :
    Compiler.encodeValue (op.value (Store.decodeBytes ((bytes.drop start).take op.bytes))) =
      [(scalarLoadedWord (loadOpcode op) (scalarLoadBytes bytes start 0#u64 0 op.bytes)).val] := by
  rw [←load_word_value op bytes start inside]
  apply numeric_word_encode
  apply load_word_small
  apply scalar_load_bytes_bound bytes start op.bytes
  · cases op with
    | full ty => cases ty <;> decide
    | packed ty width sign => cases width <;> simp [SourceMachine.Memory.Load.bytes,SourceMachine.Memory.PackedWidth.bits]
  · exact inside
end Itasca.Runtime.Interp.MemoryDescriptor

end

end

/-! ## MemoryCore -/

section

/-!
Scalar load dispatch and core execution. Bytecode dispatch equations and destination-slot effects assemble the core scalar load correspondence.
-/

/-! ## Memory Dispatch Bridge -/

section

namespace Itasca.Runtime.Interp.MemoryDescriptor
open Aeneas Aeneas.Std

variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem dispatch_load_eq (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (index inst function base : Usize)
    (op : SourceMachine.Memory.Load) (dst address offset : U32) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index inst function base
      (Compiler.memoryLoadInstruction op dst address offset) = (do
        let (result,next) ← runtime.interp.execute_load memory exec store inst base (loadOpcode op) dst address offset
        Result.ok (result,next,store,platform)) := by
  cases op with
  | full ty => cases ty <;> simp [Compiler.memoryLoadInstruction,runtime.interp.dispatch,
      runtime.interp.dispatch_load,runtime.interp.load_operands,loadOpcode,numericLoadOpcode,bind_ok]
  | packed ty width sign => cases ty <;> cases width <;> cases sign <;>
    simp [Compiler.memoryLoadInstruction,runtime.interp.dispatch,runtime.interp.dispatch_load,
      runtime.interp.load_operands,loadOpcode,packed,PackedMemory.loadOpcode,bind_ok]

theorem dispatch_store_eq (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (index inst function base : Usize)
    (op : SourceMachine.Memory.Store) (address value offset : U32) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index inst function base
      (Compiler.memoryStoreInstruction op address value offset) = (do
        let (result,next) ← runtime.interp.execute_store memory exec store inst base (storeOpcode op) address value offset
        Result.ok (result,exec,next,platform)) := by
  cases op with
  | full ty => cases ty <;> simp [Compiler.memoryStoreInstruction,runtime.interp.dispatch,
      runtime.interp.dispatch_store,runtime.interp.store_operands,storeOpcode,numericStoreOpcode,bind_ok]
  | packed ty width => cases ty <;> cases width <;>
    simp [Compiler.memoryStoreInstruction,runtime.interp.dispatch,runtime.interp.dispatch_store,
      runtime.interp.store_operands,storeOpcode,packed,PackedMemory.storeOpcode,bind_ok]

theorem dispatch_load {Q : core.result.Result Unit runtime.ExecError × runtime.interp.Execution → Prop}
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index inst function base : Usize) (op : SourceMachine.Memory.Load) (dst address offset : U32)
    (handler : runtime.interp.execute_load memory exec store inst base (loadOpcode op) dst address offset ⦃ Q ⦄) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index inst function base
      (Compiler.memoryLoadInstruction op dst address offset) ⦃ out =>
        Q (out.1,out.2.1) ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ⦄ := by
  rw [dispatch_load_eq]
  obtain ⟨out,result,property⟩ := WP.spec_imp_exists handler
  rw [result]
  rcases out with ⟨r,next⟩
  simp only [bind_ok]
  with_unfolding_all apply WP.spec.ret
  exact ⟨property,rfl,rfl⟩

theorem dispatch_store {Q : core.result.Result Unit runtime.ExecError × runtime.store.Store M → Prop}
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index inst function base : Usize) (op : SourceMachine.Memory.Store) (address value offset : U32)
    (handler : runtime.interp.execute_store memory exec store inst base (storeOpcode op) address value offset ⦃ Q ⦄) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index inst function base
      (Compiler.memoryStoreInstruction op address value offset) ⦃ out =>
        Q (out.1,out.2.2.1) ∧ out.2.1 = exec ∧ out.2.2.2 = platform ⦄ := by
  rw [dispatch_store_eq]
  obtain ⟨out,result,property⟩ := WP.spec_imp_exists handler
  rw [result]
  rcases out with ⟨r,next⟩
  simp only [bind_ok]
  with_unfolding_all apply WP.spec.ret
  exact ⟨property,rfl,rfl⟩
end Itasca.Runtime.Interp.MemoryDescriptor

end

/-! ## Memory Load Slots -/

section

namespace Itasca.Runtime.Interp.MemoryDescriptor
open Aeneas Aeneas.Std

 theorem execute_load_slots {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (instanceIndex base : Usize)
    (op : SourceMachine.Memory.Load) (address offset : U32) (inst : runtime.store.ModuleInst)
    (memoryAddress : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (front : List val) (bits : Nat)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.memories.val[0]? = some memoryAddress)
    (issued : store.memories.val[memoryAddress.index.val]? = some object)
    (values : ValuesAt exec.slots.val base.val (front ++ [SourceMachine.integerVal .I32 bits]))
    (addressSlot : address.val = Compiler.slots (front.map Compiler.valueType))
    (bitsBound : bits < 2^32) :
    runtime.interp.execute_load memory exec store instanceIndex base (loadOpcode op) address address offset ⦃ out =>
      if bits + offset.val + op.bytes ≤ (view object.buf).length then
        out.1 = .Ok () ∧
        ValuesAt out.2.slots.val base.val (front ++ [op.value
          (Store.decodeBytes (((view object.buf).val.drop (bits+offset.val)).take op.bytes))]) ∧
        {out.2 with slots := exec.slots} = exec
      else out = (.Err (.Trap .MemoryOutOfBounds),exec) ⦄ := by
  have words : WordsAt exec.slots.val base.val (Compiler.encodeValues front ++ [bits]) := by
    simpa only [ValuesAt,Compiler.encode_values_append,Compiler.encodeValues,Compiler.encodeValue,SourceMachine.integerVal,
      numtype_Inn,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil] using values
  have tail := words.append_right
  obtain ⟨bound,wordEq⟩ := tail 0 (by simp)
  have addressPosition : address.val = (Compiler.encodeValues front).length := by simpa only [Compiler.encode_values_length] using addressSlot
  have atBound : base.val + address.val < exec.slots.length := by simpa only [Nat.add_zero,←addressPosition] using bound
  let word := exec.slots.val[base.val+address.val]
  have input : exec.slots.val[base.val+address.val]? = some word := List.getElem?_eq_getElem atBound
  have actual : word.val = bits := by
    have concrete : exec.slots.val[base.val+address.val]!.val = bits := by
      simpa only [Nat.add_zero,←addressPosition,List.getElem!_cons_zero] using wordEq
    simpa only [_root_.getElem!_pos exec.slots.val (base.val+address.val) atBound] using concrete
  have castEq : (UScalar.cast .U32 word).val = bits := by scalar_tac
  apply WP.spec_mono (execute_load_effect memory view laws exec store instanceIndex base (loadOpcode op) address address offset
    inst memoryAddress object word found mapped issued input atBound)
  intro out effect
  rw [load_width,castEq] at effect
  split at effect
  · rename_i inside
    rw [if_pos inside]
    refine ⟨effect.1,?_,effect.2.2⟩
    rw [effect.2.1]
    have updated := words.append_left.set_append
      (scalarLoadedWord (loadOpcode op) (scalarLoadBytes (view object.buf).val (bits+offset.val) 0#u64 0 op.bytes))
      (by simpa only [←addressPosition] using atBound)
    rw [addressPosition]
    simpa only [ValuesAt,Compiler.encode_values_append,Compiler.encodeValues,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,load_word_encode op _ _ inside] using updated
  · rename_i outside
    rw [if_neg outside]
    exact effect
end Itasca.Runtime.Interp.MemoryDescriptor

end

/-! ## Memory Core -/

section

namespace Itasca.Runtime.Interp.MemoryDescriptor
open Aeneas Aeneas.Std SpecExt

 theorem core_load_value {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (memoryAddress : runtime.MemoryAddr)
    (object : runtime.store.MemInst M) (s : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (front : List val) (bits : Nat) (op : SourceMachine.Memory.Load) (argument : memarg) (offset : U32)
    (storeEq : s.store = Store.decodeStore view code store) (moduleEq : f.module = Store.decodeInstance store inst)
    (mapped : inst.memories.val[0]? = some memoryAddress)
    (issued : store.memories.val[memoryAddress.index.val]? = some object)
    (values : f.vals = front ++ [SourceMachine.integerVal .I32 bits]) (bound : bits < 2^32)
    (offsetEq : proj_uN_0 argument.OFFSET = offset.val) :
    SourceMachine.Core.load s f rest after op argument =
      if bits+offset.val+op.bytes ≤ (view object.buf).length then
        .next {s with frames := {f with code := after, vals := front ++ [op.value
          (Store.decodeBytes (((view object.buf).val.drop (bits+offset.val)).take op.bytes))]} :: rest}
      else .trap := by
  simp only [SourceMachine.Core.load,values,SourceMachine.pop_append,SourceMachine.integerVal,SourceMachine.integer,numtype_Inn,
    and_self,ite_true,true_and,if_pos bound,moduleEq,Store.decodeInstance,List.getElem?_map,mapped,Option.map_some,
    storeEq,Store.decodeStore,issued,offsetEq,Store.decodeMemory,Store.decodeBytes,List.length_map,
    List.map_drop,List.map_take,SourceMachine.advance]

 theorem execute_load_core {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (op : SourceMachine.Memory.Load) (address offset : U32) (inst : runtime.store.ModuleInst)
    (memoryAddress : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (s : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (front : List val) (bits : Nat) (argument : memarg)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.memories.val[0]? = some memoryAddress)
    (issued : store.memories.val[memoryAddress.index.val]? = some object)
    (storeEq : s.store = Store.decodeStore view code store)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (values : f.vals = front ++ [SourceMachine.integerVal .I32 bits])
    (slots : FrameSlots exec raw f)
    (addressSlot : address.val = Compiler.slots (f.locals.map Compiler.valueType) + Compiler.slots (front.map Compiler.valueType))
    (bitsBound : bits < 2^32) (offsetEq : proj_uN_0 argument.OFFSET = offset.val) :
    runtime.interp.execute_load memory exec store raw.instance raw.base (loadOpcode op) address address offset ⦃ out =>
      (∃ nextFrame, out.1 = .Ok () ∧ SourceMachine.Core.load s f rest after op argument = .next {s with frames := nextFrame :: rest} ∧
        FrameSlots out.2 raw nextFrame ∧ {out.2 with slots := exec.slots} = exec) ∨
      (out = (.Err (.Trap .MemoryOutOfBounds),exec) ∧ SourceMachine.Core.load s f rest after op argument = .trap) ⦄ := by
  have actualValues : ValuesAt exec.slots.val raw.base.val ((f.locals++front) ++ [SourceMachine.integerVal .I32 bits]) := by
    simpa only [FrameSlots,values,List.append_assoc] using slots
  have actualAddress : address.val = Compiler.slots ((f.locals++front).map Compiler.valueType) := by
    simpa only [List.map_append,Compiler.slots_append] using addressSlot
  have abstract := core_load_value view code store inst memoryAddress object s f rest after front bits op argument offset
    storeEq moduleEq mapped issued values bitsBound offsetEq
  apply WP.spec_mono (execute_load_slots memory view laws exec store raw.instance raw.base op address offset inst memoryAddress object
    (f.locals++front) bits found mapped issued actualValues actualAddress bitsBound)
  intro out effect
  split at effect
  · rename_i inside
    rw [if_pos inside] at abstract
    exact Or.inl ⟨_,effect.1,abstract,by simpa only [FrameSlots,List.append_assoc] using effect.2.1,effect.2.2⟩
  · rename_i outside
    rw [if_neg outside] at abstract
    exact Or.inr ⟨effect,abstract⟩
end Itasca.Runtime.Interp.MemoryDescriptor

end

end

/-! ## MemoryCoreStore -/

section

/-!
Scalar store execution from numeric input encoding through operand slots. The core correspondence uses the actual store bytes and preserves the stated memory effect.
-/

/-! ## Memory Numeric Input -/

section

namespace Itasca.Runtime.Interp.MemoryDescriptor
open Aeneas Aeneas.Std

theorem numeric_input_word (words : List U64) (position : Nat) (ty : numtype) (value : num_)
    (wellFormed : wf_num_ ty value)
    (represented : WordsAt words position (Compiler.encodeValue (.CONST ty value))) :
    ∃ word, words[position]? = some word ∧ numericStoreValue ty word = value := by
  have lengthEq : (Compiler.encodeValue (.CONST ty value)).length = 1 := by
    rw [Compiler.encode_value_length]
    cases ty <;> rfl
  obtain ⟨bits,encoded⟩ := List.length_eq_one_iff.mp lengthEq
  rw [encoded] at represented
  obtain ⟨bound,atWord⟩ := represented 0 (by simp)
  simp only [Nat.add_zero,List.getElem!_cons_zero] at bound atWord
  let word := words[position]
  have wordBits : word.val = bits := by simpa only [_root_.getElem!_pos words position bound] using atWord
  have pair : pairWords (numericMemoryType ty) (word,0#u64) = Compiler.encodeValue (.CONST ty value) := by
    rw [encoded,←wordBits]
    cases ty <;> rfl
  have floatBound : numericMemoryType ty = .F32 → word.val < 2^32 := by
    intro floating
    have sourceType : Compiler.valueType (.CONST ty value) = .F32 := by
      cases ty <;> simp_all [numericMemoryType,Compiler.valueType,valtype_numtype,numtype_Inn,numtype_Fnn]
    have bounded := encode_value_f32_low (.CONST ty value) (.val_case_0 ty value wellFormed) sourceType
    simpa only [encoded,List.getElem!_cons_zero,wordBits] using bounded
  have roundtrip := Compiler.decode_encode (.CONST ty value) (.val_case_0 ty value wellFormed) []
  simp only [List.append_nil] at roundtrip
  have translated : sourceType (numericMemoryType ty) = Compiler.valueType (.CONST ty value) := by cases ty <;> rfl
  rw [←translated,←pair,decode_words_code _ _ _ floatBound] at roundtrip
  have decoded := congrArg Prod.fst (Option.some.inj roundtrip)
  rw [numeric_store_value_decodes] at decoded
  exact ⟨word,List.getElem?_eq_getElem bound,(val.CONST.inj decoded).2⟩
end Itasca.Runtime.Interp.MemoryDescriptor

end

/-! ## Memory Store Slots -/

section

namespace Itasca.Runtime.Interp.MemoryDescriptor
open Aeneas Aeneas.Std

 theorem execute_store_slots {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (instanceIndex base : Usize)
    (op : SourceMachine.Memory.Store) (address value offset : U32) (inst : runtime.store.ModuleInst)
    (memoryAddress : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (front : List val) (bits : Nat) (number : num_)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.memories.val[0]? = some memoryAddress)
    (issued : store.memories.val[memoryAddress.index.val]? = some object)
    (values : ValuesAt exec.slots.val base.val (front ++ [SourceMachine.integerVal .I32 bits,.CONST op.type number]))
    (addressSlot : address.val = Compiler.slots (front.map Compiler.valueType))
    (valueSlot : value.val = address.val+1)
    (bitsBound : bits < 2^32) (numberWf : wf_num_ op.type number) :
    runtime.interp.execute_store memory exec store instanceIndex base (storeOpcode op) address value offset ⦃ out =>
      MemoryMutation view store out.2 memoryAddress object ∧
      if bits+offset.val+op.bytes ≤ (view object.buf).length then
        out.1 = .Ok () ∧ Store.decodeStore view code out.2 =
          Spec.memoryPayloadWrite (Store.decodeStore view code store) ⟨[],Store.decodeInstance store inst⟩
            (bits+offset.val) (op.payload number)
      else out.1 = .Err (.Trap .MemoryOutOfBounds) ∧ Store.decodeStore view code out.2 = Store.decodeStore view code store ⦄ := by
  have words : WordsAt exec.slots.val base.val
      ((Compiler.encodeValues front ++ [bits]) ++ Compiler.encodeValue (.CONST op.type number)) := by
    simpa only [ValuesAt,Compiler.encode_values_append,Compiler.encodeValues,Compiler.encodeValue,SourceMachine.integerVal,
      numtype_Inn,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc] using values
  have addressPosition : address.val = (Compiler.encodeValues front).length := by simpa only [Compiler.encode_values_length] using addressSlot
  have addressWords := words.append_left.append_right
  obtain ⟨bound,wordEq⟩ := addressWords 0 (by simp)
  have atBound : base.val+address.val < exec.slots.length := by simpa only [Nat.add_zero,←addressPosition] using bound
  let word := exec.slots.val[base.val+address.val]
  have input : exec.slots.val[base.val+address.val]? = some word := List.getElem?_eq_getElem atBound
  have actual : word.val = bits := by
    have concrete : exec.slots.val[base.val+address.val]!.val = bits := by
      simpa only [Nat.add_zero,←addressPosition,List.getElem!_cons_zero] using wordEq
    simpa only [_root_.getElem!_pos exec.slots.val (base.val+address.val) atBound] using concrete
  have castEq : (UScalar.cast .U32 word).val = bits := by scalar_tac
  have numericWords : WordsAt exec.slots.val (base.val+value.val) (Compiler.encodeValue (.CONST op.type number)) := by
    simpa only [List.length_append,List.length_singleton,←addressPosition,←valueSlot] using words.append_right
  obtain ⟨valueWord,inputValue,decoded⟩ := numeric_input_word exec.slots.val (base.val+value.val) op.type number numberWf numericWords
  have effect := execute_store_value memory view laws code exec store instanceIndex base op address value offset inst memoryAddress object word valueWord
    found mapped issued input inputValue
  simpa only [castEq,decoded] using effect
end Itasca.Runtime.Interp.MemoryDescriptor

end

/-! ## Memory Core Store -/

section

namespace Itasca.Runtime.Interp.MemoryDescriptor
open Aeneas Aeneas.Std SpecExt

 theorem core_store_value {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (memoryAddress : runtime.MemoryAddr)
    (object : runtime.store.MemInst M) (s : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (front : List val) (bits : Nat) (op : SourceMachine.Memory.Store) (number : num_) (argument : memarg) (offset : U32)
    (storeEq : s.store = Store.decodeStore view code store) (moduleEq : f.module = Store.decodeInstance store inst)
    (mapped : inst.memories.val[0]? = some memoryAddress)
    (issued : store.memories.val[memoryAddress.index.val]? = some object)
    (values : f.vals = front ++ [SourceMachine.integerVal .I32 bits,.CONST op.type number]) (bound : bits < 2^32)
    (offsetEq : proj_uN_0 argument.OFFSET = offset.val) :
    SourceMachine.Core.store s f rest after op argument =
      if bits+offset.val+op.bytes ≤ (view object.buf).length then
        .next {s with store := Spec.memoryPayloadWrite (Store.decodeStore view code store) ⟨[],Store.decodeInstance store inst⟩ (bits+offset.val) (op.payload number), frames := {f with code := after, vals := front} :: rest}
      else .trap := by
  have stack : f.vals = (front ++ [SourceMachine.integerVal .I32 bits]) ++ [.CONST op.type number] := by
    simpa only [List.append_assoc,List.singleton_append] using values
  simp only [SourceMachine.Core.store,stack,SourceMachine.pop_append,SourceMachine.integerVal,SourceMachine.integer,numtype_Inn,
    and_self,ite_true,true_and,if_pos bound,moduleEq,Store.decodeInstance,List.getElem?_map,mapped,Option.map_some,
    storeEq,Store.decodeStore,issued,offsetEq,Store.decodeMemory,Store.decodeBytes,List.length_map,
    List.map_drop,List.map_take,SourceMachine.advance]
  simp only [Spec.memoryPayloadWrite,SourceMachine.AFrame.toFrame,moduleEq,Store.decodeInstance]

 theorem execute_store_core_values {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (op : SourceMachine.Memory.Store) (address value offset : U32) (inst : runtime.store.ModuleInst)
    (memoryAddress : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (s : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (front : List val) (bits : Nat) (number : num_) (argument : memarg)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.memories.val[0]? = some memoryAddress)
    (issued : store.memories.val[memoryAddress.index.val]? = some object)
    (storeEq : s.store = Store.decodeStore view code store)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (values : f.vals = front ++ [SourceMachine.integerVal .I32 bits,.CONST op.type number])
    (slots : FrameSlots exec raw f)
    (addressSlot : address.val = Compiler.slots (f.locals.map Compiler.valueType) + Compiler.slots (front.map Compiler.valueType))
    (valueSlot : value.val = address.val+1)
    (bitsBound : bits < 2^32) (numberWf : wf_num_ op.type number)
    (offsetEq : proj_uN_0 argument.OFFSET = offset.val) :
    runtime.interp.execute_store memory exec store raw.instance raw.base (storeOpcode op) address value offset ⦃ out =>
      MemoryMutation view store out.2 memoryAddress object ∧
      ((out.1 = .Ok () ∧ SourceMachine.Core.store s f rest after op argument =
          .next {s with store := Store.decodeStore view code out.2, frames := {f with code := after, vals := front} :: rest} ∧
        FrameSlots exec raw {f with code := after, vals := front}) ∨
      (out.1 = .Err (.Trap .MemoryOutOfBounds) ∧ SourceMachine.Core.store s f rest after op argument = .trap ∧
        Store.decodeStore view code out.2 = Store.decodeStore view code store)) ⦄ := by
  have actualValues : ValuesAt exec.slots.val raw.base.val
      ((f.locals++front) ++ [SourceMachine.integerVal .I32 bits,.CONST op.type number]) := by
    simpa only [FrameSlots,values,List.append_assoc] using slots
  have actualAddress : address.val = Compiler.slots ((f.locals++front).map Compiler.valueType) := by
    simpa only [List.map_append,Compiler.slots_append] using addressSlot
  have abstract := core_store_value view code store inst memoryAddress object s f rest after front bits op number argument offset
    storeEq moduleEq mapped issued values bitsBound offsetEq
  apply WP.spec_mono (execute_store_slots memory view laws code exec store raw.instance raw.base op address value offset inst memoryAddress object
    (f.locals++front) bits number found mapped issued actualValues actualAddress valueSlot bitsBound numberWf)
  intro out effect
  refine ⟨effect.1,?_⟩
  split at effect
  · rename_i inside
    rw [if_pos inside,←effect.2.2] at abstract
    exact Or.inl ⟨effect.2.1,abstract,actualValues.locals⟩
  · rename_i outside
    rw [if_neg outside] at abstract
    exact Or.inr ⟨effect.2.1,abstract,effect.2.2⟩
end Itasca.Runtime.Interp.MemoryDescriptor

end

end

/-! ## MemoryCoreOperandBounds -/

section

/-!
Scalar memory operand inversion and bounds. Typed operands supply the address/value facts needed to justify their concrete slot accesses.
-/

/-! ## Memory Core Operands -/

section

namespace Itasca.Runtime.Interp.MemoryDescriptor
open Aeneas Aeneas.Std SpecExt

 theorem memory_lookup_back {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (f : SourceMachine.AFrame)
    (sourceAddress : Nat) (sourceObject : meminst)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (mapped : f.module.MEMS[0]? = some sourceAddress)
    (issued : (Store.decodeStore view code store).MEMS[sourceAddress]? = some sourceObject) :
    ∃ address object, inst.memories.val[0]? = some address ∧
      store.memories.val[address.index.val]? = some object := by
  rw [moduleEq] at mapped
  simp only [Store.decodeInstance,List.getElem?_map] at mapped
  obtain ⟨address,rawMapped,addressEq⟩ := Option.map_eq_some_iff.mp mapped
  simp only [Store.decodeStore,List.getElem?_map] at issued
  obtain ⟨object,rawIssued,objectEq⟩ := Option.map_eq_some_iff.mp issued
  exact ⟨address,object,rawMapped,by simpa only [addressEq] using rawIssued⟩

end Itasca.Runtime.Interp.MemoryDescriptor

end

/-! ## Memory Core Operand Bounds -/

section

namespace Itasca.Runtime.Interp.MemoryDescriptor
open Aeneas Aeneas.Std SpecExt
 theorem load_typed_operands_full {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (f : SourceMachine.AFrame)
    (after : List instr) (op : SourceMachine.Memory.Load) (argument : memarg)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (typed : SourceMachine.FrameTyped (Store.decodeStore view code store) {f with code := op.source argument :: after} []) :
    ∃ front bits address object, f.vals = front ++ [SourceMachine.integerVal .I32 bits] ∧ bits < 2^32 ∧
      inst.memories.val[0]? = some address ∧ store.memories.val[address.index.val]? = some object ∧ Forall wf_val front ∧ (∀ label ∈ f.labels, label.height ≤ front.length) := by
  obtain ⟨C,front,operands,ins,outs,bindings,_,operation,split,operandTypes,frontWf,heights⟩ :=
    SourceMachine.frame_typed_operands_bounds typed
  obtain ⟨rfl,rfl,present⟩ := op.typing argument operation
  obtain ⟨sourceAddress,sourceObject,mapped,found⟩ := bindings.memory_lookup present
  obtain ⟨address,object,rawMapped,rawFound⟩ := memory_lookup_back view code store inst f sourceAddress sourceObject moduleEq mapped found
  cases operandTypes with
  | cons addressTyped tail =>
    cases tail
    obtain ⟨bits,rfl,bitsBound⟩ := SourceMachine.integer_val_inv (ty := .I32) addressTyped
    exact ⟨front,bits,address,object,split,bitsBound,rawMapped,rawFound,frontWf,heights⟩

 theorem store_typed_operands_full {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (f : SourceMachine.AFrame)
    (after : List instr) (op : SourceMachine.Memory.Store) (argument : memarg)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (typed : SourceMachine.FrameTyped (Store.decodeStore view code store) {f with code := op.source argument :: after} []) :
    ∃ front bits number address object, f.vals = front ++ [SourceMachine.integerVal .I32 bits,.CONST op.type number] ∧
      bits < 2^32 ∧ wf_num_ op.type number ∧ inst.memories.val[0]? = some address ∧
      store.memories.val[address.index.val]? = some object ∧ Forall wf_val front ∧ (∀ label ∈ f.labels, label.height ≤ front.length) := by
  obtain ⟨C,front,operands,ins,outs,bindings,_,operation,split,operandTypes,frontWf,heights⟩ :=
    SourceMachine.frame_typed_operands_bounds typed
  obtain ⟨rfl,rfl,present⟩ := op.typing argument operation
  obtain ⟨sourceAddress,sourceObject,mapped,found⟩ := bindings.memory_lookup present
  obtain ⟨address,object,rawMapped,rawFound⟩ := memory_lookup_back view code store inst f sourceAddress sourceObject moduleEq mapped found
  cases operandTypes with
  | cons addressTyped tail =>
    cases tail with
    | cons valueTyped tail =>
      cases tail
      obtain ⟨bits,rfl,bitsBound⟩ := SourceMachine.integer_val_inv (ty := .I32) addressTyped
      obtain ⟨number,rfl,numberWf⟩ := SourceMachine.Core.numeric_value_inv valueTyped
      exact ⟨front,bits,number,address,object,split,bitsBound,numberWf,rawMapped,rawFound,frontWf,heights⟩
end Itasca.Runtime.Interp.MemoryDescriptor

end

end

/-! ## MemoryCoreResult -/

section

namespace Itasca.Runtime.Interp.MemoryDescriptor
open Aeneas Aeneas.Std SpecExt

theorem core_load_next_shape {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (memoryAddress : runtime.MemoryAddr)
    (object : runtime.store.MemInst M) (s : SourceMachine.AState) (f nextFrame : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (front : List val) (bits : Nat) (op : SourceMachine.Memory.Load) (argument : memarg) (offset : U32)
    (storeEq : s.store = Store.decodeStore view code store) (moduleEq : f.module = Store.decodeInstance store inst)
    (mapped : inst.memories.val[0]? = some memoryAddress)
    (issued : store.memories.val[memoryAddress.index.val]? = some object)
    (values : f.vals = front ++ [SourceMachine.integerVal .I32 bits]) (bound : bits < 2^32)
    (offsetEq : proj_uN_0 argument.OFFSET = offset.val)
    (actual : SourceMachine.Core.load s f rest after op argument = .next {s with frames := nextFrame :: rest}) :
    ∃ value, nextFrame = {f with code := after,vals := front ++ [value]} ∧
      Compiler.valueType value = valtype_numtype op.type := by
  rw [core_load_value view code store inst memoryAddress object s f rest after front bits op argument offset
    storeEq moduleEq mapped issued values bound offsetEq] at actual
  split at actual
  · have same := congrArg SourceMachine.AState.frames (SourceMachine.AResult.next.inj actual)
    have frameEq := (List.cons.inj same).1
    exact ⟨_,frameEq.symm,by rw [value_type_eq_abs]; exact op.value_type _⟩
  · contradiction
end Itasca.Runtime.Interp.MemoryDescriptor

end

/-! ## MemoryCoreStep -/

section

namespace Itasca.Runtime.Interp.MemoryDescriptor
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Spec
 theorem execute_load_core_simulation_exact {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (op : SourceMachine.Memory.Load) (address offset : U32) (inst : runtime.store.ModuleInst)
    (memoryAddress : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (front : List val) (bits : Nat) (argument : memarg)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.memories.val[0]? = some memoryAddress)
    (issued : store.memories.val[memoryAddress.index.val]? = some object)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (values : f.vals = front ++ [SourceMachine.integerVal .I32 bits])
    (slots : FrameSlots exec raw f)
    (addressSlot : address.val = Compiler.slots (f.locals.map Compiler.valueType) + Compiler.slots (front.map Compiler.valueType))
    (bitsBound : bits < 2^32) (offsetEq : proj_uN_0 argument.OFFSET = offset.val)
    (typed : SourceMachine.CoreTyped ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩) :
    let initial : SourceMachine.AState := ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩
    runtime.interp.execute_load memory exec store raw.instance raw.base (loadOpcode op) address address offset ⦃ out =>
      (∃ nextFrame, out.1 = .Ok () ∧
        SourceMachine.Core.load initial f rest after op argument = .next {initial with frames := nextFrame :: rest} ∧
        SourceMachine.CoreTyped {initial with frames := nextFrame :: rest} ∧
        StepH (SourceMachine.decode initial) [] (SourceMachine.decode {initial with frames := nextFrame :: rest}) ∧
        FrameSlots out.2 raw nextFrame ∧ {out.2 with slots := exec.slots} = exec) ∨
      (out = (.Err (.Trap .MemoryOutOfBounds),exec) ∧ ∃ n, 0 < n ∧
        StepsHN n (SourceMachine.decode initial) [] ⟨⟨Store.decodeStore view code store,ambient⟩,[.TRAP]⟩) ⦄ := by
  dsimp only
  have source := SourceMachine.Core.load_progress (Store.decodeStore view code store) ambient f rest after op argument typed
  apply WP.spec_mono (execute_load_core memory view laws code exec store raw op address offset inst memoryAddress object
    ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩ f rest after front bits argument found mapped issued rfl moduleEq values slots addressSlot bitsBound offsetEq)
  intro out effect
  rcases effect with ⟨nextFrame,success,actual,slotsAfter,unchanged⟩ | ⟨failed,actual⟩
  · rcases source with ⟨next,abstract,fresh,step⟩ | ⟨trapped,trace⟩
    · rw [actual] at abstract
      cases abstract
      exact Or.inl ⟨nextFrame,success,actual,fresh,step,slotsAfter,unchanged⟩
    · rw [actual] at trapped
      contradiction
  · rcases source with ⟨next,abstract,fresh,step⟩ | ⟨trapped,trace⟩
    · rw [actual] at abstract
      contradiction
    · exact Or.inr ⟨failed,trace⟩
 theorem step_load_core_simulation {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (platform : P) (index : Usize)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (op : SourceMachine.Memory.Load) (address offset : U32) (inst : runtime.store.ModuleInst)
    (memoryAddress : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (front : List val) (bits : Nat) (argument : memarg)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.memories.val[0]? = some memoryAddress)
    (issued : store.memories.val[memoryAddress.index.val]? = some object)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (values : f.vals = front ++ [SourceMachine.integerVal .I32 bits])
    (slots : FrameSlots exec raw f)
    (addressSlot : address.val = Compiler.slots (f.locals.map Compiler.valueType) + Compiler.slots (front.map Compiler.valueType))
    (bitsBound : bits < 2^32) (offsetEq : proj_uN_0 argument.OFFSET = offset.val)
    (compiled : runtime.bytecode.CompiledFunction)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (fetched : compiled.code.val[raw.pc.val]? = some (Compiler.memoryLoadInstruction op address address offset))
    (pcBound : raw.pc.val < U32.max)
    (typed : SourceMachine.CoreTyped ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩) :
    let initial : SourceMachine.AState := ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      (      (∃ nextFrame, out.1 = .Ok () ∧
        SourceMachine.Core.load initial f rest after op argument = .next {initial with frames := nextFrame :: rest} ∧
        SourceMachine.CoreTyped {initial with frames := nextFrame :: rest} ∧
        StepH (SourceMachine.decode initial) [] (SourceMachine.decode {initial with frames := nextFrame :: rest}) ∧
        FrameSlots out.2.1 raw nextFrame ∧ (∃ pc : U32, pc.val = raw.pc.val+1 ∧ {out.2.1 with slots := exec.slots} = {exec with frames := exec.frames.set index {raw with pc := pc}})) ∨
      (out.1 = .Err (.Trap .MemoryOutOfBounds) ∧ (∃ pc : U32, pc.val = raw.pc.val+1 ∧ out.2.1 = {exec with frames := exec.frames.set index {raw with pc := pc}}) ∧ ∃ n, 0 < n ∧
        StepsHN n (SourceMachine.decode initial) [] ⟨⟨Store.decodeStore view code store,ambient⟩,[.TRAP]⟩)) ⦄ := by
  dsimp only
  apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
    (Compiler.memoryLoadInstruction op address address offset) last frameFound found codeFound fetched pcBound
  intro pc pcNext
  have handler := execute_load_core_simulation_exact memory view laws code {exec with frames := exec.frames.set index {raw with pc := pc}} store raw op address offset inst memoryAddress object ambient f rest after front bits argument found mapped issued moduleEq values slots addressSlot bitsBound offsetEq typed
  apply WP.spec_mono (dispatch_load memory hooks floats allocator _ store platform index raw.instance raw.function raw.base op address address offset handler)
  intro out effect
  refine ⟨effect.2.1,effect.2.2,?_⟩
  rcases effect.1 with ⟨nextFrame,success,actual,fresh,source,represented,unchanged⟩ | ⟨failed,trace⟩
  · exact Or.inl ⟨nextFrame,success,actual,fresh,source,represented,pc,pcNext,unchanged⟩
  · exact Or.inr ⟨congrArg Prod.fst failed,⟨pc,pcNext,congrArg Prod.snd failed⟩,trace⟩
 theorem execute_store_core_simulation_exact {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (op : SourceMachine.Memory.Store) (address value offset : U32) (inst : runtime.store.ModuleInst)
    (memoryAddress : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (front : List val) (bits : Nat) (number : num_) (argument : memarg)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.memories.val[0]? = some memoryAddress)
    (issued : store.memories.val[memoryAddress.index.val]? = some object)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (values : f.vals = front ++ [SourceMachine.integerVal .I32 bits,.CONST op.type number])
    (slots : FrameSlots exec raw f)
    (addressSlot : address.val = Compiler.slots (f.locals.map Compiler.valueType) + Compiler.slots (front.map Compiler.valueType))
    (valueSlot : value.val = address.val+1)
    (bitsBound : bits < 2^32) (numberWf : wf_num_ op.type number)
    (offsetEq : proj_uN_0 argument.OFFSET = offset.val)
    (typed : SourceMachine.CoreTyped ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩) :
    let initial : SourceMachine.AState := ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩
    runtime.interp.execute_store memory exec store raw.instance raw.base (storeOpcode op) address value offset ⦃ out =>
      MemoryMutation view store out.2 memoryAddress object ∧
      ((out.1 = .Ok () ∧
        SourceMachine.Core.store initial f rest after op argument = .next {initial with store := Store.decodeStore view code out.2, frames := {f with code := after,vals := front} :: rest} ∧
        SourceMachine.CoreTyped {initial with store := Store.decodeStore view code out.2, frames := {f with code := after,vals := front} :: rest} ∧
        Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2) ∧
        StepH (SourceMachine.decode initial) [] (SourceMachine.decode {initial with store := Store.decodeStore view code out.2, frames := {f with code := after,vals := front} :: rest}) ∧
        FrameSlots exec raw {f with code := after,vals := front}) ∨
      (out.1 = .Err (.Trap .MemoryOutOfBounds) ∧ Store.decodeStore view code out.2 = Store.decodeStore view code store ∧
        ∃ n, 0 < n ∧ StepsHN n (SourceMachine.decode initial) [] ⟨⟨Store.decodeStore view code store,ambient⟩,[.TRAP]⟩)) ⦄ := by
  dsimp only
  have source := SourceMachine.Core.store_progress (Store.decodeStore view code store) ambient f rest after op argument typed
  apply WP.spec_mono (execute_store_core_values memory view laws code exec store raw op address value offset inst memoryAddress object
    ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩ f rest after front bits number argument found mapped issued rfl moduleEq values slots addressSlot valueSlot bitsBound numberWf offsetEq)
  intro out effect
  refine ⟨effect.1,?_⟩
  rcases effect.2 with ⟨success,actual,slotsAfter⟩ | ⟨failed,actual,unchanged⟩
  · rcases source with ⟨next,abstract,fresh,extension,step⟩ | ⟨trapped,trace⟩
    · rw [actual] at abstract
      cases abstract
      exact Or.inl ⟨success,actual,fresh,extension,step,slotsAfter⟩
    · rw [actual] at trapped
      contradiction
  · rcases source with ⟨next,abstract,fresh,extension,step⟩ | ⟨trapped,trace⟩
    · rw [actual] at abstract
      contradiction
    · exact Or.inr ⟨failed,unchanged,trace⟩
 theorem step_store_core_simulation {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (platform : P) (index : Usize)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (op : SourceMachine.Memory.Store) (address value offset : U32) (inst : runtime.store.ModuleInst)
    (memoryAddress : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (front : List val) (bits : Nat) (number : num_) (argument : memarg)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.memories.val[0]? = some memoryAddress)
    (issued : store.memories.val[memoryAddress.index.val]? = some object)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (values : f.vals = front ++ [SourceMachine.integerVal .I32 bits,.CONST op.type number])
    (slots : FrameSlots exec raw f)
    (addressSlot : address.val = Compiler.slots (f.locals.map Compiler.valueType) + Compiler.slots (front.map Compiler.valueType))
    (valueSlot : value.val = address.val+1)
    (bitsBound : bits < 2^32) (numberWf : wf_num_ op.type number)
    (offsetEq : proj_uN_0 argument.OFFSET = offset.val)
    (compiled : runtime.bytecode.CompiledFunction)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (fetched : compiled.code.val[raw.pc.val]? = some (Compiler.memoryStoreInstruction op address value offset))
    (pcBound : raw.pc.val < U32.max)
    (typed : SourceMachine.CoreTyped ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩) :
    let initial : SourceMachine.AState := ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.2 = platform ∧ (∃ pc : U32, pc.val = raw.pc.val+1 ∧ out.2.1 = {exec with frames := exec.frames.set index {raw with pc := pc}}) ∧
      (      MemoryMutation view store out.2.2.1 memoryAddress object ∧
      ((out.1 = .Ok () ∧
        SourceMachine.Core.store initial f rest after op argument = .next {initial with store := Store.decodeStore view code out.2.2.1, frames := {f with code := after,vals := front} :: rest} ∧
        SourceMachine.CoreTyped {initial with store := Store.decodeStore view code out.2.2.1, frames := {f with code := after,vals := front} :: rest} ∧
        Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.2.1) ∧
        StepH (SourceMachine.decode initial) [] (SourceMachine.decode {initial with store := Store.decodeStore view code out.2.2.1, frames := {f with code := after,vals := front} :: rest}) ∧
        FrameSlots exec raw {f with code := after,vals := front}) ∨
      (out.1 = .Err (.Trap .MemoryOutOfBounds) ∧ Store.decodeStore view code out.2.2.1 = Store.decodeStore view code store ∧
        ∃ n, 0 < n ∧ StepsHN n (SourceMachine.decode initial) [] ⟨⟨Store.decodeStore view code store,ambient⟩,[.TRAP]⟩))) ⦄ := by
  dsimp only
  apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
    (Compiler.memoryStoreInstruction op address value offset) last frameFound found codeFound fetched pcBound
  intro pc pcNext
  have handler := execute_store_core_simulation_exact memory view laws code {exec with frames := exec.frames.set index {raw with pc := pc}} store raw op address value offset inst memoryAddress object ambient f rest after front bits number argument found mapped issued moduleEq values slots addressSlot valueSlot bitsBound numberWf offsetEq typed
  apply WP.spec_mono (dispatch_store memory hooks floats allocator _ store platform index raw.instance raw.function raw.base op address value offset handler)
  intro out effect
  exact ⟨effect.2.2,⟨pc,pcNext,effect.2.1⟩,effect.1⟩
end Itasca.Runtime.Interp.MemoryDescriptor

end
