import Itasca.Runtime.SourceMachine.Decode
import Itasca.Runtime.SourceMachine.Typing
import Itasca.Runtime.Spec.FloatPromote

/-!
Sections, each formerly its own module: Descriptor, Semantics, Decode.
-/

/-! ## Descriptor -/

section

namespace Itasca.Runtime.SourceMachine.Memory

/-- Packed scalar widths admitted by the binary format, indexed by result width. -/
inductive PackedWidth : Inn → Type where
  | byte {ty} : PackedWidth ty
  | half {ty} : PackedWidth ty
  | word : PackedWidth .I64

def PackedWidth.bits {ty} : PackedWidth ty → Nat
  | .byte => 8
  | .half => 16
  | .word => 32

def PackedWidth.size {ty} (width : PackedWidth ty) : sz := .mk_sz width.bits

/-- All fourteen scalar loads, including the signed/unsigned packed forms. -/
inductive Load where
  | full (ty : numtype)
  | packed (ty : Inn) (width : PackedWidth ty) (signed : sx)

def Load.type : Load → numtype
  | .full ty => ty
  | .packed ty _ _ => numtype_Inn ty

def Load.bytes : Load → Nat
  | .full ty => sizenn ty / 8
  | .packed _ width _ => width.bits / 8

def Load.operation : Load → Option loadop_
  | .full _ => none
  | .packed ty width signed => some (.mk_loadop__0 ty (.mk_loadop_Inn width.size signed))

def Load.source (op : Load) (argument : memarg) : instr :=
  .LOAD op.type op.operation argument

/-- All nine scalar stores; packed writes truncate the source integer. -/
inductive Store where
  | full (ty : numtype)
  | packed (ty : Inn) (width : PackedWidth ty)

def Store.type : Store → numtype
  | .full ty => ty
  | .packed ty _ => numtype_Inn ty

def Store.bytes : Store → Nat
  | .full ty => sizenn ty / 8
  | .packed _ width => width.bits / 8

def Store.operation : Store → Option sz
  | .full _ => none
  | .packed _ width => some width.size

def Store.source (op : Store) (argument : memarg) : instr :=
  .STORE op.type op.operation argument

end Itasca.Runtime.SourceMachine.Memory

end

/-! ## Semantics -/

section

namespace Itasca.Runtime.SourceMachine.Memory
open SpecExt

def PackedWidth.spec {ty : Inn} (width : PackedWidth ty) : Spec.PackedMemory :=
  match ty,width with
  | .I32,.byte => .i32x8
  | .I32,.half => .i32x16
  | .I64,.byte => .i64x8
  | .I64,.half => .i64x16
  | .I64,.word => .i64x32

theorem PackedWidth.spec_type {ty} (width : PackedWidth ty) : width.spec.type = ty := by
  cases ty <;> cases width <;> rfl

theorem PackedWidth.spec_bytes {ty} (width : PackedWidth ty) : width.spec.bytes = width.bits / 8 := by
  cases ty <;> cases width <;> rfl

def Load.value (op : Load) (payload : List byte) : val :=
  match op with
  | .full ty => .CONST ty (inv_nbytes_ ty payload)
  | .packed ty width sign => .CONST (numtype_Inn ty) (width.spec.loaded sign payload)

def Store.payload (op : Store) (value : num_) : List byte :=
  match op with
  | .full ty => nbytes_ ty value
  | .packed _ width => SpecExt.Builtins.integerBytes (width.bits / 8)
      (proj_uN_0 (Option.get! (proj_num__0 value)))

theorem Load.value_wf (op : Load) (payload : List byte)
    (valid : Forall wf_byte payload) (length : payload.length = op.bytes) : wf_val (op.value payload) := by
  cases op with
  | full ty =>
    apply wf_val.val_case_0
    exact Spec.numeric_bytes_wf ty payload valid (by cases ty <;> exact length)
  | packed ty width sign =>
    apply wf_val.val_case_0
    have numeric := width.spec.loaded_wf sign payload valid (by simpa only [PackedWidth.spec_bytes,Load.bytes] using length)
    simpa only [PackedWidth.spec_type] using numeric

theorem Load.value_type (op : Load) (payload : List byte) :
    valueType (op.value payload) = valtype_numtype op.type := by
  cases op <;> rfl

theorem Store.payload_wf (op : Store) (value : num_) : Forall wf_byte (op.payload value) := by
  cases op with
  | full ty => exact Spec.numeric_bytes_payload_wf ty value
  | packed ty width => exact Spec.integer_bytes_wf _ _

/-- Every scalar load descriptor has the generated source step, with exactly
its byte-width bounds test and canonical decoded value. -/
theorem Load.source_step (op : Load) (s : _root_.store) (f : frame) (argument : memarg) (address : Nat)
    (storeWf : wf_store s) (frameWf : wf_frame f) (addressBound : address < 2^32)
    (operationWf : wf_admininstr (admininstr_instr (op.source argument)))
    (bytesWf : Forall wf_byte (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES) :
    StepH ⟨⟨s,f⟩,[Spec.Segment.i32 address,admininstr_instr (op.source argument)]⟩ []
      ⟨⟨s,f⟩,if address + proj_uN_0 argument.OFFSET + op.bytes ≤ (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length then
        vals [op.value (((fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.drop (address+proj_uN_0 argument.OFFSET)).take op.bytes)]
        else [.TRAP]⟩ := by
  cases op with
  | full ty =>
    have source := Spec.numeric_load_step s f ty argument address storeWf frameWf addressBound operationWf bytesWf
    cases ty <;> exact source
  | packed ty width sign =>
    have source := width.spec.load_step s f sign argument address storeWf frameWf addressBound
      (by cases ty <;> cases width <;> exact operationWf) bytesWf
    cases ty <;> cases width <;> exact source

/-- Scalar stores use the exact byte payload and generated bounds trap. -/
theorem Store.source_step (op : Store) (s : _root_.store) (f : frame) (argument : memarg)
    (address : Nat) (value : num_) (storeWf : wf_store s) (frameWf : wf_frame f)
    (addressBound : address < 2^32) (operationWf : wf_admininstr (admininstr_instr (op.source argument)))
    (valueWf : wf_num_ op.type value) (mapped : 0 < f.MODULE.MEMS.length) :
    StepH ⟨⟨s,f⟩,[Spec.Segment.i32 address,.CONST op.type value,admininstr_instr (op.source argument)]⟩ []
      (if address + proj_uN_0 argument.OFFSET + op.bytes ≤ (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length then
        ⟨⟨Spec.memoryPayloadWrite s f (address+proj_uN_0 argument.OFFSET) (op.payload value),f⟩,[]⟩
      else ⟨⟨s,f⟩,[.TRAP]⟩) := by
  cases op with
  | full ty =>
    have source := Spec.numeric_store_step s f ty argument address value storeWf frameWf
      addressBound operationWf valueWf mapped
    cases ty <;> exact source
  | packed ty width =>
    have typed : Val_ok s (.CONST (numtype_Inn ty) value) (valtype_numtype (numtype_Inn ty)) :=
      .numtype _ _ _ storeWf (.val_case_0 _ _ valueWf)
    obtain ⟨bits,equal,bound⟩ := integer_val_inv typed
    have numbers : value = .mk_num__0 ty (.mk_uN bits) := by cases equal; rfl
    subst value
    have source := width.spec.store_step s f argument address bits storeWf frameWf addressBound
      (by cases ty <;> cases width <;> exact operationWf)
      (by simpa only [PackedWidth.spec_type,Store.type] using valueWf) mapped
    cases ty <;> cases width <;> exact source

end Itasca.Runtime.SourceMachine.Memory

end

/-! ## Decode -/

section

namespace Itasca.Runtime.SourceMachine.Memory

def decodeLoad (ty : numtype) : Option loadop_ → Option Load
  | none => some (.full ty)
  | some (.mk_loadop__0 .I32 (.mk_loadop_Inn (.mk_sz 8) sign)) =>
    if ty = .I32 then some (.packed .I32 .byte sign) else none
  | some (.mk_loadop__0 .I32 (.mk_loadop_Inn (.mk_sz 16) sign)) =>
    if ty = .I32 then some (.packed .I32 .half sign) else none
  | some (.mk_loadop__0 .I64 (.mk_loadop_Inn (.mk_sz 8) sign)) =>
    if ty = .I64 then some (.packed .I64 .byte sign) else none
  | some (.mk_loadop__0 .I64 (.mk_loadop_Inn (.mk_sz 16) sign)) =>
    if ty = .I64 then some (.packed .I64 .half sign) else none
  | some (.mk_loadop__0 .I64 (.mk_loadop_Inn (.mk_sz 32) sign)) =>
    if ty = .I64 then some (.packed .I64 .word sign) else none
  | _ => none

def decodeStore : numtype → Option sz → Option Store
  | ty,none => some (.full ty)
  | .I32,some (.mk_sz 8) => some (.packed .I32 .byte)
  | .I32,some (.mk_sz 16) => some (.packed .I32 .half)
  | .I64,some (.mk_sz 8) => some (.packed .I64 .byte)
  | .I64,some (.mk_sz 16) => some (.packed .I64 .half)
  | .I64,some (.mk_sz 32) => some (.packed .I64 .word)
  | _,_ => none

theorem decode_load_descriptor (op : Load) : decodeLoad op.type op.operation = some op := by
  cases op with
  | full ty => rfl
  | packed ty width sign => cases ty <;> cases width <;> rfl

theorem decode_store_descriptor (op : Store) : decodeStore op.type op.operation = some op := by
  cases op with
  | full ty => rfl
  | packed ty width => cases ty <;> cases width <;> rfl

end Itasca.Runtime.SourceMachine.Memory

end
