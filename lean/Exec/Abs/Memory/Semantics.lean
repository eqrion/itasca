import Exec.Abs.Memory.Descriptor
import Exec.Abs.Typing
import Exec.Spec.PackedMemory

namespace Itasca.Runtime.Abs.Memory
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
    exact Spec.numericBytes_wf ty payload valid (by cases ty <;> exact length)
  | packed ty width sign =>
    apply wf_val.val_case_0
    have numeric := width.spec.loaded_wf sign payload valid (by simpa only [PackedWidth.spec_bytes,Load.bytes] using length)
    simpa only [PackedWidth.spec_type] using numeric

theorem Load.value_type (op : Load) (payload : List byte) :
    valueType (op.value payload) = valtype_numtype op.type := by
  cases op <;> rfl

theorem Store.payload_wf (op : Store) (value : num_) : Forall wf_byte (op.payload value) := by
  cases op with
  | full ty => exact Spec.numericBytes_payload_wf ty value
  | packed ty width => exact Spec.integerBytes_wf _ _

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

end Itasca.Runtime.Abs.Memory
