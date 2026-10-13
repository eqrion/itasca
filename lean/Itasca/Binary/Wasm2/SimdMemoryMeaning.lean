import Itasca.Binary.Wasm2.SimdLaneMeaning

namespace Itasca.Wasm2.Simd

/-- Core 2.0 vector memory instructions and their independently specified effects. -/
inductive MemoryOperation where
  | load
  | load8x8S
  | load8x8U
  | load16x4S
  | load16x4U
  | load32x2S
  | load32x2U
  | splat8
  | splat16
  | splat32
  | splat64
  | storeFull
  | load8Lane
  | load16Lane
  | load32Lane
  | load64Lane
  | store8Lane
  | store16Lane
  | store32Lane
  | store64Lane
  | load32Zero
  | load64Zero
  deriving DecidableEq

def MemoryOperation.naturalAlign : MemoryOperation → Nat
  | .load => 4
  | .load8x8S => 3
  | .load8x8U => 3
  | .load16x4S => 3
  | .load16x4U => 3
  | .load32x2S => 3
  | .load32x2U => 3
  | .splat8 => 0
  | .splat16 => 1
  | .splat32 => 2
  | .splat64 => 3
  | .storeFull => 4
  | .load8Lane => 0
  | .load16Lane => 1
  | .load32Lane => 2
  | .load64Lane => 3
  | .store8Lane => 0
  | .store16Lane => 1
  | .store32Lane => 2
  | .store64Lane => 3
  | .load32Zero => 2
  | .load64Zero => 3

def MemoryOperation.laneCount : MemoryOperation → Nat
  | .load => 0
  | .load8x8S => 0
  | .load8x8U => 0
  | .load16x4S => 0
  | .load16x4U => 0
  | .load32x2S => 0
  | .load32x2U => 0
  | .splat8 => 0
  | .splat16 => 0
  | .splat32 => 0
  | .splat64 => 0
  | .storeFull => 0
  | .load8Lane => 16
  | .load16Lane => 8
  | .load32Lane => 4
  | .load64Lane => 2
  | .store8Lane => 16
  | .store16Lane => 8
  | .store32Lane => 4
  | .store64Lane => 2
  | .load32Zero => 0
  | .load64Zero => 0

def MemoryOperation.store : MemoryOperation → Bool
  | .load => false
  | .load8x8S => false
  | .load8x8U => false
  | .load16x4S => false
  | .load16x4U => false
  | .load32x2S => false
  | .load32x2U => false
  | .splat8 => false
  | .splat16 => false
  | .splat32 => false
  | .splat64 => false
  | .storeFull => true
  | .load8Lane => false
  | .load16Lane => false
  | .load32Lane => false
  | .load64Lane => false
  | .store8Lane => true
  | .store16Lane => true
  | .store32Lane => true
  | .store64Lane => true
  | .load32Zero => false
  | .load64Zero => false

def MemoryOperation.instruction (op : MemoryOperation) (arg : memarg) (lane : laneidx) : instr :=
  match op with
  | .load => .VLOAD .V128 none arg
  | .load8x8S => .VLOAD .V128 (some (.SHAPEX_ (.mk_sz 8) 8 .S)) arg
  | .load8x8U => .VLOAD .V128 (some (.SHAPEX_ (.mk_sz 8) 8 .U)) arg
  | .load16x4S => .VLOAD .V128 (some (.SHAPEX_ (.mk_sz 16) 4 .S)) arg
  | .load16x4U => .VLOAD .V128 (some (.SHAPEX_ (.mk_sz 16) 4 .U)) arg
  | .load32x2S => .VLOAD .V128 (some (.SHAPEX_ (.mk_sz 32) 2 .S)) arg
  | .load32x2U => .VLOAD .V128 (some (.SHAPEX_ (.mk_sz 32) 2 .U)) arg
  | .splat8 => .VLOAD .V128 (some (.SPLAT (.mk_sz 8))) arg
  | .splat16 => .VLOAD .V128 (some (.SPLAT (.mk_sz 16))) arg
  | .splat32 => .VLOAD .V128 (some (.SPLAT (.mk_sz 32))) arg
  | .splat64 => .VLOAD .V128 (some (.SPLAT (.mk_sz 64))) arg
  | .storeFull => .VSTORE .V128 arg
  | .load8Lane => .VLOAD_LANE .V128 (.mk_sz 8) arg lane
  | .load16Lane => .VLOAD_LANE .V128 (.mk_sz 16) arg lane
  | .load32Lane => .VLOAD_LANE .V128 (.mk_sz 32) arg lane
  | .load64Lane => .VLOAD_LANE .V128 (.mk_sz 64) arg lane
  | .store8Lane => .VSTORE_LANE .V128 (.mk_sz 8) arg lane
  | .store16Lane => .VSTORE_LANE .V128 (.mk_sz 16) arg lane
  | .store32Lane => .VSTORE_LANE .V128 (.mk_sz 32) arg lane
  | .store64Lane => .VSTORE_LANE .V128 (.mk_sz 64) arg lane
  | .load32Zero => .VLOAD .V128 (some (.ZERO (.mk_sz 32))) arg
  | .load64Zero => .VLOAD .V128 (some (.ZERO (.mk_sz 64))) arg

def MemoryOperation.inputs (op : MemoryOperation) : List valtype :=
  if op.store || op.laneCount != 0 then [.I32, .V128] else [.I32]

def MemoryOperation.outputs (op : MemoryOperation) : List valtype :=
  if op.store then [] else [.V128]

theorem MemoryOperation.wellFormed (op : MemoryOperation) (arg : memarg) (lane : laneidx)
    (ha : wf_memarg arg) (hl : wf_uN 8 lane) : wf_instr (op.instruction arg lane) := by
  cases op <;> simp only [instruction]
  all_goals constructor
  all_goals try exact ha
  all_goals try exact hl
  all_goals try (simp only [Forall, Option.toList_none, List.not_mem_nil, false_implies, implies_true])
  all_goals try (simp only [Forall, Option.toList_some, List.mem_singleton]; intro value he; subst value)
  all_goals repeat' first | exact ha | exact hl | decide | constructor
  all_goals norm_num [proj_sz_0, vsize]

/-- Alignment and lane premises are kept explicit at the specification boundary. -/
theorem MemoryOperation.typed (op : MemoryOperation) (C : context) (arg : memarg) (lane : laneidx)
    (mt : memtype) (hm : 0 < C.MEMS.length) (he : C.MEMS[0]! = mt)
    (hC : wf_context C) (hmt : wf_memtype mt) (ha : wf_memarg arg) (h8 : wf_uN 8 lane)
    (halign : (2 : Rat) ^ proj_uN_0 arg.ALIGN ≤ (2 : Rat) ^ op.naturalAlign)
    (hlane : op.laneCount ≠ 0 → proj_uN_0 lane < op.laneCount) :
    Instr_ok C (op.instruction arg lane)
      (.mk_functype (.mk_list op.inputs) (.mk_list op.outputs)) := by
  have hw := op.wellFormed arg lane ha h8
  cases op
  case load =>
    exact Instr_ok.vload_val C  arg mt hm he (by decide) (by convert halign using 1 <;> norm_num [naturalAlign, size]) hC hmt hw
  case load8x8S =>
    exact Instr_ok.vload_pack C 8 8 .S arg mt hm he (by convert halign using 1 <;> norm_num [naturalAlign, size]) hC hmt hw
  case load8x8U =>
    exact Instr_ok.vload_pack C 8 8 .U arg mt hm he (by convert halign using 1 <;> norm_num [naturalAlign, size]) hC hmt hw
  case load16x4S =>
    exact Instr_ok.vload_pack C 16 4 .S arg mt hm he (by convert halign using 1 <;> norm_num [naturalAlign, size]) hC hmt hw
  case load16x4U =>
    exact Instr_ok.vload_pack C 16 4 .U arg mt hm he (by convert halign using 1 <;> norm_num [naturalAlign, size]) hC hmt hw
  case load32x2S =>
    exact Instr_ok.vload_pack C 32 2 .S arg mt hm he (by convert halign using 1 <;> norm_num [naturalAlign, size]) hC hmt hw
  case load32x2U =>
    exact Instr_ok.vload_pack C 32 2 .U arg mt hm he (by convert halign using 1 <;> norm_num [naturalAlign, size]) hC hmt hw
  case splat8 =>
    exact Instr_ok.vload_splat C 8 arg mt hm he (by convert halign using 1 <;> norm_num [naturalAlign, size]) hC hmt hw
  case splat16 =>
    exact Instr_ok.vload_splat C 16 arg mt hm he (by convert halign using 1 <;> norm_num [naturalAlign, size]) hC hmt hw
  case splat32 =>
    exact Instr_ok.vload_splat C 32 arg mt hm he (by convert halign using 1 <;> norm_num [naturalAlign, size]) hC hmt hw
  case splat64 =>
    exact Instr_ok.vload_splat C 64 arg mt hm he (by convert halign using 1 <;> norm_num [naturalAlign, size]) hC hmt hw
  case storeFull =>
    exact Instr_ok.vstore C  arg mt hm he (by decide) (by convert halign using 1 <;> norm_num [naturalAlign, size]) hC hmt hw
  case load8Lane =>
    exact Instr_ok.vload_lane C 8 arg lane mt hm he (by convert halign using 1 <;> norm_num [naturalAlign, size]) (by have h := hlane (by decide); norm_num [laneCount] at h ⊢; exact_mod_cast h) hC hmt hw
  case load16Lane =>
    exact Instr_ok.vload_lane C 16 arg lane mt hm he (by convert halign using 1 <;> norm_num [naturalAlign, size]) (by have h := hlane (by decide); norm_num [laneCount] at h ⊢; exact_mod_cast h) hC hmt hw
  case load32Lane =>
    exact Instr_ok.vload_lane C 32 arg lane mt hm he (by convert halign using 1 <;> norm_num [naturalAlign, size]) (by have h := hlane (by decide); norm_num [laneCount] at h ⊢; exact_mod_cast h) hC hmt hw
  case load64Lane =>
    exact Instr_ok.vload_lane C 64 arg lane mt hm he (by convert halign using 1 <;> norm_num [naturalAlign, size]) (by have h := hlane (by decide); norm_num [laneCount] at h ⊢; exact_mod_cast h) hC hmt hw
  case store8Lane =>
    exact Instr_ok.vstore_lane C 8 arg lane mt hm he (by convert halign using 1 <;> norm_num [naturalAlign, size]) (by have h := hlane (by decide); norm_num [laneCount] at h ⊢; exact_mod_cast h) hC hmt hw
  case store16Lane =>
    exact Instr_ok.vstore_lane C 16 arg lane mt hm he (by convert halign using 1 <;> norm_num [naturalAlign, size]) (by have h := hlane (by decide); norm_num [laneCount] at h ⊢; exact_mod_cast h) hC hmt hw
  case store32Lane =>
    exact Instr_ok.vstore_lane C 32 arg lane mt hm he (by convert halign using 1 <;> norm_num [naturalAlign, size]) (by have h := hlane (by decide); norm_num [laneCount] at h ⊢; exact_mod_cast h) hC hmt hw
  case store64Lane =>
    exact Instr_ok.vstore_lane C 64 arg lane mt hm he (by convert halign using 1 <;> norm_num [naturalAlign, size]) (by have h := hlane (by decide); norm_num [laneCount] at h ⊢; exact_mod_cast h) hC hmt hw
  case load32Zero =>
    exact Instr_ok.vload_zero C 32 arg mt hm he (by convert halign using 1 <;> norm_num [naturalAlign, size]) hC hmt hw
  case load64Zero =>
    exact Instr_ok.vload_zero C 64 arg mt hm he (by convert halign using 1 <;> norm_num [naturalAlign, size]) hC hmt hw

theorem MemoryOperation.principal (op : MemoryOperation) (C : context) (arg : memarg)
    (lane : laneidx) (ins outs : List valtype)
    (ht : Instr_ok C (op.instruction arg lane) (.mk_functype (.mk_list ins) (.mk_list outs))) :
    ins = op.inputs ∧ outs = op.outputs := by
  cases op <;> simp only [instruction] at ht <;> cases ht <;> exact ⟨rfl, rfl⟩

/-- `load64_zero` uses the published opcode 93, correcting the duplicate 92
in the pinned SpecTec binary table without changing its declarative model. -/
theorem MemoryOperation.declared (op : MemoryOperation) (refs : List funcidx) (arg : memarg) (lane : laneidx) :
    DeclaredReferences.Instruction refs (op.instruction arg lane) := by
  cases op <;> simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]

def memoryMeaning (opcode : Nat) : Option MemoryOperation :=
  match opcode with
  | 0 => some .load
  | 1 => some .load8x8S
  | 2 => some .load8x8U
  | 3 => some .load16x4S
  | 4 => some .load16x4U
  | 5 => some .load32x2S
  | 6 => some .load32x2U
  | 7 => some .splat8
  | 8 => some .splat16
  | 9 => some .splat32
  | 10 => some .splat64
  | 11 => some .storeFull
  | 84 => some .load8Lane
  | 85 => some .load16Lane
  | 86 => some .load32Lane
  | 87 => some .load64Lane
  | 88 => some .store8Lane
  | 89 => some .store16Lane
  | 90 => some .store32Lane
  | 91 => some .store64Lane
  | 92 => some .load32Zero
  | 93 => some .load64Zero
  | _ => none

end Itasca.Wasm2.Simd
