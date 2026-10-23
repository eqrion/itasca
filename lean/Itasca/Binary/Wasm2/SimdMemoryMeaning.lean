import Itasca.Binary.Wasm2.SimdLaneMeaning

/-!
# Wasm 2.0 SIMD memory instructions

`Simd.MemoryOperation` lists the vector loads, stores, splat loads, zero-extending loads and lane
loads and stores, with their natural alignment, lane count and stack types.
`MemoryOperation.typed` shows that `Instr_ok` types each when the memory exists and the alignment
and lane are in bounds, `MemoryOperation.principal` recovers the stack effect, and `memoryMeaning`
maps subopcodes 0 to 11 and 84 to 93 to operations. `lane_pure_none`, `memory_pure_none` and
`memory_lane_none` show that the SIMD opcode tables do not overlap.
-/

namespace Itasca.Wasm2.Simd

/-- The vector memory instructions of Wasm 2.0. -/
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

/-- The natural alignment exponent of a memory operation. -/
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

/-- The lane count of a lane load or store, and 0 for the other operations. -/
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

/-- Whether the operation writes memory. -/
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

/-- The SpecTec instruction of a memory operation at a memory argument and lane index. The lane
index is ignored by operations without lanes. -/
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

/-- The operand types of a memory operation. -/
def MemoryOperation.inputs (op : MemoryOperation) : List valtype :=
  if op.store || op.laneCount != 0 then [.I32, .V128] else [.I32]

/-- The result types of a memory operation. -/
def MemoryOperation.outputs (op : MemoryOperation) : List valtype :=
  if op.store then [] else [.V128]

/-- A memory operation with a well-formed memory argument and byte lane index is well formed. -/
theorem MemoryOperation.wellFormed (op : MemoryOperation) (arg : memarg) (lane : laneidx)
    (ha : wf_memarg arg) (hl : wf_uN 8 lane) : wf_instr (op.instruction arg lane) := by
  cases op <;> simp only [instruction]
  all_goals constructor
  all_goals try exact ha
  all_goals try exact hl
  all_goals try (simp only [Forall, Option.toList_none, List.not_mem_nil, false_implies, implies_true])
  all_goals try (simp only [Option.toList_some, List.mem_singleton]; intro value he; subst value)
  all_goals repeat' first | exact ha | exact hl | decide | constructor
  all_goals norm_num [proj_sz_0, vsize]

/-- A memory operation has its stack effect under `Instr_ok`, given memory zero, an alignment within
the natural alignment and an in-range lane for lane operations. -/
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
    exact Instr_ok.vload_val C  arg mt hm he (by decide) (by convert halign using 1; norm_num [naturalAlign, size]) hC hmt hw
  case load8x8S =>
    exact Instr_ok.vload_pack C 8 8 .S arg mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) hC hmt hw
  case load8x8U =>
    exact Instr_ok.vload_pack C 8 8 .U arg mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) hC hmt hw
  case load16x4S =>
    exact Instr_ok.vload_pack C 16 4 .S arg mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) hC hmt hw
  case load16x4U =>
    exact Instr_ok.vload_pack C 16 4 .U arg mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) hC hmt hw
  case load32x2S =>
    exact Instr_ok.vload_pack C 32 2 .S arg mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) hC hmt hw
  case load32x2U =>
    exact Instr_ok.vload_pack C 32 2 .U arg mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) hC hmt hw
  case splat8 =>
    exact Instr_ok.vload_splat C 8 arg mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) hC hmt hw
  case splat16 =>
    exact Instr_ok.vload_splat C 16 arg mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) hC hmt hw
  case splat32 =>
    exact Instr_ok.vload_splat C 32 arg mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) hC hmt hw
  case splat64 =>
    exact Instr_ok.vload_splat C 64 arg mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) hC hmt hw
  case storeFull =>
    exact Instr_ok.vstore C  arg mt hm he (by decide) (by convert halign using 1; norm_num [naturalAlign, size]) hC hmt hw
  case load8Lane =>
    exact Instr_ok.vload_lane C 8 arg lane mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) (by have h := hlane (by decide); norm_num [laneCount] at h ⊢; exact_mod_cast h) hC hmt hw
  case load16Lane =>
    exact Instr_ok.vload_lane C 16 arg lane mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) (by have h := hlane (by decide); norm_num [laneCount] at h ⊢; exact_mod_cast h) hC hmt hw
  case load32Lane =>
    exact Instr_ok.vload_lane C 32 arg lane mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) (by have h := hlane (by decide); norm_num [laneCount] at h ⊢; exact_mod_cast h) hC hmt hw
  case load64Lane =>
    exact Instr_ok.vload_lane C 64 arg lane mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) (by have h := hlane (by decide); norm_num [laneCount] at h ⊢; exact_mod_cast h) hC hmt hw
  case store8Lane =>
    exact Instr_ok.vstore_lane C 8 arg lane mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) (by have h := hlane (by decide); norm_num [laneCount] at h ⊢; exact_mod_cast h) hC hmt hw
  case store16Lane =>
    exact Instr_ok.vstore_lane C 16 arg lane mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) (by have h := hlane (by decide); norm_num [laneCount] at h ⊢; exact_mod_cast h) hC hmt hw
  case store32Lane =>
    exact Instr_ok.vstore_lane C 32 arg lane mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) (by have h := hlane (by decide); norm_num [laneCount] at h ⊢; exact_mod_cast h) hC hmt hw
  case store64Lane =>
    exact Instr_ok.vstore_lane C 64 arg lane mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) (by have h := hlane (by decide); norm_num [laneCount] at h ⊢; exact_mod_cast h) hC hmt hw
  case load32Zero =>
    exact Instr_ok.vload_zero C 32 arg mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) hC hmt hw
  case load64Zero =>
    exact Instr_ok.vload_zero C 64 arg mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) hC hmt hw

/-- A generated typing of a memory operation has the operation's stack effect. -/
theorem MemoryOperation.principal (op : MemoryOperation) (C : context) (arg : memarg)
    (lane : laneidx) (ins outs : List valtype)
    (ht : Instr_ok C (op.instruction arg lane) (.mk_functype (.mk_list ins) (.mk_list outs))) :
    ins = op.inputs ∧ outs = op.outputs := by
  cases op <;> simp only [instruction] at ht <;> cases ht <;> exact ⟨rfl, rfl⟩

/-- A memory operation has no declared-reference obligation. -/
theorem MemoryOperation.declared (op : MemoryOperation) (refs : List funcidx) (arg : memarg) (lane : laneidx) :
    DeclaredReferences.Instruction refs (op.instruction arg lane) := by
  cases op <;> simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]

/-- The memory operation assigned to a `0xfd` subopcode. `load64_zero` is opcode 93 as in the
published specification. The pinned SpecTec binary table lists 92 twice. -/
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

/-- A subopcode with a lane meaning has no pure meaning. -/
theorem lane_pure_none {opcode : Nat} {op : LaneOperation}
    (h : laneMeaning opcode = some op) : pureMeaning opcode = none := by
  unfold laneMeaning at h
  split at h <;> first | rfl | contradiction

/-- A subopcode with a memory meaning has no pure meaning. -/
theorem memory_pure_none {opcode : Nat} {op : MemoryOperation}
    (h : memoryMeaning opcode = some op) : pureMeaning opcode = none := by
  unfold memoryMeaning at h
  split at h <;> first | rfl | contradiction

/-- A subopcode with a memory meaning has no lane meaning. -/
theorem memory_lane_none {opcode : Nat} {op : MemoryOperation}
    (h : memoryMeaning opcode = some op) : laneMeaning opcode = none := by
  unfold memoryMeaning at h
  split at h <;> first | rfl | contradiction

end Itasca.Wasm2.Simd
