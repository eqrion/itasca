import Exec.Interp.StructuredMachine.FloatConstantStep
import Exec.Interp.StructuredMachine.FloatConstantCapacity
namespace Exec.Interp.StructuredMachine.FloatConstant
variable {emission : FunctionEmission} [∀ compiled, FloatHeads (emission compiled)]
open Aeneas Aeneas.Std SpecExt
theorem step_float32_core_bounded_forward {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (sourceStore : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (value : fN) (after : List instr)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (fetchBound : compiled.code.val.length ≤ U32.max)
    (slots : FrameSlots exec raw f)
    (checked : runtime.bytecode.CompiledFunction.well_formed compiled = .ok true)
    (allocated : raw.base.val+compiled.slot_count.val ≤ exec.slots.length)
    (point : FramePoint emission sourceStore raw {f with code := .CONST .F32 (.mk_num__1 .F32 value) :: after} compiled C targets next output)
    (typed : Abs.CoreTyped ⟨sourceStore,ambient,{f with code := .CONST .F32 (.mk_num__1 .F32 value) :: after}::rest,[]⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : Abs.AFrame), raw.pc.val < pc.val ∧
        {out.2.1 with slots := exec.slots} = {exec with frames := exec.frames.set index {raw with pc := pc}} ∧
        FrameSlots out.2.1 {raw with pc := pc} g ∧
        FramePoint emission sourceStore {raw with pc := pc} g compiled C targets next output ∧
        Abs.CoreTyped ⟨sourceStore,ambient,g::rest,[]⟩ ∧ FrameMetadata f g ∧
        (g = {f with code := .CONST .F32 (.mk_num__1 .F32 value) :: after} ∨
          g = {f with code := after,vals := f.vals ++ [.CONST .F32 (.mk_num__1 .F32 value)]}) ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false
          ⟨sourceStore,ambient,{f with code := .CONST .F32 (.mk_num__1 .F32 value) :: after}::rest,[]⟩
          ⟨sourceStore,ambient,g::rest,[]⟩ ∧
        (out.2.1.slots.val = exec.slots.val ∨ ∃ position word, raw.base.val ≤ position ∧
          position < exec.slots.length ∧ out.2.1.slots.val = exec.slots.val.set position word) ⦄ := by
  have sourceSlots := float32_point_capacity compiled checked C f.resultTypes (f.vals.map Code.valueType) targets value after next output raw.pc.val point.code
  have capacity : raw.base.val+Code.slots ((f.locals++f.vals).map Code.valueType) < exec.slots.length := by
    simp only [point.locals,List.map_append,Code.slots_append] at sourceSlots ⊢
    omega
  have pcBound : raw.pc.val < U32.max := by
    rcases corePoint_float32_head value after point.code with ⟨target,forward,fetched,tail⟩ | ⟨dst,bits,valueEq,position,fetched,tail⟩
    · have bound := (List.getElem?_eq_some_iff.mp fetched).1
      omega
    · have bound := (List.getElem?_eq_some_iff.mp fetched).1
      omega
  exact step_float32_core_forward memory hooks floats allocator exec store platform index raw inst compiled C targets next output
    sourceStore ambient f rest value after last frameFound instanceFound codeFound pcBound slots capacity point typed

theorem step_float32_core_bounded {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (sourceStore : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (value : fN) (after : List instr)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (fetchBound : compiled.code.val.length ≤ U32.max)
    (slots : FrameSlots exec raw f)
    (checked : runtime.bytecode.CompiledFunction.well_formed compiled = .ok true)
    (allocated : raw.base.val+compiled.slot_count.val ≤ exec.slots.length)
    (point : FramePoint emission sourceStore raw {f with code := .CONST .F32 (.mk_num__1 .F32 value) :: after} compiled C targets next output)
    (typed : Abs.CoreTyped ⟨sourceStore,ambient,{f with code := .CONST .F32 (.mk_num__1 .F32 value) :: after}::rest,[]⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : Abs.AFrame),
        {out.2.1 with slots := exec.slots} = {exec with frames := exec.frames.set index {raw with pc := pc}} ∧
        FrameSlots out.2.1 {raw with pc := pc} g ∧
        FramePoint emission sourceStore {raw with pc := pc} g compiled C targets next output ∧
        Abs.CoreTyped ⟨sourceStore,ambient,g::rest,[]⟩ ∧ FrameMetadata f g ∧
        (g = {f with code := .CONST .F32 (.mk_num__1 .F32 value) :: after} ∨
          g = {f with code := after,vals := f.vals ++ [.CONST .F32 (.mk_num__1 .F32 value)]}) ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false
          ⟨sourceStore,ambient,{f with code := .CONST .F32 (.mk_num__1 .F32 value) :: after}::rest,[]⟩
          ⟨sourceStore,ambient,g::rest,[]⟩ ∧
        (out.2.1.slots.val = exec.slots.val ∨ ∃ position word, raw.base.val ≤ position ∧
          position < exec.slots.length ∧ out.2.1.slots.val = exec.slots.val.set position word) ⦄ := by
  apply WP.spec_mono (step_float32_core_bounded_forward memory hooks floats allocator exec store platform index raw inst compiled C targets next output sourceStore ambient f rest value after last frameFound instanceFound codeFound fetchBound slots checked allocated point typed)
  rintro out ⟨success,sameStore,samePlatform,pc,g,forward,rest⟩
  exact ⟨success,sameStore,samePlatform,pc,g,rest⟩

theorem step_float64_core_bounded_forward {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (sourceStore : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (value : fN) (after : List instr)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (fetchBound : compiled.code.val.length ≤ U32.max)
    (slots : FrameSlots exec raw f)
    (checked : runtime.bytecode.CompiledFunction.well_formed compiled = .ok true)
    (allocated : raw.base.val+compiled.slot_count.val ≤ exec.slots.length)
    (point : FramePoint emission sourceStore raw {f with code := .CONST .F64 (.mk_num__1 .F64 value) :: after} compiled C targets next output)
    (typed : Abs.CoreTyped ⟨sourceStore,ambient,{f with code := .CONST .F64 (.mk_num__1 .F64 value) :: after}::rest,[]⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : Abs.AFrame), raw.pc.val < pc.val ∧
        {out.2.1 with slots := exec.slots} = {exec with frames := exec.frames.set index {raw with pc := pc}} ∧
        FrameSlots out.2.1 {raw with pc := pc} g ∧
        FramePoint emission sourceStore {raw with pc := pc} g compiled C targets next output ∧
        Abs.CoreTyped ⟨sourceStore,ambient,g::rest,[]⟩ ∧ FrameMetadata f g ∧
        (g = {f with code := .CONST .F64 (.mk_num__1 .F64 value) :: after} ∨
          g = {f with code := after,vals := f.vals ++ [.CONST .F64 (.mk_num__1 .F64 value)]}) ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false
          ⟨sourceStore,ambient,{f with code := .CONST .F64 (.mk_num__1 .F64 value) :: after}::rest,[]⟩
          ⟨sourceStore,ambient,g::rest,[]⟩ ∧
        (out.2.1.slots.val = exec.slots.val ∨ ∃ position word, raw.base.val ≤ position ∧
          position < exec.slots.length ∧ out.2.1.slots.val = exec.slots.val.set position word) ⦄ := by
  have sourceSlots := float64_point_capacity compiled checked C f.resultTypes (f.vals.map Code.valueType) targets value after next output raw.pc.val point.code
  have capacity : raw.base.val+Code.slots ((f.locals++f.vals).map Code.valueType) < exec.slots.length := by
    simp only [point.locals,List.map_append,Code.slots_append] at sourceSlots ⊢
    omega
  have pcBound : raw.pc.val < U32.max := by
    rcases corePoint_float64_head value after point.code with ⟨target,forward,fetched,tail⟩ | ⟨dst,bits,valueEq,position,fetched,tail⟩
    · have bound := (List.getElem?_eq_some_iff.mp fetched).1
      omega
    · have bound := (List.getElem?_eq_some_iff.mp fetched).1
      omega
  exact step_float64_core_forward memory hooks floats allocator exec store platform index raw inst compiled C targets next output
    sourceStore ambient f rest value after last frameFound instanceFound codeFound pcBound slots capacity point typed

theorem step_float64_core_bounded {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (sourceStore : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (value : fN) (after : List instr)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (fetchBound : compiled.code.val.length ≤ U32.max)
    (slots : FrameSlots exec raw f)
    (checked : runtime.bytecode.CompiledFunction.well_formed compiled = .ok true)
    (allocated : raw.base.val+compiled.slot_count.val ≤ exec.slots.length)
    (point : FramePoint emission sourceStore raw {f with code := .CONST .F64 (.mk_num__1 .F64 value) :: after} compiled C targets next output)
    (typed : Abs.CoreTyped ⟨sourceStore,ambient,{f with code := .CONST .F64 (.mk_num__1 .F64 value) :: after}::rest,[]⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : Abs.AFrame),
        {out.2.1 with slots := exec.slots} = {exec with frames := exec.frames.set index {raw with pc := pc}} ∧
        FrameSlots out.2.1 {raw with pc := pc} g ∧
        FramePoint emission sourceStore {raw with pc := pc} g compiled C targets next output ∧
        Abs.CoreTyped ⟨sourceStore,ambient,g::rest,[]⟩ ∧ FrameMetadata f g ∧
        (g = {f with code := .CONST .F64 (.mk_num__1 .F64 value) :: after} ∨
          g = {f with code := after,vals := f.vals ++ [.CONST .F64 (.mk_num__1 .F64 value)]}) ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false
          ⟨sourceStore,ambient,{f with code := .CONST .F64 (.mk_num__1 .F64 value) :: after}::rest,[]⟩
          ⟨sourceStore,ambient,g::rest,[]⟩ ∧
        (out.2.1.slots.val = exec.slots.val ∨ ∃ position word, raw.base.val ≤ position ∧
          position < exec.slots.length ∧ out.2.1.slots.val = exec.slots.val.set position word) ⦄ := by
  apply WP.spec_mono (step_float64_core_bounded_forward memory hooks floats allocator exec store platform index raw inst compiled C targets next output sourceStore ambient f rest value after last frameFound instanceFound codeFound fetchBound slots checked allocated point typed)
  rintro out ⟨success,sameStore,samePlatform,pc,g,forward,rest⟩
  exact ⟨success,sameStore,samePlatform,pc,g,rest⟩


end Exec.Interp.StructuredMachine.FloatConstant
