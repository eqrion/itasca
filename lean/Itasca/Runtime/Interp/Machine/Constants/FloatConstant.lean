import Itasca.Runtime.Interp.Machine.Coverage.OrdinaryHeads
import Itasca.Runtime.Compiler.Local.Lowering.Float.FloatEmissionInversion
import Itasca.Runtime.Interp.Machine.Constants.FloatEmission
import Itasca.Runtime.Interp.Relations.Capacity
import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission
import Itasca.Runtime.Interp.Machine.Constants.FloatSlots
import Itasca.Runtime.Compiler.Local.Control.Segments.Structured
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredComposition
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels
import Itasca.Runtime.Interp.Control.StructuredPoint
import Itasca.Runtime.SourceMachine.ModuleBindingsExtension
import Itasca.Runtime.Interp.Relations.ControlPoint
import Itasca.Runtime.SourceMachine.Core.Typing
import Itasca.Runtime.SourceMachine.Core.Pure
import Itasca.Runtime.Interp.Machine.Control.ForwardJump
import Itasca.Runtime.Interp.Machine.Coverage.SupportedControlSemantics
import Itasca.Runtime.Interp.Machine.Retention.ReturnedOwnership
import Itasca.Runtime.SourceMachine.Core.Bound
import Itasca.Runtime.Interp.Machine.Progress.OrdinaryExecution
import Itasca.Runtime.Spec.Extend

/-!
Floating-point constants through structured machine execution.

Fetch inversion and destination capacity justify the constant bit-pattern write.
The resulting execution lemmas retain ownership and source code bounds for the
supported dispatch, host-site, and source-resource constructions.
-/

/-! ## Float Constant Point -/

section

namespace Itasca.Runtime.Interp.Machine.FloatConstant
variable {jumpTables : List Aeneas.Std.U32}
variable {family : ContextEmission} [FloatHeads family]
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp.FloatConstant
theorem core_point_float32_head {C returns code labels stack pc next output}
    (value : fN) (after : List instr)
    (point : Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
      (.CONST .F32 (.mk_num__1 .F32 value) :: after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
        (.CONST .F32 (.mk_num__1 .F32 value) :: after) target.val next output) ∨
    (∃ dst bits, value = Builtins.floatOfBits 32 bits.val ∧
      dst.val = Compiler.slots C.LOCALS + Compiler.slots stack ∧ code[pc]? = some (.Const32 dst bits) ∧
      Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels
        (stack ++ [.F32]) after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : instr.CONST .F32 (.mk_num__1 .F32 value) :: after = source at relation
  cases relation with
  | linear head ordinary fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    obtain ⟨dst,bits,emitted,result,valueEq,position⟩ := scalar_emission_float32_inv value (FloatHeads.project (.core (.const _ _)) head)
    subst_vars
    have fetch := fragment.fetch (index := 0) (by rfl)
    obtain ⟨_,_,_,_,nextEq⟩ := fragment
    refine Or.inr ⟨dst,bits,rfl,position,by simpa using fetch,?_⟩
    exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
  | skip forward instruction rest =>
    subst_vars
    exact Or.inl ⟨_,forward,instruction,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | _ => cases sourceEq


theorem core_point_float64_head {C returns code labels stack pc next output}
    (value : fN) (after : List instr)
    (point : Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
      (.CONST .F64 (.mk_num__1 .F64 value) :: after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
        (.CONST .F64 (.mk_num__1 .F64 value) :: after) target.val next output) ∨
    (∃ dst bits, value = Builtins.floatOfBits 64 bits.val ∧
      dst.val = Compiler.slots C.LOCALS + Compiler.slots stack ∧ code[pc]? = some (.Const64 dst bits) ∧
      Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels
        (stack ++ [.F64]) after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : instr.CONST .F64 (.mk_num__1 .F64 value) :: after = source at relation
  cases relation with
  | linear head ordinary fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    obtain ⟨dst,bits,emitted,result,valueEq,position⟩ := scalar_emission_float64_inv value (FloatHeads.project (.core (.const _ _)) head)
    subst_vars
    have fetch := fragment.fetch (index := 0) (by rfl)
    obtain ⟨_,_,_,_,nextEq⟩ := fragment
    refine Or.inr ⟨dst,bits,rfl,position,by simpa using fetch,?_⟩
    exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
  | skip forward instruction rest =>
    subst_vars
    exact Or.inl ⟨_,forward,instruction,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | _ => cases sourceEq


end Itasca.Runtime.Interp.Machine.FloatConstant

end

/-! ## Float Constant Capacity -/

section

namespace Itasca.Runtime.Interp.Machine.FloatConstant
variable {family : ContextEmission} [FloatHeads family]
open Aeneas Aeneas.Std

theorem float32_point_capacity (compiled : runtime.bytecode.CompiledFunction)
    (checked : runtime.bytecode.CompiledFunction.well_formed compiled = .ok true)
    (C : context) (returns stack : List valtype) (labels : List Compiler.LabelTarget)
    (value : fN) (after : List instr) (next : Nat) (output : List valtype) :
    ∀ pc, Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS compiled.code.val compiled.jump_tables.val labels stack
      (.CONST .F32 (.mk_num__1 .F32 value)::after) pc next output →
      Compiler.slots C.LOCALS + Compiler.slots stack < compiled.slot_count.val := by
  intro pc point
  generalize measureEq : compiled.code.val.length-pc = measure
  induction measure using Nat.strong_induction_on generalizing pc with
  | h measure ih =>
    rcases core_point_float32_head value after point with ⟨target,forward,fetch,tail⟩ | ⟨dst,bits,valueEq,position,fetch,tail⟩
    · have bound := tail.current.entry_bound
      exact ih (compiled.code.val.length-target.val) (by omega) target.val tail rfl
    · have bound := Compiler.const32_valid_bounds compiled dst bits (Compiler.well_formed_fetched compiled checked pc _ fetch)
      simpa only [position] using bound

theorem float64_point_capacity (compiled : runtime.bytecode.CompiledFunction)
    (checked : runtime.bytecode.CompiledFunction.well_formed compiled = .ok true)
    (C : context) (returns stack : List valtype) (labels : List Compiler.LabelTarget)
    (value : fN) (after : List instr) (next : Nat) (output : List valtype) :
    ∀ pc, Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS compiled.code.val compiled.jump_tables.val labels stack
      (.CONST .F64 (.mk_num__1 .F64 value)::after) pc next output →
      Compiler.slots C.LOCALS + Compiler.slots stack < compiled.slot_count.val := by
  intro pc point
  generalize measureEq : compiled.code.val.length-pc = measure
  induction measure using Nat.strong_induction_on generalizing pc with
  | h measure ih =>
    rcases core_point_float64_head value after point with ⟨target,forward,fetch,tail⟩ | ⟨dst,bits,valueEq,position,fetch,tail⟩
    · have bound := tail.current.entry_bound
      exact ih (compiled.code.val.length-target.val) (by omega) target.val tail rfl
    · have bound := Compiler.const64_valid_bounds compiled dst bits (Compiler.well_formed_fetched compiled checked pc _ fetch)
      simpa only [position] using bound

end Itasca.Runtime.Interp.Machine.FloatConstant

end

/-! ## Float Constant Step -/

section

namespace Itasca.Runtime.Interp.Machine.FloatConstant
open Itasca.Runtime.Interp.FloatConstant
open Aeneas Aeneas.Std SpecExt

theorem step_float32_core_forward {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (sourceStore : _root_.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (value : fN) (after : List instr)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (slots : FrameSlots exec raw f)
    (capacity : raw.base.val+Compiler.slots ((f.locals++f.vals).map Compiler.valueType) < exec.slots.length)
    (point : FramePoint sourceStore raw {f with code := .CONST .F32 (.mk_num__1 .F32 value) :: after} compiled C targets next output)
    (typed : SourceMachine.CoreTyped ⟨sourceStore,ambient,{f with code := .CONST .F32 (.mk_num__1 .F32 value) :: after}::rest,[]⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : SourceMachine.AFrame), raw.pc.val < pc.val ∧
        {out.2.1 with slots := exec.slots} = {exec with frames := exec.frames.set index {raw with pc := pc}} ∧
        FrameSlots out.2.1 {raw with pc := pc} g ∧
        FramePoint sourceStore {raw with pc := pc} g compiled C targets next output ∧
        SourceMachine.CoreTyped ⟨sourceStore,ambient,g::rest,[]⟩ ∧ FrameMetadata f g ∧
        (g = {f with code := .CONST .F32 (.mk_num__1 .F32 value) :: after} ∨
          g = {f with code := after,vals := f.vals ++ [.CONST .F32 (.mk_num__1 .F32 value)]}) ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false
          ⟨sourceStore,ambient,{f with code := .CONST .F32 (.mk_num__1 .F32 value) :: after}::rest,[]⟩
          ⟨sourceStore,ambient,g::rest,[]⟩ ∧
        (out.2.1.slots.val = exec.slots.val ∨ ∃ position word, raw.base.val ≤ position ∧
          position < exec.slots.length ∧ out.2.1.slots.val = exec.slots.val.set position word) ⦄ := by
  rcases core_point_float32_head value after point.code with ⟨target,forward,fetched,tail⟩ | ⟨dst,bits,valueEq,position,fetched,tail⟩
  · have targetPoint : FramePoint sourceStore {raw with pc := target} {f with code := .CONST .F32 (.mk_num__1 .F32 value) :: after} compiled C targets next output :=
      ⟨point.bindings,point.locals,point.labels,tail⟩
    apply WP.spec_mono (step_forward_jump_flat memory hooks floats allocator exec store platform index raw inst compiled
      sourceStore ambient {f with code := .CONST .F32 (.mk_num__1 .F32 value) :: after} rest C targets next output target last frameFound instanceFound codeFound pcBound forward fetched slots targetPoint typed)
    intro out effect
    obtain ⟨success,sameStore,samePlatform,exactState,represented,retained,fresh,simulation⟩ := effect
    refine ⟨success,sameStore,samePlatform,target,_,forward,?_,represented,retained,fresh,⟨rfl,rfl,rfl,rfl⟩,Or.inl rfl,simulation,?_⟩
    · rw [exactState]
    · exact Or.inl (by rw [exactState])
  · subst value
    have destination : dst.val = Compiler.slots ((f.locals++f.vals).map Compiler.valueType) := by
      simpa only [point.locals,List.map_append,Compiler.slots_append] using position
    have frameTyped : SourceMachine.FrameTyped sourceStore {f with code := .CONST .F32 (.mk_num__1 .F32 (Builtins.floatOfBits 32 bits.val)) :: after} [] := by
      cases typed.typed.frames with | cons head _ => exact head
    obtain ⟨nextState,actual,fresh,simulation⟩ := SourceMachine.Core.constant_progress sourceStore ambient f rest after .F32 (.mk_num__1 .F32 (Builtins.floatOfBits 32 bits.val)) typed
    have nextEq : (⟨sourceStore,ambient,{f with code := after,vals := f.vals ++ [.CONST .F32 (.mk_num__1 .F32 (Builtins.floatOfBits 32 bits.val))]}::rest,[]⟩ : SourceMachine.AState) = nextState := SourceMachine.AResult.next.inj actual
    subst nextState
    apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
      (.Const32 dst bits) last frameFound instanceFound codeFound fetched pcBound
    intro pc pcNext
    have nextPoint : FramePoint sourceStore {raw with pc := pc}
        {f with code := after,vals := f.vals ++ [.CONST .F32 (.mk_num__1 .F32 (Builtins.floatOfBits 32 bits.val))]} compiled C targets next output := by
      refine ⟨point.bindings,point.locals,?_,?_⟩
      · have labels : LabelsMatch (f.vals++[]) f.labels targets := by simpa only [List.append_nil] using point.labels
        have heights := SourceMachine.frame_typed_heights frameTyped
        exact labels.replace_suffix heights
      · simpa only [List.map_append,List.map_cons,List.map_nil,Compiler.valueType,valtype_numtype,pcNext] using tail
    apply WP.spec_mono (dispatch_float32_slots memory hooks floats allocator
      {exec with frames := exec.frames.set index {raw with pc := pc}} store platform index raw dst bits f after slots destination
      (by simpa only [destination] using capacity))
    intro out effect
    obtain ⟨success,sameStore,samePlatform,represented,written,unchanged⟩ := effect
    refine ⟨success,sameStore,samePlatform,pc,_,by omega,unchanged,represented,nextPoint,fresh,⟨rfl,rfl,rfl,rfl⟩,Or.inr rfl,?_,?_⟩
    · exact ConcreteSim.of_source _ _ _ _ _ simulation
    · exact Or.inr ⟨raw.base.val+dst.val,_,Nat.le_add_right _ _,by simpa only [destination] using capacity,written⟩

theorem step_float64_core_forward {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (sourceStore : _root_.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (value : fN) (after : List instr)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (slots : FrameSlots exec raw f)
    (capacity : raw.base.val+Compiler.slots ((f.locals++f.vals).map Compiler.valueType) < exec.slots.length)
    (point : FramePoint sourceStore raw {f with code := .CONST .F64 (.mk_num__1 .F64 value) :: after} compiled C targets next output)
    (typed : SourceMachine.CoreTyped ⟨sourceStore,ambient,{f with code := .CONST .F64 (.mk_num__1 .F64 value) :: after}::rest,[]⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : SourceMachine.AFrame), raw.pc.val < pc.val ∧
        {out.2.1 with slots := exec.slots} = {exec with frames := exec.frames.set index {raw with pc := pc}} ∧
        FrameSlots out.2.1 {raw with pc := pc} g ∧
        FramePoint sourceStore {raw with pc := pc} g compiled C targets next output ∧
        SourceMachine.CoreTyped ⟨sourceStore,ambient,g::rest,[]⟩ ∧ FrameMetadata f g ∧
        (g = {f with code := .CONST .F64 (.mk_num__1 .F64 value) :: after} ∨
          g = {f with code := after,vals := f.vals ++ [.CONST .F64 (.mk_num__1 .F64 value)]}) ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false
          ⟨sourceStore,ambient,{f with code := .CONST .F64 (.mk_num__1 .F64 value) :: after}::rest,[]⟩
          ⟨sourceStore,ambient,g::rest,[]⟩ ∧
        (out.2.1.slots.val = exec.slots.val ∨ ∃ position word, raw.base.val ≤ position ∧
          position < exec.slots.length ∧ out.2.1.slots.val = exec.slots.val.set position word) ⦄ := by
  rcases core_point_float64_head value after point.code with ⟨target,forward,fetched,tail⟩ | ⟨dst,bits,valueEq,position,fetched,tail⟩
  · have targetPoint : FramePoint sourceStore {raw with pc := target} {f with code := .CONST .F64 (.mk_num__1 .F64 value) :: after} compiled C targets next output :=
      ⟨point.bindings,point.locals,point.labels,tail⟩
    apply WP.spec_mono (step_forward_jump_flat memory hooks floats allocator exec store platform index raw inst compiled
      sourceStore ambient {f with code := .CONST .F64 (.mk_num__1 .F64 value) :: after} rest C targets next output target last frameFound instanceFound codeFound pcBound forward fetched slots targetPoint typed)
    intro out effect
    obtain ⟨success,sameStore,samePlatform,exactState,represented,retained,fresh,simulation⟩ := effect
    refine ⟨success,sameStore,samePlatform,target,_,forward,?_,represented,retained,fresh,⟨rfl,rfl,rfl,rfl⟩,Or.inl rfl,simulation,?_⟩
    · rw [exactState]
    · exact Or.inl (by rw [exactState])
  · subst value
    have destination : dst.val = Compiler.slots ((f.locals++f.vals).map Compiler.valueType) := by
      simpa only [point.locals,List.map_append,Compiler.slots_append] using position
    have frameTyped : SourceMachine.FrameTyped sourceStore {f with code := .CONST .F64 (.mk_num__1 .F64 (Builtins.floatOfBits 64 bits.val)) :: after} [] := by
      cases typed.typed.frames with | cons head _ => exact head
    obtain ⟨nextState,actual,fresh,simulation⟩ := SourceMachine.Core.constant_progress sourceStore ambient f rest after .F64 (.mk_num__1 .F64 (Builtins.floatOfBits 64 bits.val)) typed
    have nextEq : (⟨sourceStore,ambient,{f with code := after,vals := f.vals ++ [.CONST .F64 (.mk_num__1 .F64 (Builtins.floatOfBits 64 bits.val))]}::rest,[]⟩ : SourceMachine.AState) = nextState := SourceMachine.AResult.next.inj actual
    subst nextState
    apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
      (.Const64 dst bits) last frameFound instanceFound codeFound fetched pcBound
    intro pc pcNext
    have nextPoint : FramePoint sourceStore {raw with pc := pc}
        {f with code := after,vals := f.vals ++ [.CONST .F64 (.mk_num__1 .F64 (Builtins.floatOfBits 64 bits.val))]} compiled C targets next output := by
      refine ⟨point.bindings,point.locals,?_,?_⟩
      · have labels : LabelsMatch (f.vals++[]) f.labels targets := by simpa only [List.append_nil] using point.labels
        have heights := SourceMachine.frame_typed_heights frameTyped
        exact labels.replace_suffix heights
      · simpa only [List.map_append,List.map_cons,List.map_nil,Compiler.valueType,valtype_numtype,pcNext] using tail
    apply WP.spec_mono (dispatch_float64_slots memory hooks floats allocator
      {exec with frames := exec.frames.set index {raw with pc := pc}} store platform index raw dst bits f after slots destination
      (by simpa only [destination] using capacity))
    intro out effect
    obtain ⟨success,sameStore,samePlatform,represented,written,unchanged⟩ := effect
    refine ⟨success,sameStore,samePlatform,pc,_,by omega,unchanged,represented,nextPoint,fresh,⟨rfl,rfl,rfl,rfl⟩,Or.inr rfl,?_,?_⟩
    · exact ConcreteSim.of_source _ _ _ _ _ simulation
    · exact Or.inr ⟨raw.base.val+dst.val,_,Nat.le_add_right _ _,by simpa only [destination] using capacity,written⟩

end Itasca.Runtime.Interp.Machine.FloatConstant

end

/-! ## Float Constant Bounded -/

section

namespace Itasca.Runtime.Interp.Machine.FloatConstant
open Aeneas Aeneas.Std SpecExt
theorem step_float32_core_bounded_forward {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (sourceStore : _root_.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (value : fN) (after : List instr)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (fetchBound : compiled.code.val.length ≤ U32.max)
    (slots : FrameSlots exec raw f)
    (checked : runtime.bytecode.CompiledFunction.well_formed compiled = .ok true)
    (allocated : raw.base.val+compiled.slot_count.val ≤ exec.slots.length)
    (point : FramePoint sourceStore raw {f with code := .CONST .F32 (.mk_num__1 .F32 value) :: after} compiled C targets next output)
    (typed : SourceMachine.CoreTyped ⟨sourceStore,ambient,{f with code := .CONST .F32 (.mk_num__1 .F32 value) :: after}::rest,[]⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : SourceMachine.AFrame), raw.pc.val < pc.val ∧
        {out.2.1 with slots := exec.slots} = {exec with frames := exec.frames.set index {raw with pc := pc}} ∧
        FrameSlots out.2.1 {raw with pc := pc} g ∧
        FramePoint sourceStore {raw with pc := pc} g compiled C targets next output ∧
        SourceMachine.CoreTyped ⟨sourceStore,ambient,g::rest,[]⟩ ∧ FrameMetadata f g ∧
        (g = {f with code := .CONST .F32 (.mk_num__1 .F32 value) :: after} ∨
          g = {f with code := after,vals := f.vals ++ [.CONST .F32 (.mk_num__1 .F32 value)]}) ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false
          ⟨sourceStore,ambient,{f with code := .CONST .F32 (.mk_num__1 .F32 value) :: after}::rest,[]⟩
          ⟨sourceStore,ambient,g::rest,[]⟩ ∧
        (out.2.1.slots.val = exec.slots.val ∨ ∃ position word, raw.base.val ≤ position ∧
          position < exec.slots.length ∧ out.2.1.slots.val = exec.slots.val.set position word) ⦄ := by
  have sourceSlots := float32_point_capacity compiled checked C f.resultTypes (f.vals.map Compiler.valueType) targets value after next output raw.pc.val point.code
  have capacity : raw.base.val+Compiler.slots ((f.locals++f.vals).map Compiler.valueType) < exec.slots.length := by
    simp only [point.locals,List.map_append,Compiler.slots_append] at sourceSlots ⊢
    omega
  have pcBound : raw.pc.val < U32.max := by
    rcases core_point_float32_head value after point.code with ⟨target,forward,fetched,tail⟩ | ⟨dst,bits,valueEq,position,fetched,tail⟩
    · have bound := (List.getElem?_eq_some_iff.mp fetched).1
      omega
    · have bound := (List.getElem?_eq_some_iff.mp fetched).1
      omega
  exact step_float32_core_forward memory hooks floats allocator exec store platform index raw inst compiled C targets next output
    sourceStore ambient f rest value after last frameFound instanceFound codeFound pcBound slots capacity point typed

theorem step_float64_core_bounded_forward {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (sourceStore : _root_.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (value : fN) (after : List instr)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (fetchBound : compiled.code.val.length ≤ U32.max)
    (slots : FrameSlots exec raw f)
    (checked : runtime.bytecode.CompiledFunction.well_formed compiled = .ok true)
    (allocated : raw.base.val+compiled.slot_count.val ≤ exec.slots.length)
    (point : FramePoint sourceStore raw {f with code := .CONST .F64 (.mk_num__1 .F64 value) :: after} compiled C targets next output)
    (typed : SourceMachine.CoreTyped ⟨sourceStore,ambient,{f with code := .CONST .F64 (.mk_num__1 .F64 value) :: after}::rest,[]⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : SourceMachine.AFrame), raw.pc.val < pc.val ∧
        {out.2.1 with slots := exec.slots} = {exec with frames := exec.frames.set index {raw with pc := pc}} ∧
        FrameSlots out.2.1 {raw with pc := pc} g ∧
        FramePoint sourceStore {raw with pc := pc} g compiled C targets next output ∧
        SourceMachine.CoreTyped ⟨sourceStore,ambient,g::rest,[]⟩ ∧ FrameMetadata f g ∧
        (g = {f with code := .CONST .F64 (.mk_num__1 .F64 value) :: after} ∨
          g = {f with code := after,vals := f.vals ++ [.CONST .F64 (.mk_num__1 .F64 value)]}) ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false
          ⟨sourceStore,ambient,{f with code := .CONST .F64 (.mk_num__1 .F64 value) :: after}::rest,[]⟩
          ⟨sourceStore,ambient,g::rest,[]⟩ ∧
        (out.2.1.slots.val = exec.slots.val ∨ ∃ position word, raw.base.val ≤ position ∧
          position < exec.slots.length ∧ out.2.1.slots.val = exec.slots.val.set position word) ⦄ := by
  have sourceSlots := float64_point_capacity compiled checked C f.resultTypes (f.vals.map Compiler.valueType) targets value after next output raw.pc.val point.code
  have capacity : raw.base.val+Compiler.slots ((f.locals++f.vals).map Compiler.valueType) < exec.slots.length := by
    simp only [point.locals,List.map_append,Compiler.slots_append] at sourceSlots ⊢
    omega
  have pcBound : raw.pc.val < U32.max := by
    rcases core_point_float64_head value after point.code with ⟨target,forward,fetched,tail⟩ | ⟨dst,bits,valueEq,position,fetched,tail⟩
    · have bound := (List.getElem?_eq_some_iff.mp fetched).1
      omega
    · have bound := (List.getElem?_eq_some_iff.mp fetched).1
      omega
  exact step_float64_core_forward memory hooks floats allocator exec store platform index raw inst compiled C targets next output
    sourceStore ambient f rest value after last frameFound instanceFound codeFound pcBound slots capacity point typed

end Itasca.Runtime.Interp.Machine.FloatConstant

end

/-! ## Float Constant Execution Owned -/

section

namespace Itasca.Runtime.Interp.Machine.FloatConstant
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Spec
theorem step_float32_execution_owned_forward {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (value : fN) (after : List instr)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := .CONST .F32 (.mk_num__1 .F32 value) :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := .CONST .F32 (.mk_num__1 .F32 value)::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS) :
    let initial : SourceMachine.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .CONST .F32 (.mk_num__1 .F32 value)::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : SourceMachine.AFrame), raw.pc.val < pc.val ∧
        Execution view code store out.2.1 {initial with frames := g::rest} expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial {initial with frames := g::rest} ∧
        (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds initial → SourceMachine.Ownership.StatefulOwned bounds {initial with frames := g::rest}) ∧
        (∀ bound, SourceMachine.CodeBound bound initial → SourceMachine.CodeBound bound {initial with frames := g::rest}) ⦄ := by
  dsimp only
  have top : exec.frames.val.getLast? = some raw := by
    rw [List.getLast?_eq_getElem?]
    have position : exec.frames.val.length-1 = index.val := by change exec.frames.length-1 = index.val; omega
    rw [position]
    exact frameFound
  obtain ⟨boundInst,fn,boundCompiled,signature,owner,member,found,issued,wasm,lookup,signatureFound,moduleEq,resultEq,localsEq,allocated⟩ :=
    (machine.stack.top raw top).binding
  have instEq : boundInst = inst := by rw [instanceFound] at found; exact Option.some.inj found.symm
  subst boundInst
  have compiledEq : boundCompiled = compiled := by rw [codeFound] at lookup; exact Option.some.inj lookup.symm
  subst boundCompiled
  apply WP.spec_mono (step_float32_core_bounded_forward memory hooks floats allocator exec store platform index raw inst compiled C targets next output
    (Store.decodeStore view code store) ambient f rest value after last frameFound instanceFound codeFound program.fetchBound slots program.checked allocated point machine.typed)
  intro out effect
  obtain ⟨success,sameStore,samePlatform,pc,g,forward,fields,represented,retained,fresh,metadata,shape,simulation,footprint⟩ := effect
  have covered : SourceMachine.SupportedState ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
    rcases shape with same | changed
    · rw [same]; exact machine.core
    · apply Machine.core_step_supported machine.typed machine.core
      rw [changed]
      rfl
  have ownership : ∀ bounds, SourceMachine.Ownership.StatefulOwned bounds
      ⟨Store.decodeStore view code store,ambient,{f with code := .CONST .F32 (.mk_num__1 .F32 value)::after}::rest,[]⟩ →
      SourceMachine.Ownership.StatefulOwned bounds ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
    apply Machine.owned_transition machine.typed machine.core
    rcases shape with same | changed
    · exact Or.inl (by rw [same])
    · exact Or.inr (by rw [changed]; rfl)
  have bounded : ∀ bounds, SourceMachine.CodeBound bounds
      ⟨Store.decodeStore view code store,ambient,{f with code := .CONST .F32 (.mk_num__1 .F32 value)::after}::rest,[]⟩ →
      SourceMachine.CodeBound bounds ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
    apply Machine.bound_transition machine.typed machine.core
    rcases shape with same | changed
    · exact Or.inl (by rw [same])
    · exact Or.inr (by rw [changed]; rfl)
  have preserved : SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val := by
    rcases footprint with same | ⟨position,word,above,bound,changed⟩
    · rw [same]; exact .refl _ _
    · rw [changed]; exact .set _ _ _ _ above
  exact ⟨success,sameStore,samePlatform,pc,g,forward,
    Execution.ordinary view code ambient {f with code := .CONST .F32 (.mk_num__1 .F32 value)::after} g rest expected raw.pc.val false machine
      (.refl store) (extend_store_refl _ machine.typed.typed.store) raw index pc last frameFound program
      (.ready retained) represented ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩ fields preserved fresh covered,simulation,ownership,bounded⟩

theorem step_float32_execution_owned {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (value : fN) (after : List instr)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := .CONST .F32 (.mk_num__1 .F32 value) :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := .CONST .F32 (.mk_num__1 .F32 value)::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS) :
    let initial : SourceMachine.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .CONST .F32 (.mk_num__1 .F32 value)::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : SourceMachine.AFrame),
        Execution view code store out.2.1 {initial with frames := g::rest} expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial {initial with frames := g::rest} ∧
        (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds initial → SourceMachine.Ownership.StatefulOwned bounds {initial with frames := g::rest}) ∧
        (∀ bound, SourceMachine.CodeBound bound initial → SourceMachine.CodeBound bound {initial with frames := g::rest}) ⦄ := by
  apply WP.spec_mono (step_float32_execution_owned_forward memory hooks floats allocator exec store platform index raw inst compiled C targets next output view code ambient f rest value after last frameFound instanceFound codeFound slots point expected machine program)
  rintro out ⟨success,sameStore,samePlatform,pc,g,forward,rest⟩
  exact ⟨success,sameStore,samePlatform,pc,g,rest⟩

theorem step_float64_execution_owned_forward {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (value : fN) (after : List instr)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := .CONST .F64 (.mk_num__1 .F64 value) :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := .CONST .F64 (.mk_num__1 .F64 value)::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS) :
    let initial : SourceMachine.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .CONST .F64 (.mk_num__1 .F64 value)::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : SourceMachine.AFrame), raw.pc.val < pc.val ∧
        Execution view code store out.2.1 {initial with frames := g::rest} expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial {initial with frames := g::rest} ∧
        (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds initial → SourceMachine.Ownership.StatefulOwned bounds {initial with frames := g::rest}) ∧
        (∀ bound, SourceMachine.CodeBound bound initial → SourceMachine.CodeBound bound {initial with frames := g::rest}) ⦄ := by
  dsimp only
  have top : exec.frames.val.getLast? = some raw := by
    rw [List.getLast?_eq_getElem?]
    have position : exec.frames.val.length-1 = index.val := by change exec.frames.length-1 = index.val; omega
    rw [position]
    exact frameFound
  obtain ⟨boundInst,fn,boundCompiled,signature,owner,member,found,issued,wasm,lookup,signatureFound,moduleEq,resultEq,localsEq,allocated⟩ :=
    (machine.stack.top raw top).binding
  have instEq : boundInst = inst := by rw [instanceFound] at found; exact Option.some.inj found.symm
  subst boundInst
  have compiledEq : boundCompiled = compiled := by rw [codeFound] at lookup; exact Option.some.inj lookup.symm
  subst boundCompiled
  apply WP.spec_mono (step_float64_core_bounded_forward memory hooks floats allocator exec store platform index raw inst compiled C targets next output
    (Store.decodeStore view code store) ambient f rest value after last frameFound instanceFound codeFound program.fetchBound slots program.checked allocated point machine.typed)
  intro out effect
  obtain ⟨success,sameStore,samePlatform,pc,g,forward,fields,represented,retained,fresh,metadata,shape,simulation,footprint⟩ := effect
  have covered : SourceMachine.SupportedState ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
    rcases shape with same | changed
    · rw [same]; exact machine.core
    · apply Machine.core_step_supported machine.typed machine.core
      rw [changed]
      rfl
  have ownership : ∀ bounds, SourceMachine.Ownership.StatefulOwned bounds
      ⟨Store.decodeStore view code store,ambient,{f with code := .CONST .F64 (.mk_num__1 .F64 value)::after}::rest,[]⟩ →
      SourceMachine.Ownership.StatefulOwned bounds ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
    apply Machine.owned_transition machine.typed machine.core
    rcases shape with same | changed
    · exact Or.inl (by rw [same])
    · exact Or.inr (by rw [changed]; rfl)
  have bounded : ∀ bounds, SourceMachine.CodeBound bounds
      ⟨Store.decodeStore view code store,ambient,{f with code := .CONST .F64 (.mk_num__1 .F64 value)::after}::rest,[]⟩ →
      SourceMachine.CodeBound bounds ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
    apply Machine.bound_transition machine.typed machine.core
    rcases shape with same | changed
    · exact Or.inl (by rw [same])
    · exact Or.inr (by rw [changed]; rfl)
  have preserved : SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val := by
    rcases footprint with same | ⟨position,word,above,bound,changed⟩
    · rw [same]; exact .refl _ _
    · rw [changed]; exact .set _ _ _ _ above
  exact ⟨success,sameStore,samePlatform,pc,g,forward,
    Execution.ordinary view code ambient {f with code := .CONST .F64 (.mk_num__1 .F64 value)::after} g rest expected raw.pc.val false machine
      (.refl store) (extend_store_refl _ machine.typed.typed.store) raw index pc last frameFound program
      (.ready retained) represented ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩ fields preserved fresh covered,simulation,ownership,bounded⟩

theorem step_float64_execution_owned {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (value : fN) (after : List instr)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := .CONST .F64 (.mk_num__1 .F64 value) :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := .CONST .F64 (.mk_num__1 .F64 value)::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS) :
    let initial : SourceMachine.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .CONST .F64 (.mk_num__1 .F64 value)::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : SourceMachine.AFrame),
        Execution view code store out.2.1 {initial with frames := g::rest} expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial {initial with frames := g::rest} ∧
        (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds initial → SourceMachine.Ownership.StatefulOwned bounds {initial with frames := g::rest}) ∧
        (∀ bound, SourceMachine.CodeBound bound initial → SourceMachine.CodeBound bound {initial with frames := g::rest}) ⦄ := by
  apply WP.spec_mono (step_float64_execution_owned_forward memory hooks floats allocator exec store platform index raw inst compiled C targets next output view code ambient f rest value after last frameFound instanceFound codeFound slots point expected machine program)
  rintro out ⟨success,sameStore,samePlatform,pc,g,forward,rest⟩
  exact ⟨success,sameStore,samePlatform,pc,g,rest⟩

end Itasca.Runtime.Interp.Machine.FloatConstant

end
