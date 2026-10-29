import Itasca.Runtime.Interp.Machine.Coverage.OrdinaryHeads
import Itasca.Runtime.Compiler.Local.Lowering.Float.FloatEmissionInversion
import Itasca.Runtime.Interp.Machine.Constants.IntegerEmission
import Itasca.Runtime.Interp.Relations.Capacity
import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission
import Itasca.Runtime.Interp.Machine.Constants.IntegerSlots
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
Integer constants through structured machine execution.

Fetch inversion identifies a forward jump or the constant instruction; checked
capacity then justifies the slot write. The final execution lemmas preserve
ownership and source code bounds for the ordinary-instruction advance proof.
-/

/-! ## Fetch and inversion -/

section

namespace Itasca.Runtime.Interp.Machine.IntegerConstant
variable {jumpTables : List Aeneas.Std.U32}
variable {family : ContextEmission} [FloatHeads family]
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp.IntegerConstant
theorem core_point_integer32_head {C returns code labels stack pc next output}
    (value : U32) (after : List instr)
    (point : Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
      (.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) :: after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
        (.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) :: after) target.val next output) ∨
    (∃ dst bits, value = bits ∧
      dst.val = Compiler.slots C.LOCALS + Compiler.slots stack ∧ code[pc]? = some (.Const32 dst bits) ∧
      Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels
        (stack ++ [.I32]) after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : instr.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) :: after = source at relation
  cases relation with
  | linear head ordinary fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    obtain ⟨dst,bits,emitted,result,valueEq,position⟩ := scalar_emission_integer32_inv value (FloatHeads.project (.core (.pure (.const .I32 (.mk_uN value.val)))) head)
    subst_vars
    have fetch := fragment.fetch (index := 0) (by rfl)
    obtain ⟨_,_,_,_,nextEq⟩ := fragment
    refine Or.inr ⟨dst,bits,rfl,position,by simpa using fetch,?_⟩
    exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
  | skip forward instruction rest =>
    subst_vars
    exact Or.inl ⟨_,forward,instruction,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | _ => cases sourceEq


theorem core_point_integer64_head {C returns code labels stack pc next output}
    (value : U64) (after : List instr)
    (point : Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
      (.CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) :: after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
        (.CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) :: after) target.val next output) ∨
    (∃ dst bits, value = bits ∧
      dst.val = Compiler.slots C.LOCALS + Compiler.slots stack ∧ code[pc]? = some (.Const64 dst bits) ∧
      Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels
        (stack ++ [.I64]) after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : instr.CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) :: after = source at relation
  cases relation with
  | linear head ordinary fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    obtain ⟨dst,bits,emitted,result,valueEq,position⟩ := scalar_emission_integer64_inv value (FloatHeads.project (.core (.pure (.const .I64 (.mk_uN value.val)))) head)
    subst_vars
    have fetch := fragment.fetch (index := 0) (by rfl)
    obtain ⟨_,_,_,_,nextEq⟩ := fragment
    refine Or.inr ⟨dst,bits,rfl,position,by simpa using fetch,?_⟩
    exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
  | skip forward instruction rest =>
    subst_vars
    exact Or.inl ⟨_,forward,instruction,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | _ => cases sourceEq


end Itasca.Runtime.Interp.Machine.IntegerConstant

end

/-! ## Destination capacity -/

section

namespace Itasca.Runtime.Interp.Machine.IntegerConstant
variable {family : ContextEmission} [FloatHeads family]
open Aeneas Aeneas.Std

theorem integer32_point_capacity (compiled : runtime.bytecode.CompiledFunction)
    (checked : runtime.bytecode.CompiledFunction.well_formed compiled = .ok true)
    (C : context) (returns stack : List valtype) (labels : List Compiler.LabelTarget)
    (value : U32) (after : List instr) (next : Nat) (output : List valtype) :
    ∀ pc, Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS compiled.code.val compiled.jump_tables.val labels stack
      (.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))::after) pc next output →
      Compiler.slots C.LOCALS + Compiler.slots stack < compiled.slot_count.val := by
  intro pc point
  generalize measureEq : compiled.code.val.length-pc = measure
  induction measure using Nat.strong_induction_on generalizing pc with
  | h measure ih =>
    rcases core_point_integer32_head value after point with ⟨target,forward,fetch,tail⟩ | ⟨dst,bits,valueEq,position,fetch,tail⟩
    · have bound := tail.current.entry_bound
      exact ih (compiled.code.val.length-target.val) (by omega) target.val tail rfl
    · have bound := Compiler.const32_valid_bounds compiled dst bits (Compiler.well_formed_fetched compiled checked pc _ fetch)
      simpa only [position] using bound

theorem integer64_point_capacity (compiled : runtime.bytecode.CompiledFunction)
    (checked : runtime.bytecode.CompiledFunction.well_formed compiled = .ok true)
    (C : context) (returns stack : List valtype) (labels : List Compiler.LabelTarget)
    (value : U64) (after : List instr) (next : Nat) (output : List valtype) :
    ∀ pc, Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS compiled.code.val compiled.jump_tables.val labels stack
      (.CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val))::after) pc next output →
      Compiler.slots C.LOCALS + Compiler.slots stack < compiled.slot_count.val := by
  intro pc point
  generalize measureEq : compiled.code.val.length-pc = measure
  induction measure using Nat.strong_induction_on generalizing pc with
  | h measure ih =>
    rcases core_point_integer64_head value after point with ⟨target,forward,fetch,tail⟩ | ⟨dst,bits,valueEq,position,fetch,tail⟩
    · have bound := tail.current.entry_bound
      exact ih (compiled.code.val.length-target.val) (by omega) target.val tail rfl
    · have bound := Compiler.const64_valid_bounds compiled dst bits (Compiler.well_formed_fetched compiled checked pc _ fetch)
      simpa only [position] using bound

end Itasca.Runtime.Interp.Machine.IntegerConstant

end

/-! ## Concrete step -/

section

namespace Itasca.Runtime.Interp.Machine.IntegerConstant
open Itasca.Runtime.Interp.IntegerConstant
open Aeneas Aeneas.Std SpecExt

theorem step_integer32_core_forward {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (sourceStore : _root_.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (value : U32) (after : List instr)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (slots : FrameSlots exec raw f)
    (capacity : raw.base.val+Compiler.slots ((f.locals++f.vals).map Compiler.valueType) < exec.slots.length)
    (point : FramePoint sourceStore raw {f with code := .CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) :: after} compiled C targets next output)
    (typed : SourceMachine.CoreTyped ⟨sourceStore,ambient,{f with code := .CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) :: after}::rest,[]⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : SourceMachine.AFrame), raw.pc.val < pc.val ∧
        {out.2.1 with slots := exec.slots} = {exec with frames := exec.frames.set index {raw with pc := pc}} ∧
        FrameSlots out.2.1 {raw with pc := pc} g ∧
        FramePoint sourceStore {raw with pc := pc} g compiled C targets next output ∧
        SourceMachine.CoreTyped ⟨sourceStore,ambient,g::rest,[]⟩ ∧ FrameMetadata f g ∧
        (g = {f with code := .CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) :: after} ∨
          g = {f with code := after,vals := f.vals ++ [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))]}) ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false
          ⟨sourceStore,ambient,{f with code := .CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) :: after}::rest,[]⟩
          ⟨sourceStore,ambient,g::rest,[]⟩ ∧
        (out.2.1.slots.val = exec.slots.val ∨ ∃ position word, raw.base.val ≤ position ∧
          position < exec.slots.length ∧ out.2.1.slots.val = exec.slots.val.set position word) ⦄ := by
  rcases core_point_integer32_head value after point.code with ⟨target,forward,fetched,tail⟩ | ⟨dst,bits,valueEq,position,fetched,tail⟩
  · have targetPoint : FramePoint sourceStore {raw with pc := target} {f with code := .CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) :: after} compiled C targets next output :=
      ⟨point.bindings,point.locals,point.labels,tail⟩
    apply WP.spec_mono (step_forward_jump_flat memory hooks floats allocator exec store platform index raw inst compiled
      sourceStore ambient {f with code := .CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) :: after} rest C targets next output target last frameFound instanceFound codeFound pcBound forward fetched slots targetPoint typed)
    intro out effect
    obtain ⟨success,sameStore,samePlatform,exactState,represented,retained,fresh,simulation⟩ := effect
    refine ⟨success,sameStore,samePlatform,target,_,forward,?_,represented,retained,fresh,⟨rfl,rfl,rfl,rfl⟩,Or.inl rfl,simulation,?_⟩
    · rw [exactState]
    · exact Or.inl (by rw [exactState])
  · subst value
    have destination : dst.val = Compiler.slots ((f.locals++f.vals).map Compiler.valueType) := by
      simpa only [point.locals,List.map_append,Compiler.slots_append] using position
    have frameTyped : SourceMachine.FrameTyped sourceStore {f with code := .CONST .I32 (.mk_num__0 .I32 (.mk_uN bits.val)) :: after} [] := by
      cases typed.typed.frames with | cons head _ => exact head
    obtain ⟨nextState,actual,fresh,simulation⟩ := SourceMachine.Core.constant_progress sourceStore ambient f rest after .I32 (.mk_num__0 .I32 (.mk_uN bits.val)) typed
    have nextEq : (⟨sourceStore,ambient,{f with code := after,vals := f.vals ++ [.CONST .I32 (.mk_num__0 .I32 (.mk_uN bits.val))]}::rest,[]⟩ : SourceMachine.AState) = nextState := SourceMachine.AResult.next.inj actual
    subst nextState
    apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
      (.Const32 dst bits) last frameFound instanceFound codeFound fetched pcBound
    intro pc pcNext
    have nextPoint : FramePoint sourceStore {raw with pc := pc}
        {f with code := after,vals := f.vals ++ [.CONST .I32 (.mk_num__0 .I32 (.mk_uN bits.val))]} compiled C targets next output := by
      refine ⟨point.bindings,point.locals,?_,?_⟩
      · have labels : LabelsMatch (f.vals++[]) f.labels targets := by simpa only [List.append_nil] using point.labels
        have heights := SourceMachine.frame_typed_heights frameTyped
        exact labels.replace_suffix heights
      · simpa only [List.map_append,List.map_cons,List.map_nil,Compiler.valueType,valtype_numtype,pcNext] using tail
    apply WP.spec_mono (dispatch_integer32_slots memory hooks floats allocator
      {exec with frames := exec.frames.set index {raw with pc := pc}} store platform index raw dst bits f after slots destination
      (by simpa only [destination] using capacity))
    intro out effect
    obtain ⟨success,sameStore,samePlatform,represented,written,unchanged⟩ := effect
    refine ⟨success,sameStore,samePlatform,pc,_,by omega,unchanged,represented,nextPoint,fresh,⟨rfl,rfl,rfl,rfl⟩,Or.inr rfl,?_,?_⟩
    · exact ConcreteSim.of_source _ _ _ _ _ simulation
    · exact Or.inr ⟨raw.base.val+dst.val,_,Nat.le_add_right _ _,by simpa only [destination] using capacity,written⟩

theorem step_integer64_core_forward {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (sourceStore : _root_.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (value : U64) (after : List instr)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (slots : FrameSlots exec raw f)
    (capacity : raw.base.val+Compiler.slots ((f.locals++f.vals).map Compiler.valueType) < exec.slots.length)
    (point : FramePoint sourceStore raw {f with code := .CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) :: after} compiled C targets next output)
    (typed : SourceMachine.CoreTyped ⟨sourceStore,ambient,{f with code := .CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) :: after}::rest,[]⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : SourceMachine.AFrame), raw.pc.val < pc.val ∧
        {out.2.1 with slots := exec.slots} = {exec with frames := exec.frames.set index {raw with pc := pc}} ∧
        FrameSlots out.2.1 {raw with pc := pc} g ∧
        FramePoint sourceStore {raw with pc := pc} g compiled C targets next output ∧
        SourceMachine.CoreTyped ⟨sourceStore,ambient,g::rest,[]⟩ ∧ FrameMetadata f g ∧
        (g = {f with code := .CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) :: after} ∨
          g = {f with code := after,vals := f.vals ++ [.CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val))]}) ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false
          ⟨sourceStore,ambient,{f with code := .CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) :: after}::rest,[]⟩
          ⟨sourceStore,ambient,g::rest,[]⟩ ∧
        (out.2.1.slots.val = exec.slots.val ∨ ∃ position word, raw.base.val ≤ position ∧
          position < exec.slots.length ∧ out.2.1.slots.val = exec.slots.val.set position word) ⦄ := by
  rcases core_point_integer64_head value after point.code with ⟨target,forward,fetched,tail⟩ | ⟨dst,bits,valueEq,position,fetched,tail⟩
  · have targetPoint : FramePoint sourceStore {raw with pc := target} {f with code := .CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) :: after} compiled C targets next output :=
      ⟨point.bindings,point.locals,point.labels,tail⟩
    apply WP.spec_mono (step_forward_jump_flat memory hooks floats allocator exec store platform index raw inst compiled
      sourceStore ambient {f with code := .CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) :: after} rest C targets next output target last frameFound instanceFound codeFound pcBound forward fetched slots targetPoint typed)
    intro out effect
    obtain ⟨success,sameStore,samePlatform,exactState,represented,retained,fresh,simulation⟩ := effect
    refine ⟨success,sameStore,samePlatform,target,_,forward,?_,represented,retained,fresh,⟨rfl,rfl,rfl,rfl⟩,Or.inl rfl,simulation,?_⟩
    · rw [exactState]
    · exact Or.inl (by rw [exactState])
  · subst value
    have destination : dst.val = Compiler.slots ((f.locals++f.vals).map Compiler.valueType) := by
      simpa only [point.locals,List.map_append,Compiler.slots_append] using position
    have frameTyped : SourceMachine.FrameTyped sourceStore {f with code := .CONST .I64 (.mk_num__0 .I64 (.mk_uN bits.val)) :: after} [] := by
      cases typed.typed.frames with | cons head _ => exact head
    obtain ⟨nextState,actual,fresh,simulation⟩ := SourceMachine.Core.constant_progress sourceStore ambient f rest after .I64 (.mk_num__0 .I64 (.mk_uN bits.val)) typed
    have nextEq : (⟨sourceStore,ambient,{f with code := after,vals := f.vals ++ [.CONST .I64 (.mk_num__0 .I64 (.mk_uN bits.val))]}::rest,[]⟩ : SourceMachine.AState) = nextState := SourceMachine.AResult.next.inj actual
    subst nextState
    apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
      (.Const64 dst bits) last frameFound instanceFound codeFound fetched pcBound
    intro pc pcNext
    have nextPoint : FramePoint sourceStore {raw with pc := pc}
        {f with code := after,vals := f.vals ++ [.CONST .I64 (.mk_num__0 .I64 (.mk_uN bits.val))]} compiled C targets next output := by
      refine ⟨point.bindings,point.locals,?_,?_⟩
      · have labels : LabelsMatch (f.vals++[]) f.labels targets := by simpa only [List.append_nil] using point.labels
        have heights := SourceMachine.frame_typed_heights frameTyped
        exact labels.replace_suffix heights
      · simpa only [List.map_append,List.map_cons,List.map_nil,Compiler.valueType,valtype_numtype,pcNext] using tail
    apply WP.spec_mono (dispatch_integer64_slots memory hooks floats allocator
      {exec with frames := exec.frames.set index {raw with pc := pc}} store platform index raw dst bits f after slots destination
      (by simpa only [destination] using capacity))
    intro out effect
    obtain ⟨success,sameStore,samePlatform,represented,written,unchanged⟩ := effect
    refine ⟨success,sameStore,samePlatform,pc,_,by omega,unchanged,represented,nextPoint,fresh,⟨rfl,rfl,rfl,rfl⟩,Or.inr rfl,?_,?_⟩
    · exact ConcreteSim.of_source _ _ _ _ _ simulation
    · exact Or.inr ⟨raw.base.val+dst.val,_,Nat.le_add_right _ _,by simpa only [destination] using capacity,written⟩

end Itasca.Runtime.Interp.Machine.IntegerConstant

end

/-! ## Checked frame bounds -/

section

namespace Itasca.Runtime.Interp.Machine.IntegerConstant
open Aeneas Aeneas.Std SpecExt
theorem step_integer32_core_bounded_forward {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (sourceStore : _root_.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (value : U32) (after : List instr)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (fetchBound : compiled.code.val.length ≤ U32.max)
    (slots : FrameSlots exec raw f)
    (checked : runtime.bytecode.CompiledFunction.well_formed compiled = .ok true)
    (allocated : raw.base.val+compiled.slot_count.val ≤ exec.slots.length)
    (point : FramePoint sourceStore raw {f with code := .CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) :: after} compiled C targets next output)
    (typed : SourceMachine.CoreTyped ⟨sourceStore,ambient,{f with code := .CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) :: after}::rest,[]⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : SourceMachine.AFrame), raw.pc.val < pc.val ∧
        {out.2.1 with slots := exec.slots} = {exec with frames := exec.frames.set index {raw with pc := pc}} ∧
        FrameSlots out.2.1 {raw with pc := pc} g ∧
        FramePoint sourceStore {raw with pc := pc} g compiled C targets next output ∧
        SourceMachine.CoreTyped ⟨sourceStore,ambient,g::rest,[]⟩ ∧ FrameMetadata f g ∧
        (g = {f with code := .CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) :: after} ∨
          g = {f with code := after,vals := f.vals ++ [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))]}) ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false
          ⟨sourceStore,ambient,{f with code := .CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) :: after}::rest,[]⟩
          ⟨sourceStore,ambient,g::rest,[]⟩ ∧
        (out.2.1.slots.val = exec.slots.val ∨ ∃ position word, raw.base.val ≤ position ∧
          position < exec.slots.length ∧ out.2.1.slots.val = exec.slots.val.set position word) ⦄ := by
  have sourceSlots := integer32_point_capacity compiled checked C f.resultTypes (f.vals.map Compiler.valueType) targets value after next output raw.pc.val point.code
  have capacity : raw.base.val+Compiler.slots ((f.locals++f.vals).map Compiler.valueType) < exec.slots.length := by
    simp only [point.locals,List.map_append,Compiler.slots_append] at sourceSlots ⊢
    omega
  have pcBound : raw.pc.val < U32.max := by
    rcases core_point_integer32_head value after point.code with ⟨target,forward,fetched,tail⟩ | ⟨dst,bits,valueEq,position,fetched,tail⟩
    · have bound := (List.getElem?_eq_some_iff.mp fetched).1
      omega
    · have bound := (List.getElem?_eq_some_iff.mp fetched).1
      omega
  exact step_integer32_core_forward memory hooks floats allocator exec store platform index raw inst compiled C targets next output
    sourceStore ambient f rest value after last frameFound instanceFound codeFound pcBound slots capacity point typed

theorem step_integer64_core_bounded_forward {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (sourceStore : _root_.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (value : U64) (after : List instr)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (fetchBound : compiled.code.val.length ≤ U32.max)
    (slots : FrameSlots exec raw f)
    (checked : runtime.bytecode.CompiledFunction.well_formed compiled = .ok true)
    (allocated : raw.base.val+compiled.slot_count.val ≤ exec.slots.length)
    (point : FramePoint sourceStore raw {f with code := .CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) :: after} compiled C targets next output)
    (typed : SourceMachine.CoreTyped ⟨sourceStore,ambient,{f with code := .CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) :: after}::rest,[]⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : SourceMachine.AFrame), raw.pc.val < pc.val ∧
        {out.2.1 with slots := exec.slots} = {exec with frames := exec.frames.set index {raw with pc := pc}} ∧
        FrameSlots out.2.1 {raw with pc := pc} g ∧
        FramePoint sourceStore {raw with pc := pc} g compiled C targets next output ∧
        SourceMachine.CoreTyped ⟨sourceStore,ambient,g::rest,[]⟩ ∧ FrameMetadata f g ∧
        (g = {f with code := .CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) :: after} ∨
          g = {f with code := after,vals := f.vals ++ [.CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val))]}) ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false
          ⟨sourceStore,ambient,{f with code := .CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) :: after}::rest,[]⟩
          ⟨sourceStore,ambient,g::rest,[]⟩ ∧
        (out.2.1.slots.val = exec.slots.val ∨ ∃ position word, raw.base.val ≤ position ∧
          position < exec.slots.length ∧ out.2.1.slots.val = exec.slots.val.set position word) ⦄ := by
  have sourceSlots := integer64_point_capacity compiled checked C f.resultTypes (f.vals.map Compiler.valueType) targets value after next output raw.pc.val point.code
  have capacity : raw.base.val+Compiler.slots ((f.locals++f.vals).map Compiler.valueType) < exec.slots.length := by
    simp only [point.locals,List.map_append,Compiler.slots_append] at sourceSlots ⊢
    omega
  have pcBound : raw.pc.val < U32.max := by
    rcases core_point_integer64_head value after point.code with ⟨target,forward,fetched,tail⟩ | ⟨dst,bits,valueEq,position,fetched,tail⟩
    · have bound := (List.getElem?_eq_some_iff.mp fetched).1
      omega
    · have bound := (List.getElem?_eq_some_iff.mp fetched).1
      omega
  exact step_integer64_core_forward memory hooks floats allocator exec store platform index raw inst compiled C targets next output
    sourceStore ambient f rest value after last frameFound instanceFound codeFound pcBound slots capacity point typed

end Itasca.Runtime.Interp.Machine.IntegerConstant

end

/-! ## Execution and ownership -/

section

namespace Itasca.Runtime.Interp.Machine.IntegerConstant
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Spec
theorem step_integer32_execution_owned_forward {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (value : U32) (after : List instr)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := .CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := .CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS) :
    let initial : SourceMachine.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))::after}::rest,[]⟩
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
  apply WP.spec_mono (step_integer32_core_bounded_forward memory hooks floats allocator exec store platform index raw inst compiled C targets next output
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
      ⟨Store.decodeStore view code store,ambient,{f with code := .CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))::after}::rest,[]⟩ →
      SourceMachine.Ownership.StatefulOwned bounds ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
    apply Machine.owned_transition machine.typed machine.core
    rcases shape with same | changed
    · exact Or.inl (by rw [same])
    · exact Or.inr (by rw [changed]; rfl)
  have bounded : ∀ bounds, SourceMachine.CodeBound bounds
      ⟨Store.decodeStore view code store,ambient,{f with code := .CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))::after}::rest,[]⟩ →
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
    Execution.ordinary view code ambient {f with code := .CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))::after} g rest expected raw.pc.val false machine
      (.refl store) (extend_store_refl _ machine.typed.typed.store) raw index pc last frameFound program
      (.ready retained) represented ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩ fields preserved fresh covered,simulation,ownership,bounded⟩

theorem step_integer64_execution_owned_forward {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (value : U64) (after : List instr)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := .CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := .CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val))::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS) :
    let initial : SourceMachine.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val))::after}::rest,[]⟩
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
  apply WP.spec_mono (step_integer64_core_bounded_forward memory hooks floats allocator exec store platform index raw inst compiled C targets next output
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
      ⟨Store.decodeStore view code store,ambient,{f with code := .CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val))::after}::rest,[]⟩ →
      SourceMachine.Ownership.StatefulOwned bounds ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
    apply Machine.owned_transition machine.typed machine.core
    rcases shape with same | changed
    · exact Or.inl (by rw [same])
    · exact Or.inr (by rw [changed]; rfl)
  have bounded : ∀ bounds, SourceMachine.CodeBound bounds
      ⟨Store.decodeStore view code store,ambient,{f with code := .CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val))::after}::rest,[]⟩ →
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
    Execution.ordinary view code ambient {f with code := .CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val))::after} g rest expected raw.pc.val false machine
      (.refl store) (extend_store_refl _ machine.typed.typed.store) raw index pc last frameFound program
      (.ready retained) represented ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩ fields preserved fresh covered,simulation,ownership,bounded⟩

end Itasca.Runtime.Interp.Machine.IntegerConstant

end
