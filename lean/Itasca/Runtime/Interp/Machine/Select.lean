import Itasca.Runtime.Interp.Machine.Coverage.OrdinaryHeads
import Itasca.Runtime.Compiler.Local.Lowering.Float.FloatEmissionInversion
import Itasca.Runtime.Interp.State.GlobalCoreEmission
import Itasca.Runtime.Interp.State.GlobalCoreOperands
import Itasca.Runtime.SourceMachine.Core.Trap
import Itasca.Runtime.SourceMachine.Measure
import Itasca.Runtime.SourceMachine.Float.Results
import Itasca.Runtime.SourceMachine.Numeric.Transition
import Itasca.Runtime.SourceMachine.Bound
import Itasca.Runtime.SourceMachine.Supported.PureCoverage
import Itasca.Runtime.SourceMachine.Ownership.Extension
import Itasca.Runtime.SourceMachine.Core.SelectPositive
import Itasca.Runtime.Interp.State.GlobalCoreStep
import Itasca.Runtime.Interp.Relations.Capacity
import Itasca.Runtime.Compiler.Local.Capacity.GlobalCapacity
import Itasca.Runtime.Interp.Machine.Emission.Local
import Itasca.Runtime.Interp.Machine.Normalization.IndexedEmpty
import Itasca.Runtime.Interp.Relations.ReferenceTransfers
import Itasca.Runtime.Interp.Relations.SourceClosure
import Itasca.Runtime.Interp.Relations.PrefixDispatch
import Itasca.Runtime.Interp.Relations.ControlPoint
import Itasca.Runtime.Interp.Numeric.Integer.NumericFetch
import Itasca.Runtime.Interp.Numeric.Integer.NumericCodePoint
import Itasca.Runtime.SourceMachine.Numeric.TransitionSimulation
import Itasca.Runtime.Interp.Machine.Progress.SupportedAdvance
import Itasca.Runtime.Spec.Integer
import Itasca.Runtime.SourceMachine.Numeric.Positive
import Itasca.Runtime.Interp.Machine.Control.BranchSource
import Itasca.Runtime.Interp.Machine.Coverage.RecordingHeads
import Itasca.Runtime.Interp.Machine.Select.Operands
import Itasca.Runtime.Interp.Relations.SelectSlots
import Itasca.Runtime.Interp.Machine.Control.BranchPoint
import Itasca.Runtime.Interp.Machine.Retention.ReturnedOwnership

/-!
Sections, each formerly its own module: Global, Numeric, Select.
-/

/-! ## Global -/

section

/-!
Global reads and writes from structured fetch inversion through preparation and certified step. Whole-execution ownership remains separate: mutation proofs need the certified step without its 150 additional execution dependencies.
-/

/-! ## Global Point -/

section

namespace Itasca.Runtime.Interp.Machine.Global
variable {jumpTables : List Aeneas.Std.U32}
variable {family : ContextEmission} [FloatHeads family]
open Aeneas Aeneas.Std

theorem core_point_global_get_head {C returns code labels stack pc next output}
    (index : Nat) (after : List instr)
    (point : Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
      (.GLOBAL_GET (.mk_uN index) :: after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
        (.GLOBAL_GET (.mk_uN index) :: after) target.val next output) ∨
    (∃ mutability ty idx dst, index = idx.val ∧
      C.GLOBALS[index]? = some (.mk_globaltype mutability ty) ∧
      dst.val = Compiler.slots C.LOCALS + Compiler.slots stack ∧
      code[pc]? = some (Compiler.globalGetInstruction (decide (Compiler.width ty = 2)) dst idx) ∧
      Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels
        (stack ++ [ty]) after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : instr.GLOBAL_GET (.mk_uN index) :: after = source at relation
  cases relation with
  | linear head ordinary fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    obtain ⟨mutability,ty,idx,dst,indexEq,lookup,emitted,result,position⟩ := scalar_emission_global_get_inv index (FloatHeads.project (.core (.global_get (.mk_uN index))) head)
    subst_vars
    have fetch := fragment.fetch (index := 0) (by rfl)
    obtain ⟨_,_,_,_,nextEq⟩ := fragment
    refine Or.inr ⟨mutability,ty,idx,dst,rfl,lookup,position,by simpa using fetch,?_⟩
    exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
  | skip forward instruction rest =>
    subst_vars
    exact Or.inl ⟨_,forward,instruction,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | _ => cases sourceEq

theorem core_point_global_set_head {C returns code labels stack pc next output}
    (index : Nat) (after : List instr)
    (point : Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
      (.GLOBAL_SET (.mk_uN index) :: after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
        (.GLOBAL_SET (.mk_uN index) :: after) target.val next output) ∨
    (∃ front ty idx src, index = idx.val ∧ stack = front ++ [ty] ∧
      C.GLOBALS[index]? = some (.mk_globaltype (some .MUT) ty) ∧
      src.val = Compiler.slots C.LOCALS + Compiler.slots front ∧
      code[pc]? = some (Compiler.globalSetInstruction (decide (Compiler.width ty = 2)) src idx) ∧
      Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels
        front after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : instr.GLOBAL_SET (.mk_uN index) :: after = source at relation
  cases relation with
  | linear head ordinary fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    obtain ⟨front,ty,idx,src,indexEq,input,lookup,emitted,result,position⟩ := scalar_emission_global_set_inv index (FloatHeads.project (.core (.global_set (.mk_uN index))) head)
    subst_vars
    have fetch := fragment.fetch (index := 0) (by rfl)
    obtain ⟨_,_,_,_,nextEq⟩ := fragment
    refine Or.inr ⟨front,ty,idx,src,rfl,rfl,lookup,position,by simpa using fetch,?_⟩
    exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
  | skip forward instruction rest =>
    subst_vars
    exact Or.inl ⟨_,forward,instruction,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | _ => cases sourceEq
end Itasca.Runtime.Interp.Machine.Global

end

/-! ## Global Prepare -/

section

namespace Itasca.Runtime.Interp.Machine.Global
open Aeneas Aeneas.Std SpecExt

theorem core_frame_point_global_get_prepare {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (raw : runtime.interp.Frame)
    (f : SourceMachine.AFrame) (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Compiler.LabelTarget)
    (next : Nat) (output : List valtype) (after : List instr) (index : Nat)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := .GLOBAL_GET (.mk_uN index) :: after} compiled C targets next output) :
    (∃ target : U32, raw.pc.val < target.val ∧ compiled.code.val[raw.pc.val]? = some (.Jump target) ∧
      FramePoint (Store.decodeStore view code store) {raw with pc := target} {f with code := .GLOBAL_GET (.mk_uN index) :: after} compiled C targets next output) ∨
    (∃ idx dst address object, index = idx.val ∧
      inst.globals.val[index]? = some address ∧ store.globals.val[address.index.val]? = some object ∧
      dst.val = Compiler.slots ((f.locals ++ f.vals).map Compiler.valueType) ∧
      compiled.code.val[raw.pc.val]? = some (Compiler.globalGetInstruction (decide (Compiler.width (sourceType object.ty.valtype) = 2)) dst idx) ∧
      Compiler.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS compiled.code.val compiled.jump_tables.val targets
        (f.vals.map Compiler.valueType ++ [sourceType object.ty.valtype]) after (raw.pc.val+1) next output) := by
  rcases core_point_global_get_head index after point.code with ⟨target,forward,fetch,tail⟩ | ⟨mutability,ty,idx,dst,indexEq,lookup,position,fetch,tail⟩
  · exact Or.inl ⟨target,forward,fetch,⟨point.bindings,point.locals,point.labels,tail⟩⟩
  · obtain ⟨address,object,mapped,issued,mutEq,typeEq⟩ := core_global_lookup view code store inst f C index mutability ty moduleEq point.bindings lookup
    refine Or.inr ⟨idx,dst,address,object,indexEq,mapped,issued,?_,?_,?_⟩
    · simpa only [point.locals,List.map_append,Compiler.slots_append] using position
    · simpa only [typeEq] using fetch
    · simpa only [typeEq] using tail

theorem core_frame_point_global_set_prepare {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (raw : runtime.interp.Frame)
    (f : SourceMachine.AFrame) (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Compiler.LabelTarget)
    (next : Nat) (output : List valtype) (after : List instr) (index : Nat)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (typed : SourceMachine.FrameTyped (Store.decodeStore view code store) {f with code := .GLOBAL_SET (.mk_uN index) :: after} [])
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := .GLOBAL_SET (.mk_uN index) :: after} compiled C targets next output) :
    (∃ target : U32, raw.pc.val < target.val ∧ compiled.code.val[raw.pc.val]? = some (.Jump target) ∧
      FramePoint (Store.decodeStore view code store) {raw with pc := target} {f with code := .GLOBAL_SET (.mk_uN index) :: after} compiled C targets next output) ∨
    (∃ front value idx src address object, index = idx.val ∧ f.vals = front ++ [value] ∧ wf_val value ∧
      (∀ label ∈ f.labels, label.height ≤ front.length) ∧
      inst.globals.val[index]? = some address ∧ store.globals.val[address.index.val]? = some object ∧
      object.ty.mutability = .Var ∧ sourceType object.ty.valtype = Compiler.valueType value ∧
      src.val = Compiler.slots ((f.locals ++ front).map Compiler.valueType) ∧
      compiled.code.val[raw.pc.val]? = some (Compiler.globalSetInstruction (decide (Compiler.width (sourceType object.ty.valtype) = 2)) src idx) ∧
      Compiler.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS compiled.code.val compiled.jump_tables.val targets
        (front.map Compiler.valueType) after (raw.pc.val+1) next output) := by
  rcases core_point_global_set_head index after point.code with ⟨target,forward,fetch,tail⟩ | ⟨types,ty,idx,src,indexEq,input,lookup,position,fetch,tail⟩
  · exact Or.inl ⟨target,forward,fetch,⟨point.bindings,point.locals,point.labels,tail⟩⟩
  · obtain ⟨address,object,mapped,issued,mutEq,typeEq⟩ := core_global_lookup view code store inst f C index (some .MUT) ty moduleEq point.bindings lookup
    obtain ⟨front,value,values,valueWf,heights⟩ := global_set_typed_operand f after index typed
    have shape := input
    simp only [values,List.map_append,List.map_cons,List.map_nil] at shape
    have lengthEq : (front.map Compiler.valueType).length = types.length := by
      have lengths := congrArg List.length shape
      simp only [List.length_append,List.length_cons,List.length_nil] at lengths
      omega
    obtain ⟨typesEq,valueEq⟩ := List.append_inj shape lengthEq
    have valueType : Compiler.valueType value = ty := by simpa using valueEq
    have mutable : object.ty.mutability = .Var := by
      cases eq : object.ty.mutability <;> simp_all [Store.decodeMut]
    refine Or.inr ⟨front,value,idx,src,address,object,indexEq,values,valueWf,heights,mapped,issued,mutable,typeEq.trans valueType.symm,?_,?_,?_⟩
    · simpa only [point.locals,List.map_append,Compiler.slots_append,typesEq] using position
    · simpa only [typeEq] using fetch
    · simpa only [typesEq] using tail
end Itasca.Runtime.Interp.Machine.Global

end

/-! ## Global Continue -/

section

namespace Itasca.Runtime.Interp.Machine.Global
open Aeneas Aeneas.Std SpecExt

theorem decode_words_value_type (ty : Itasca.wasm_types.ValueType) (lo hi : U64) :
    Compiler.valueType (Store.decodeWords ty lo hi) = sourceType ty := by
  cases ty <;> simp only [Store.decodeWords,Store.decodeRef,Store.decodeElemType,sourceType]
  all_goals first | rfl | (split <;> rfl)

theorem core_point_global_get_continue {sourceStore raw f compiled C targets next output}
    (point : FramePoint sourceStore raw f compiled C targets next output)
    (value : val) (ty : valtype) (after : List instr)
    (heights : ∀ label ∈ f.labels, label.height ≤ f.vals.length)
    (valueType : Compiler.valueType value = ty)
    (tail : Compiler.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val compiled.jump_tables.val targets (f.vals.map Compiler.valueType ++ [ty]) after (raw.pc.val+1) next output)
    (pc : U32) (pcNext : pc.val = raw.pc.val+1) :
    FramePoint sourceStore {raw with pc := pc} {f with code := after,vals := f.vals ++ [value]}
      compiled C targets next output := by
  refine ⟨point.bindings,point.locals,?_,?_⟩
  · have labels : LabelsMatch (f.vals ++ []) f.labels targets := by simpa only [List.append_nil] using point.labels
    exact labels.replace_suffix heights
  · simpa only [List.map_append,List.map_cons,List.map_nil,valueType,pcNext] using tail

theorem core_point_global_set_continue {before afterStore raw f compiled C targets next output}
    (point : FramePoint before raw f compiled C targets next output)
    (extension : Extend_store before afterStore)
    (front : List val) (value : val) (after : List instr)
    (values : f.vals = front ++ [value])
    (heights : ∀ label ∈ f.labels, label.height ≤ front.length)
    (tail : Compiler.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val compiled.jump_tables.val targets (front.map Compiler.valueType) after (raw.pc.val+1) next output)
    (pc : U32) (pcNext : pc.val = raw.pc.val+1) :
    FramePoint afterStore {raw with pc := pc} {f with code := after,vals := front}
      compiled C targets next output := by
  refine ⟨point.bindings.extend extension,point.locals,?_,?_⟩
  · have labels := point.labels
    rw [values] at labels
    simpa only [List.append_nil] using labels.replace_suffix (after := []) heights
  · simpa only [pcNext] using tail
end Itasca.Runtime.Interp.Machine.Global

end

/-! ## Global Certified Step Owned -/

section

namespace Itasca.Runtime.Interp.Machine.Global
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Spec
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem core_frame_point_global_get_step_owned (platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr) (index : Nat)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (slots : FrameSlots exec raw f) (binding : FrameBinding store exec raw f)
    (last : frameIndex.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (checked : runtime.bytecode.CompiledFunction.well_formed compiled = .ok true)
    (pcBound : raw.pc.val < U32.max)
    (small : ∀ object ∈ store.globals.val, object.ty.valtype = .I32 ∨ object.ty.valtype = .F32 → object.lo.val < 2^32)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := .GLOBAL_GET (.mk_uN index) :: after} compiled C targets next output)
    (typed : SourceMachine.CoreTyped ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_GET (.mk_uN index) :: after} :: rest,[]⟩) :
    let initial : SourceMachine.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_GET (.mk_uN index) :: after} :: rest,[]⟩
    (∃ target : U32, raw.pc.val < target.val ∧ compiled.code.val[raw.pc.val]? = some (.Jump target) ∧
      FramePoint (Store.decodeStore view code store) {raw with pc := target} {f with code := .GLOBAL_GET (.mk_uN index) :: after} compiled C targets next output) ∨
    (runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ nextFrame pc, pc.val = raw.pc.val+1 ∧
        {out.2.1 with slots := exec.slots} = {exec with frames := exec.frames.set frameIndex {raw with pc := pc}} ∧
        SourceMachine.CoreTyped {initial with frames := nextFrame :: rest} ∧
        StepH (SourceMachine.decode initial) [] (SourceMachine.decode {initial with frames := nextFrame :: rest}) ∧
        FrameSlots out.2.1 {raw with pc := pc} nextFrame ∧
        FramePoint (Store.decodeStore view code store) {raw with pc := pc} nextFrame compiled C targets next output ∧ (∃ values, nextFrame = {f with code := after,vals := values}) ∧ SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ∧
        SourceMachine.Core.step initial = .next {initial with frames := nextFrame :: rest} ⦄) := by
  dsimp only
  have frameTyped : SourceMachine.FrameTyped (Store.decodeStore view code store) {f with code := .GLOBAL_GET (.mk_uN index) :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  rcases core_frame_point_global_get_prepare view code store inst raw f compiled C targets next output after index moduleEq point with jump | operation
  · exact Or.inl jump
  · apply Or.inr
    obtain ⟨idx,dst,address,object,indexEq,mapped,issued,position,fetch,tail⟩ := operation
    subst index
    have valid := Compiler.well_formed_fetched compiled checked raw.pc.val _ fetch
    have bound := Compiler.global_get_valid_bounds compiled (sourceType object.ty.valtype) dst idx valid
    have allocated := binding.capacity inst compiled found codeFound
    have capacity : raw.base.val + dst.val + Compiler.width (sourceType object.ty.valtype) ≤ exec.slots.length := by omega
    apply WP.spec_mono (step_global_get_simulation memory hooks floats allocator view code exec store raw dst idx inst address object ambient f rest after platform frameIndex found mapped issued moduleEq slots position capacity
      (small object (List.mem_of_getElem? issued)) compiled last frameFound codeFound fetch pcBound typed)
    intro out effect
    obtain ⟨success,platformSame,storeSame,nextFrame,actual,fresh,source,represented,pc,pcNext,unchanged,prefixEffect⟩ := effect
    have coreStep : SourceMachine.Core.step ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_GET (.mk_uN idx.val) :: after} :: rest,[]⟩ =
        .next ⟨Store.decodeStore view code store,ambient,nextFrame::rest,[]⟩ := by
      simpa only [SourceMachine.Core.step,SourceMachine.Core.instruction,SourceMachine.Core.globalGet] using actual
    have exactStep := core_global_get_value view code store inst address object ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_GET (.mk_uN idx.val) :: after} :: rest,[]⟩ f rest after idx rfl moduleEq mapped issued
    rw [exactStep] at actual
    have frameEq := (List.cons.inj (congrArg SourceMachine.AState.frames (SourceMachine.AResult.next.inj actual))).1
    refine ⟨success,storeSame,platformSame,nextFrame,pc,pcNext,unchanged,fresh,source,represented,?_,?_,prefixEffect,coreStep⟩
    · rw [←frameEq]
      exact core_point_global_get_continue point _ _ after (SourceMachine.frame_typed_heights frameTyped)
        (decode_words_value_type _ _ _) tail pc pcNext
    · exact ⟨_,frameEq.symm⟩

theorem core_frame_point_global_set_step_owned (platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr) (index : Nat)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := .GLOBAL_SET (.mk_uN index) :: after} compiled C targets next output)
    (typed : SourceMachine.CoreTyped ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_SET (.mk_uN index) :: after} :: rest,[]⟩) :
    let initial : SourceMachine.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_SET (.mk_uN index) :: after} :: rest,[]⟩
    (∃ target : U32, raw.pc.val < target.val ∧ compiled.code.val[raw.pc.val]? = some (.Jump target) ∧
      FramePoint (Store.decodeStore view code store) {raw with pc := target} {f with code := .GLOBAL_SET (.mk_uN index) :: after} compiled C targets next output) ∨
    (runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.2 = platform ∧ FrameStoreMetadata store out.2.2.1 ∧
      ∃ nextFrame pc, pc.val = raw.pc.val+1 ∧
        out.2.1 = {exec with frames := exec.frames.set frameIndex {raw with pc := pc}} ∧
        SourceMachine.CoreTyped {initial with store := Store.decodeStore view code out.2.2.1,frames := nextFrame :: rest} ∧
        Extend_store initial.store (Store.decodeStore view code out.2.2.1) ∧
        StepH (SourceMachine.decode initial) [] (SourceMachine.decode {initial with store := Store.decodeStore view code out.2.2.1,frames := nextFrame :: rest}) ∧
        FrameSlots out.2.1 {raw with pc := pc} nextFrame ∧
        FramePoint (Store.decodeStore view code out.2.2.1) {raw with pc := pc} nextFrame compiled C targets next output ∧ (∃ values, nextFrame = {f with code := after,vals := values}) ∧
        SourceMachine.Core.step initial = .next {initial with store := Store.decodeStore view code out.2.2.1,frames := nextFrame :: rest} ⦄) := by
  dsimp only
  have frameTyped : SourceMachine.FrameTyped (Store.decodeStore view code store) {f with code := .GLOBAL_SET (.mk_uN index) :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  rcases core_frame_point_global_set_prepare view code store inst raw f compiled C targets next output after index moduleEq frameTyped point with jump | operation
  · exact Or.inl jump
  · apply Or.inr
    obtain ⟨front,value,idx,src,address,object,indexEq,values,valueWf,heights,mapped,issued,mutable,valueType,position,fetch,tail⟩ := operation
    subst index
    apply WP.spec_mono (step_global_set_simulation memory hooks floats allocator view code exec store raw src idx inst address object ambient f rest after front value platform frameIndex found mapped issued moduleEq slots values position mutable valueWf valueType compiled last frameFound codeFound fetch pcBound typed)
    intro out effect
    obtain ⟨platformSame,success,⟨pc,pcNext,unchanged⟩,metadata,nextFrame,actual,fresh,extension,source,represented⟩ := effect
    have coreStep : SourceMachine.Core.step ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_SET (.mk_uN idx.val) :: after} :: rest,[]⟩ =
        .next ⟨Store.decodeStore view code out.2.2.1,ambient,nextFrame::rest,[]⟩ := by
      simpa only [SourceMachine.Core.step,SourceMachine.Core.instruction,SourceMachine.Core.globalSet,SourceMachine.AFrame.toFrame] using actual
    have typeEq : SourceMachine.valueType value = sourceType object.ty.valtype := by rw [←value_type_eq_abs]; exact valueType.symm
    have exactStep := core_global_set_value view code store inst address object ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_SET (.mk_uN idx.val) :: after} :: rest,[]⟩ f rest after idx front value rfl moduleEq mapped issued values mutable typeEq
    rw [exactStep] at actual
    have frameEq := (List.cons.inj (congrArg SourceMachine.AState.frames (SourceMachine.AResult.next.inj actual))).1
    refine ⟨success,platformSame,metadata,nextFrame,pc,pcNext,unchanged,fresh,extension,source,represented,?_,?_,coreStep⟩
    · rw [←frameEq]
      exact core_point_global_set_continue point extension front value after values heights tail pc pcNext
    · exact ⟨_,frameEq.symm⟩

end Itasca.Runtime.Interp.Machine.Global

end

end

/-! ## Numeric -/

section

/-!
Integer numeric machine fetch, execution and trap classification. The resulting argument is consumed by complete machine advance while preserving its source grammar and store premises.
-/

/-! ## Numeric Inversion -/

section

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std
theorem emission_numeric_pure {compiled C before after emitted} (op : SourceMachine.Numeric.Instruction)
    (head : Interp.emission compiled C before op.source emitted after) :
    Compiler.LinearEmission C.LOCALS before op.source emitted after :=
  scalar_emission_numeric_pure op (FloatHeads.project (.core (.pure (.numeric op))) head)
end Itasca.Runtime.Interp.Machine

end

/-! ## Numeric -/

section

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std SourceMachine.Numeric
theorem step_numeric {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (s : _root_.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (op : Instruction) (after : List instr)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (typed : SourceMachine.CoreTyped ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (point : FramePoint s raw { f with code := op.source :: after }
      compiled C targets next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ((out.1 = .Ok () ∧
      ∃ (pc : U32) (g : SourceMachine.AFrame),
        { out.2.1 with slots := exec.slots } =
          { exec with frames := exec.frames.set index { raw with pc := pc } } ∧
        FrameSlots out.2.1 { raw with pc := pc } g ∧
        FramePoint s { raw with pc := pc } g compiled C targets next output ∧
        SourceMachine.CoreTyped ⟨s, ambient, g :: rest, []⟩ ∧
        FrameMetadata f g ∧
        SourceClosure { f with code := op.source :: after } g ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false
          ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩
          ⟨s, ambient, g :: rest, []⟩ ∧
        SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ∧
        (g = {f with code := op.source :: after} ∨
          SourceMachine.Core.step ⟨s,ambient,{f with code := op.source :: after} :: rest,[]⟩ = .next ⟨s,ambient,g::rest,[]⟩)) ∨
      (∃ trap, out.1 = .Err (.Trap trap) ∧
        (trap = .IntegerDivideByZero ∨ trap = .IntegerOverflow) ∧
        ∃ count, 0 < count ∧ Spec.StepsHN count
          (SourceMachine.decode ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩) []
          ⟨⟨s, ambient⟩, [.TRAP]⟩)) ⦄ := by
  have linear : linearSource op.source = true := by
    cases op <;> (try casesm* Conversion) <;> rfl
  rcases structured_code_linear_inv linear point.code.current with skip | branch
  · obtain ⟨target, forward, fetched, continuation⟩ := skip
    have targetPoint : FramePoint s { raw with pc := target }
        { f with code := op.source :: after } compiled C targets next output :=
      ⟨point.bindings,point.locals,point.labels, ⟨continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩⟩
    apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform
      index raw inst compiled target last hf hi hc pcBound fetched)
    intro out effect
    obtain ⟨success, exactState, sameStore, samePlatform⟩ := effect
    refine ⟨sameStore, samePlatform, .inl ⟨success, target, { f with code := op.source :: after },
      ?_, ?_, targetPoint, typed, ⟨rfl, rfl, rfl, rfl⟩, .refl _, ?_,?_,Or.inl rfl⟩⟩
    · rw [exactState]
    · rw [exactState]
      exact slots
    · exact Or.inl ⟨rfl, dispatch_measure_forward _ _ _ _ forward continuation.entry_bound⟩
    · rw [exactState]
      exact SlotPrefix.refl _ _
  · obtain ⟨middle, emitted, tail, head, fragment, continuation⟩ := branch
    obtain ⟨stack, left, right, shape, emittedEq, middleEq, leftPos, rightPos⟩ := linear_emission_numeric_inv op (emission_numeric_pure op head)
    have frameTyped : SourceMachine.FrameTyped s { f with code := op.source :: after } [] := by
      cases typed.typed.frames with | cons h _ => exact h
    obtain ⟨front, a, b, split, wfFront, heights⟩ := op.typed_operands_bounds frameTyped
    have frontTypes : front.map Compiler.valueType = stack := by
      rw [split, List.map_append, numeric_operand_types] at shape
      exact List.append_cancel_right shape
    have leftPosition : left.val = Compiler.slots ((f.locals ++ front).map Compiler.valueType) := by
      simpa only [point.locals,List.map_append, Compiler.slots_append, frontTypes] using leftPos
    have fetched : compiled.code.val[raw.pc.val]? = some (Compiler.integerInstruction op left left right) := by
      simpa only [Nat.add_zero] using fragment.fetch (index := 0) (by simp only [emittedEq, List.getElem?_cons_zero])
    have endpoint : tail = raw.pc.val + 1 := by
      obtain ⟨_, _, _, _, h⟩ := fragment
      simpa only [emittedEq, List.length_singleton] using h
    have represented : ValuesAt exec.slots.val raw.base.val ((f.locals ++ front) ++ op.operands a b) := by
      simpa only [FrameSlots, split, List.append_assoc] using slots
    obtain ⟨out,returned,effect⟩ := WP.spec_imp_exists (step_integer_values memory hooks floats allocator exec store platform index raw inst compiled
      op left right (f.locals ++ front) a b last hf hi hc fetched pcBound represented leftPosition rightPos)
    rw [returned]
    simp only [WP.spec_ok]
    have prefixEffect := step_prefix memory hooks floats allocator exec store platform index raw inst compiled
      (Compiler.integerInstruction op left left right) last hf hi hc fetched (.numeric op left left right) out returned
    obtain ⟨sameStore, samePlatform, pc, pcEq, effect⟩ := effect
    refine ⟨sameStore, samePlatform, ?_⟩
    cases operation : op.apply a b with
    | none =>
      simp only [NumericValuesEffect, operation] at effect
      obtain ⟨trap, kind, exactEffect⟩ := effect
      have sourceTrap : SourceMachine.astep ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩ = .trap := by
        have h := astep_operands ⟨s, ambient, [], []⟩ f rest after front op a b
        simp only [finish, operation] at h
        simpa only [← split] using h
      refine .inr ⟨trap, congrArg Prod.fst exactEffect, kind, ?_⟩
      exact astep_trap_simulation s ambient f rest after op typed.typed sourceTrap
    | some value =>
      simp only [NumericValuesEffect, operation] at effect
      obtain ⟨success, represented, unchanged⟩ := effect
      have sourceStep : SourceMachine.astep ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩ = .next
          ⟨s, ambient, { f with code := after, vals := front ++ [SourceMachine.integerVal op.output value.toNat] } :: rest, []⟩ := by
        have h := astep_operands ⟨s, ambient, [], []⟩ f rest after front op a b
        simp only [finish, operation, SourceMachine.advance] at h
        simpa only [← split] using h
      have nextTyped := SourceMachine.instruction_preservation s ambient f rest _ after _ (.numeric op) typed.typed sourceStep
      have nextPoint : FramePoint s { raw with pc := pc }
          { f with code := after, vals := front ++ [SourceMachine.integerVal op.output value.toNat] }
          compiled C targets next output := by
        apply linear_continuation point pc f.locals
          (front ++ [SourceMachine.integerVal op.output value.toNat]) after middle
        · simpa only [endpoint, pcEq] using continuation
        · rfl
        · simp only [middleEq, List.map_append, List.map_cons, List.map_nil, integer_value_type, frontTypes]
        · have labels : LabelsMatch (front ++ op.operands a b) f.labels targets := by
            simpa only [← split] using point.labels
          exact labels.replace_suffix heights
      refine .inl ⟨success, pc, { f with code := after, vals := front ++ [SourceMachine.integerVal op.output value.toNat] },
        unchanged, ?_, nextPoint, ⟨nextTyped,typed.contents⟩, ⟨rfl,rfl,rfl,rfl⟩,
        .tail _ _ _ _ _ (frame_references_numeric f front _ _ _ split), ?_,prefixEffect,Or.inr ?_⟩
      · simpa only [FrameSlots, List.append_assoc] using represented
      · apply ConcreteSim.of_source
        exact astep_simulation s ambient f rest after op _ typed.typed sourceStep
      · change SourceMachine.Core.instruction s ambient {f with code := op.source :: after} rest op.source after = _
        rw [SourceMachine.Core.instruction_slice s ambient {f with code := op.source :: after} rest op.source after (.numeric op) frameTyped]
        exact sourceStep

end Itasca.Runtime.Interp.Machine

end

/-! ## Numeric Fetch -/

section

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std SourceMachine.Numeric
theorem numeric_fetched {raw compiled C targets next output s} {f : SourceMachine.AFrame}
    (op : Instruction) (after : List instr)
    (point : FramePoint s raw {f with code := op.source :: after} compiled C targets next output) :
    ∃ instruction, compiled.code.val[raw.pc.val]? = some instruction := by
  have linear : linearSource op.source = true := by cases op <;> (try casesm* Conversion) <;> rfl
  rcases structured_code_linear_inv linear point.code.current with ⟨target,forward,fetch,tail⟩ | ⟨middle,emitted,tail,head,fragment,rest⟩
  · exact ⟨_,fetch⟩
  · obtain ⟨stack,left,right,shape,emittedEq,middleEq,leftPos,rightPos⟩ := linear_emission_numeric_inv op (emission_numeric_pure op head)
    refine ⟨Compiler.integerInstruction op left left right,?_⟩
    simpa only [Nat.add_zero] using fragment.fetch (index := 0) (by simp only [emittedEq,List.getElem?_cons_zero])

end Itasca.Runtime.Interp.Machine

end

/-! ## Numeric Execution Owned -/

section

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std SourceMachine.Numeric

theorem step_numeric_execution_owned_uniform {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context)
    (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (op : Instruction) (after : List instr)
    (last : index.val+1 = exec.frames.length) (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := op.source :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec ⟨Store.decodeStore view code store,ambient,{f with code := op.source :: after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : SourceMachine.AState := ⟨Store.decodeStore view code store,ambient,{f with code := op.source :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ((out.1 = .Ok () ∧ ∃ pc : U32, ∃ g : SourceMachine.AFrame,
        Execution view code store out.2.1 ⟨initial.store,ambient,g::rest,[]⟩ expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial ⟨initial.store,ambient,g::rest,[]⟩ ∧
        UniformConcreteSim raw.pc.val pc.val false false initial ⟨initial.store,ambient,g::rest,[]⟩ [] ∧
        (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds initial → SourceMachine.Ownership.StatefulOwned bounds ⟨initial.store,ambient,g::rest,[]⟩) ∧
        (∀ bound, SourceMachine.CodeBound bound initial → SourceMachine.CodeBound bound ⟨initial.store,ambient,g::rest,[]⟩)) ∨
      (∃ trap, out.1 = .Err (.Trap trap) ∧ (trap = .IntegerDivideByZero ∨ trap = .IntegerOverflow) ∧
        ∃ count, 0 < count ∧ Spec.StepsHN count (SourceMachine.decode initial) [] ⟨⟨initial.store,ambient⟩,[.TRAP]⟩)) ⦄ := by
  dsimp only
  obtain ⟨instruction,fetched⟩ := numeric_fetched op after point
  have pcBound := program.fetched_bound instruction fetched
  apply WP.spec_mono (step_numeric memory hooks floats allocator exec store platform index raw inst compiled C targets
    next output (Store.decodeStore view code store) ambient f rest op after last hf hi hc pcBound machine.typed slots point)
  intro out effect
  refine ⟨effect.1,effect.2.1,?_⟩
  rcases effect.2.2 with success | trapped
  · obtain ⟨status,pc,g,unchanged,represented,continuation,fresh,metadata,closure,simulation,prefixEffect,sourceStep⟩ := success
    have uniform : UniformConcreteSim raw.pc.val pc.val false false
        ⟨Store.decodeStore view code store,ambient,{f with code := op.source::after}::rest,[]⟩
        ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ [] := by
      rcases sourceStep with same | step
      · subst g
        exact simulation.uniform_same (by scalar_tac)
      · exact UniformConcreteSim.single (SourceMachine.Numeric.core_step_positive _ _ _ _ _ _ _ machine.typed.typed step)
    have covered : SourceMachine.SupportedState ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
      rcases sourceStep with same | step
      · simpa only [same] using machine.core
      · exact Machine.core_step_supported machine.typed machine.core step
    have ownership : ∀ bounds, SourceMachine.Ownership.StatefulOwned bounds ⟨Store.decodeStore view code store,ambient,{f with code := op.source :: after}::rest,[]⟩ →
        SourceMachine.Ownership.StatefulOwned bounds ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
      intro bounds bounded
      rcases sourceStep with same | step
      · simpa only [same] using bounded
      · exact Machine.core_step_owned machine.typed machine.core step bounds bounded
    refine Or.inl ⟨status,pc,g,?_,simulation,uniform,ownership,Machine.bound_transition machine.typed machine.core (sourceStep.imp_left (fun same => by rw [same]))⟩
    exact machine.ordinary view code ambient {f with code := op.source :: after} g rest expected raw.pc.val false
      (.refl store) (Spec.extend_store_refl _ machine.typed.typed.store) raw index pc last hf program (.ready continuation)
      represented ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩ unchanged prefixEffect fresh covered
  · exact Or.inr trapped
theorem step_numeric_execution_owned {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context)
    (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (op : Instruction) (after : List instr)
    (last : index.val+1 = exec.frames.length) (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := op.source :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec ⟨Store.decodeStore view code store,ambient,{f with code := op.source :: after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : SourceMachine.AState := ⟨Store.decodeStore view code store,ambient,{f with code := op.source :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ((out.1 = .Ok () ∧ ∃ pc : U32, ∃ g : SourceMachine.AFrame,
        Execution view code store out.2.1 ⟨initial.store,ambient,g::rest,[]⟩ expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial ⟨initial.store,ambient,g::rest,[]⟩ ∧
        (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds initial → SourceMachine.Ownership.StatefulOwned bounds ⟨initial.store,ambient,g::rest,[]⟩) ∧
        (∀ bound, SourceMachine.CodeBound bound initial → SourceMachine.CodeBound bound ⟨initial.store,ambient,g::rest,[]⟩)) ∨
      (∃ trap, out.1 = .Err (.Trap trap) ∧ (trap = .IntegerDivideByZero ∨ trap = .IntegerOverflow) ∧
        ∃ count, 0 < count ∧ Spec.StepsHN count (SourceMachine.decode initial) [] ⟨⟨initial.store,ambient⟩,[.TRAP]⟩)) ⦄ := by
  apply WP.spec_mono (step_numeric_execution_owned_uniform memory hooks floats allocator view code exec store platform index raw inst compiled C targets next output ambient f rest op after last hf hi hc program slots point expected machine)
  rintro out ⟨same,platform,success | trapped⟩
  · rcases success with ⟨success,pc,g,machine,simulation,uniform,ownership,bounded⟩
    exact ⟨same,platform,Or.inl ⟨success,pc,g,machine,simulation,ownership,bounded⟩⟩
  · exact ⟨same,platform,Or.inr trapped⟩

end Itasca.Runtime.Interp.Machine

end

/-! ## Numeric No Trap -/

section

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std SourceMachine.Numeric

theorem step_numeric_no_trap {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (s : _root_.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (op : Instruction) (after : List instr)
    (total : ∀ a b, op.apply a b ≠ none)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (typed : SourceMachine.CoreTyped ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (point : FramePoint s raw { f with code := op.source :: after }
      compiled C targets next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out => out.1 = .Ok () ⦄ := by
  have linear : linearSource op.source = true := by
    cases op <;> (try casesm* Conversion) <;> rfl
  rcases structured_code_linear_inv linear point.code.current with skip | branch
  · obtain ⟨target, forward, fetched, continuation⟩ := skip
    apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform
      index raw inst compiled target last hf hi hc pcBound fetched)
    intro out effect
    obtain ⟨success, exactState, sameStore, samePlatform⟩ := effect
    exact success
  · obtain ⟨middle, emitted, tail, head, fragment, continuation⟩ := branch
    obtain ⟨stack, left, right, shape, emittedEq, middleEq, leftPos, rightPos⟩ := linear_emission_numeric_inv op (emission_numeric_pure op head)
    have frameTyped : SourceMachine.FrameTyped s { f with code := op.source :: after } [] := by
      cases typed.typed.frames with | cons h _ => exact h
    obtain ⟨front, a, b, split, wfFront, heights⟩ := op.typed_operands_bounds frameTyped
    have frontTypes : front.map Compiler.valueType = stack := by
      rw [split, List.map_append, numeric_operand_types] at shape
      exact List.append_cancel_right shape
    have leftPosition : left.val = Compiler.slots ((f.locals ++ front).map Compiler.valueType) := by
      simpa only [point.locals,List.map_append, Compiler.slots_append, frontTypes] using leftPos
    have fetched : compiled.code.val[raw.pc.val]? = some (Compiler.integerInstruction op left left right) := by
      simpa only [Nat.add_zero] using fragment.fetch (index := 0) (by simp only [emittedEq, List.getElem?_cons_zero])
    have endpoint : tail = raw.pc.val + 1 := by
      obtain ⟨_, _, _, _, h⟩ := fragment
      simpa only [emittedEq, List.length_singleton] using h
    have represented : ValuesAt exec.slots.val raw.base.val ((f.locals ++ front) ++ op.operands a b) := by
      simpa only [FrameSlots, split, List.append_assoc] using slots
    obtain ⟨out,returned,effect⟩ := WP.spec_imp_exists (step_integer_values memory hooks floats allocator exec store platform index raw inst compiled
      op left right (f.locals ++ front) a b last hf hi hc fetched pcBound represented leftPosition rightPos)
    rw [returned]
    simp only [WP.spec_ok]
    obtain ⟨sameStore,samePlatform,pc,pcEq,effect⟩ := effect
    cases operation : op.apply a b with
    | none => exact False.elim (total a b operation)
    | some value =>
      simp only [NumericValuesEffect,operation] at effect
      exact effect.1
end Itasca.Runtime.Interp.Machine

end

end

/-! ## Select -/

section

/-!
Untyped select machine fetch, step and ownership. The resulting argument is consumed by complete machine advance while preserving its source grammar and store premises.
-/

/-! ## Select Point -/

section

namespace Itasca.Runtime.Interp.Machine.Select
variable {jumpTables : List Aeneas.Std.U32}
variable {family : ContextEmission} [FloatHeads family]
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp
theorem core_point_select_head {C returns code labels stack pc next output} (after : List instr)
    (point : Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
      (.SELECT none :: after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
        (.SELECT none :: after) target.val next output) ∨
    (∃ front ty left right condition, stack = front ++ [ty,ty,.I32] ∧
      left.val = Compiler.slots C.LOCALS+Compiler.slots front ∧ right.val = left.val+Compiler.width ty ∧
      condition.val = right.val+Compiler.width ty ∧
      code[pc]? = some (Compiler.selectInstruction (decide (Compiler.width ty = 2)) left right condition) ∧
      Compiler.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels
        (front ++ [ty]) after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : instr.SELECT none :: after = source at relation
  cases relation with
  | linear head ordinary fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    obtain ⟨front,ty,left,right,condition,input,emitted,result,leftPos,rightPos,conditionPos⟩ := scalar_emission_select_inv (FloatHeads.project (.core .select) head)
    subst_vars
    have fetch := fragment.fetch (index := 0) (by rfl)
    obtain ⟨_,_,_,_,nextEq⟩ := fragment
    refine Or.inr ⟨front,ty,left,right,condition,rfl,leftPos,rightPos,conditionPos,by simpa using fetch,?_⟩
    exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
  | skip forward instruction rest =>
    subst_vars
    exact Or.inl ⟨_,forward,instruction,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | _ => simp at sourceEq

end Itasca.Runtime.Interp.Machine.Select

end

/-! ## Select Step -/

section

namespace Itasca.Runtime.Interp.Machine.Select
open Aeneas Aeneas.Std SpecExt

theorem step_select_core {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Compiler.LabelTarget)
    (next : Nat) (output : List valtype) (sourceStore : _root_.store) (ambient : frame)
    (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (last : index.val+1 = exec.frames.length) (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max) (slots : FrameSlots exec raw f)
    (point : FramePoint sourceStore raw {f with code := .SELECT none::after} compiled C targets next output)
    (typed : SourceMachine.CoreTyped ⟨sourceStore,ambient,{f with code := .SELECT none::after}::rest,[]⟩) :
    let initial : SourceMachine.AState := ⟨sourceStore,ambient,{f with code := .SELECT none::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : SourceMachine.AFrame),
        {out.2.1 with slots := exec.slots} = {exec with frames := exec.frames.set index {raw with pc := pc}} ∧
        FrameSlots out.2.1 {raw with pc := pc} g ∧
        FramePoint sourceStore {raw with pc := pc} g compiled C targets next output ∧
        SourceMachine.CoreTyped {initial with frames := g::rest} ∧ FrameMetadata f g ∧
        (initial = {initial with frames := g::rest} ∨ SourceMachine.Core.step initial = .next {initial with frames := g::rest}) ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial {initial with frames := g::rest} ∧
        SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ⦄ := by
  dsimp only
  rcases core_point_select_head after point.code with ⟨target,forward,fetched,tail⟩ | ⟨types,ty,a,b,condition,input,leftPos,rightPos,conditionPos,fetched,tail⟩
  · have retained : FramePoint sourceStore {raw with pc := target} {f with code := .SELECT none::after} compiled C targets next output :=
      ⟨point.bindings,point.locals,point.labels,tail⟩
    apply WP.spec_mono (step_forward_jump_flat memory hooks floats allocator exec store platform index raw inst compiled
      sourceStore ambient {f with code := .SELECT none::after} rest C targets next output target
      last frameFound instanceFound codeFound pcBound forward fetched slots retained typed)
    intro out effect
    obtain ⟨success,sameStore,samePlatform,exactState,represented,retained,fresh,simulation⟩ := effect
    refine ⟨success,sameStore,samePlatform,target,_,?_,represented,retained,fresh,⟨rfl,rfl,rfl,rfl⟩,Or.inl rfl,simulation,?_⟩
    · rw [exactState]
    · rw [exactState]; exact .refl _ _
  · have frameTyped : SourceMachine.FrameTyped sourceStore {f with code := .SELECT none::after} [] := by
      cases typed.typed.frames with | cons head _ => exact head
    obtain ⟨front,left,right,bits,valueTy,split,bitsBound,leftType,rightType,heights⟩ := select_typed_operands frameTyped
    have conditionType : Compiler.valueType (SourceMachine.integerVal .I32 bits) = .I32 := rfl
    have stackEq : front.map Compiler.valueType ++ [valueTy,valueTy,.I32] = types ++ [ty,ty,.I32] := by
      simpa only [split,List.map_append,List.map_cons,List.map_nil,leftType,rightType,conditionType] using input
    have lengthEq : (front.map Compiler.valueType).length = types.length := by
      have lengths := congrArg List.length stackEq
      simp only [List.length_append,List.length_cons,List.length_nil] at lengths
      omega
    obtain ⟨frontEq,typeEq⟩ := List.append_inj stackEq lengthEq
    have sameTy : valueTy = ty := (List.cons.inj typeEq).1
    have leftType' : Compiler.valueType left = ty := leftType.trans sameTy
    have rightType' : Compiler.valueType right = ty := rightType.trans sameTy
    have position : a.val = Compiler.slots ((f.locals++front).map Compiler.valueType) := by
      simpa only [List.map_append,Compiler.slots_append,point.locals,← frontEq] using leftPos
    have actual := select_source_next (s := sourceStore) (ambient := ambient) (rest := rest) (after := after) split (leftType.trans rightType.symm) bitsBound
    obtain ⟨nextState,nextEq,fresh,source⟩ := SourceMachine.Core.select_progress sourceStore ambient f rest after typed
    have nextEq' : SourceMachine.Core.step ⟨sourceStore,ambient,{f with code := .SELECT none::after}::rest,[]⟩ = .next nextState := nextEq
    have sameState := SourceMachine.AResult.next.inj (actual.symm.trans nextEq')
    subst nextState
    apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
      (Compiler.selectInstruction (decide (Compiler.width ty = 2)) a b condition) last frameFound instanceFound codeFound fetched pcBound
    intro pc pcNext
    have continuation : FramePoint sourceStore {raw with pc := pc}
        {f with code := after,vals := front++[if bits = 0 then right else left]} compiled C targets next output := by
      refine ⟨point.bindings,point.locals,?_,?_⟩
      · have labels : LabelsMatch (front++[left,right,SourceMachine.integerVal .I32 bits]) f.labels targets := by simpa only [split] using point.labels
        exact labels.replace_suffix heights
      · have selectedType : Compiler.valueType (if bits = 0 then right else left) = ty := by split <;> first | exact rightType' | exact leftType'
        simpa only [List.map_append,List.map_cons,List.map_nil,selectedType,frontEq,pcNext] using tail
    have represented : ValuesAt exec.slots.val raw.base.val ((f.locals++front)++[left,right,SourceMachine.integerVal .I32 bits]) := by
      simpa only [FrameSlots,split,List.append_assoc] using slots
    apply WP.spec_mono (select_slots memory hooks floats allocator
      {exec with frames := exec.frames.set index {raw with pc := pc}} store platform index raw (f.locals++front) left right bits a b condition ty
      represented leftType' rightType' position rightPos conditionPos bitsBound)
    intro out effect
    obtain ⟨success,sameStore,samePlatform,represented,fields,preserved⟩ := effect
    refine ⟨success,sameStore,samePlatform,pc,_,fields,?_,continuation,fresh,⟨rfl,rfl,rfl,rfl⟩,Or.inr actual,?_,preserved⟩
    · simpa only [FrameSlots,List.append_assoc] using represented
    · exact Or.inr ⟨1,by omega,by simpa using Itasca.Runtime.Spec.StepsHN.cons source (Itasca.Runtime.Spec.StepsHN.refl (Itasca.Runtime.Spec.step_h_wf source).2)⟩
end Itasca.Runtime.Interp.Machine.Select

end

/-! ## Select Execution Owned -/

section

namespace Itasca.Runtime.Interp.Machine.Select
open Aeneas Aeneas.Std
theorem step_select_core_execution_owned_uniform {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Compiler.LabelTarget)
    (next : Nat) (output : List valtype) (view : M → Slice U8) (code : Store.CodeInterpretation) (ambient : frame)
    (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (last : index.val+1 = exec.frames.length) (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := .SELECT none::after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := .SELECT none::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS) :
    let initial : SourceMachine.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .SELECT none::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : SourceMachine.AFrame),
        Execution view code store out.2.1 {initial with frames := g::rest} expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial {initial with frames := g::rest} ∧
        UniformConcreteSim raw.pc.val pc.val false false initial {initial with frames := g::rest} [] ∧
        (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds initial → SourceMachine.Ownership.StatefulOwned bounds {initial with frames := g::rest}) ∧
        (∀ bound, SourceMachine.CodeBound bound initial → SourceMachine.CodeBound bound {initial with frames := g::rest}) ⦄ := by
  dsimp only
  have pcBound : raw.pc.val < U32.max := by
    rcases core_point_select_head after point.code with ⟨target,forward,fetched,tail⟩ | ⟨types,ty,a,b,condition,input,leftPos,rightPos,conditionPos,fetched,tail⟩
    · have bound := (List.getElem?_eq_some_iff.mp fetched).1
      have limit := program.fetchBound
      omega
    · have bound := (List.getElem?_eq_some_iff.mp fetched).1
      have limit := program.fetchBound
      omega
  apply WP.spec_mono (step_select_core memory hooks floats allocator exec store platform index raw inst compiled C targets next output
    (Store.decodeStore view code store) ambient f rest after last frameFound instanceFound codeFound pcBound slots point machine.typed)
  intro out effect
  obtain ⟨success,sameStore,samePlatform,pc,g,fields,represented,retained,fresh,metadata,transition,simulation,preserved⟩ := effect
  have uniform : UniformConcreteSim raw.pc.val pc.val false false
      ⟨Store.decodeStore view code store,ambient,{f with code := .SELECT none::after}::rest,[]⟩
      ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ [] := by
    rcases transition with same | step
    · rw [← same] at simulation ⊢
      exact simulation.uniform_same (by scalar_tac)
    · exact UniformConcreteSim.single (SourceMachine.Core.select_step_positive _ _ _ _ _ _ machine.typed step)
  have covered : SourceMachine.SupportedState ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
    rcases transition with same | step
    · rw [← same]; exact machine.core
    · exact Machine.core_step_supported machine.typed machine.core step
  exact ⟨success,sameStore,samePlatform,pc,g,
    Execution.ordinary view code ambient {f with code := .SELECT none::after} g rest expected raw.pc.val false machine
      (.refl store) (Itasca.Runtime.Spec.extend_store_refl _ machine.typed.typed.store) raw index pc last frameFound program
      (.ready retained) represented ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩ fields preserved fresh covered,simulation,uniform,Machine.owned_transition machine.typed machine.core transition,Machine.bound_transition machine.typed machine.core transition⟩
theorem step_select_core_execution_owned {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Compiler.LabelTarget)
    (next : Nat) (output : List valtype) (view : M → Slice U8) (code : Store.CodeInterpretation) (ambient : frame)
    (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (last : index.val+1 = exec.frames.length) (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := .SELECT none::after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := .SELECT none::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS) :
    let initial : SourceMachine.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .SELECT none::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : SourceMachine.AFrame),
        Execution view code store out.2.1 {initial with frames := g::rest} expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial {initial with frames := g::rest} ∧
        (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds initial → SourceMachine.Ownership.StatefulOwned bounds {initial with frames := g::rest}) ∧
        (∀ bound, SourceMachine.CodeBound bound initial → SourceMachine.CodeBound bound {initial with frames := g::rest}) ⦄ := by
  apply WP.spec_mono (step_select_core_execution_owned_uniform memory hooks floats allocator exec store platform index raw inst compiled C targets next output view code ambient f rest after last frameFound instanceFound codeFound slots point expected machine program)
  rintro out ⟨success,same,platform,pc,g,machine,simulation,uniform,ownership,bounded⟩
  exact ⟨success,same,platform,pc,g,machine,simulation,ownership,bounded⟩

end Itasca.Runtime.Interp.Machine.Select

end

end
