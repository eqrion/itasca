import Itasca.Runtime.Interp.Machine.Coverage.OrdinaryHeads
import Itasca.Runtime.Compiler.Local.Lowering.Float.FloatEmissionInversion
import Itasca.Runtime.Interp.State.GlobalCoreEmission
import Itasca.Runtime.Interp.State.GlobalCoreOperands
import Itasca.Runtime.SourceMachine.Core.Step
import Itasca.Runtime.SourceMachine.Core
import Itasca.Runtime.SourceMachine.Float.Descriptor
import Itasca.Runtime.SourceMachine.Numeric.Transition
import Itasca.Runtime.SourceMachine.StepSafety
import Itasca.Runtime.SourceMachine.Supported.CoreStuck
import Itasca.Runtime.SourceMachine.Core.Pure
import Itasca.Runtime.SourceMachine.Ownership.Core
import Itasca.Runtime.SourceMachine.Core.Bound
import Itasca.Runtime.Interp.State.GlobalCoreStep
import Itasca.Runtime.Interp.Relations.Capacity
import Itasca.Runtime.Compiler.Local.Capacity.GlobalCapacity

/-!
Global reads and writes from structured fetch inversion through preparation and certified step. Whole-execution ownership remains separate: mutation proofs need the certified step without its 150 additional execution dependencies.
-/

/-! ## Global Point -/

section

namespace Itasca.Runtime.Interp.StructuredMachine.Global
variable {jumpTables : List Aeneas.Std.U32}
variable {family : ContextEmission} [FloatHeads family]
open Aeneas Aeneas.Std

theorem corePoint_globalGet_head {C returns code labels stack pc next output}
    (index : Nat) (after : List instr)
    (point : Code.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
      (.GLOBAL_GET (.mk_uN index) :: after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
        (.GLOBAL_GET (.mk_uN index) :: after) target.val next output) ∨
    (∃ mutability ty idx dst, index = idx.val ∧
      C.GLOBALS[index]? = some (.mk_globaltype mutability ty) ∧
      dst.val = Code.slots C.LOCALS + Code.slots stack ∧
      code[pc]? = some (Code.globalGetInstruction (decide (Code.width ty = 2)) dst idx) ∧
      Code.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels
        (stack ++ [ty]) after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : instr.GLOBAL_GET (.mk_uN index) :: after = source at relation
  cases relation with
  | linear head ordinary fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    obtain ⟨mutability,ty,idx,dst,indexEq,lookup,emitted,result,position⟩ := scalarEmission_globalGet_inv index (FloatHeads.project (.core (.global_get (.mk_uN index))) head)
    subst_vars
    have fetch := fragment.fetch (index := 0) (by rfl)
    obtain ⟨_,_,_,_,nextEq⟩ := fragment
    refine Or.inr ⟨mutability,ty,idx,dst,rfl,lookup,position,by simpa using fetch,?_⟩
    exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
  | skip forward instruction rest =>
    subst_vars
    exact Or.inl ⟨_,forward,instruction,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | _ => cases sourceEq

theorem corePoint_globalSet_head {C returns code labels stack pc next output}
    (index : Nat) (after : List instr)
    (point : Code.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
      (.GLOBAL_SET (.mk_uN index) :: after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
        (.GLOBAL_SET (.mk_uN index) :: after) target.val next output) ∨
    (∃ front ty idx src, index = idx.val ∧ stack = front ++ [ty] ∧
      C.GLOBALS[index]? = some (.mk_globaltype (some .MUT) ty) ∧
      src.val = Code.slots C.LOCALS + Code.slots front ∧
      code[pc]? = some (Code.globalSetInstruction (decide (Code.width ty = 2)) src idx) ∧
      Code.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels
        front after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : instr.GLOBAL_SET (.mk_uN index) :: after = source at relation
  cases relation with
  | linear head ordinary fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    obtain ⟨front,ty,idx,src,indexEq,input,lookup,emitted,result,position⟩ := scalarEmission_globalSet_inv index (FloatHeads.project (.core (.global_set (.mk_uN index))) head)
    subst_vars
    have fetch := fragment.fetch (index := 0) (by rfl)
    obtain ⟨_,_,_,_,nextEq⟩ := fragment
    refine Or.inr ⟨front,ty,idx,src,rfl,rfl,lookup,position,by simpa using fetch,?_⟩
    exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
  | skip forward instruction rest =>
    subst_vars
    exact Or.inl ⟨_,forward,instruction,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | _ => cases sourceEq
end Itasca.Runtime.Interp.StructuredMachine.Global

end

/-! ## Global Prepare -/

section

namespace Itasca.Runtime.Interp.StructuredMachine.Global
open Aeneas Aeneas.Std SpecExt

theorem coreFramePoint_globalGet_prepare {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (raw : runtime.interp.Frame)
    (f : Abs.AFrame) (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Code.LabelTarget)
    (next : Nat) (output : List valtype) (after : List instr) (index : Nat)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := .GLOBAL_GET (.mk_uN index) :: after} compiled C targets next output) :
    (∃ target : U32, raw.pc.val < target.val ∧ compiled.code.val[raw.pc.val]? = some (.Jump target) ∧
      FramePoint (Store.decodeStore view code store) {raw with pc := target} {f with code := .GLOBAL_GET (.mk_uN index) :: after} compiled C targets next output) ∨
    (∃ idx dst address object, index = idx.val ∧
      inst.globals.val[index]? = some address ∧ store.globals.val[address.index.val]? = some object ∧
      dst.val = Code.slots ((f.locals ++ f.vals).map Code.valueType) ∧
      compiled.code.val[raw.pc.val]? = some (Code.globalGetInstruction (decide (Code.width (sourceType object.ty.valtype) = 2)) dst idx) ∧
      Code.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS compiled.code.val compiled.jump_tables.val targets
        (f.vals.map Code.valueType ++ [sourceType object.ty.valtype]) after (raw.pc.val+1) next output) := by
  rcases corePoint_globalGet_head index after point.code with ⟨target,forward,fetch,tail⟩ | ⟨mutability,ty,idx,dst,indexEq,lookup,position,fetch,tail⟩
  · exact Or.inl ⟨target,forward,fetch,⟨point.bindings,point.locals,point.labels,tail⟩⟩
  · obtain ⟨address,object,mapped,issued,mutEq,typeEq⟩ := coreGlobal_lookup view code store inst f C index mutability ty moduleEq point.bindings lookup
    refine Or.inr ⟨idx,dst,address,object,indexEq,mapped,issued,?_,?_,?_⟩
    · simpa only [point.locals,List.map_append,Code.slots_append] using position
    · simpa only [typeEq] using fetch
    · simpa only [typeEq] using tail

theorem coreFramePoint_globalSet_prepare {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (raw : runtime.interp.Frame)
    (f : Abs.AFrame) (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Code.LabelTarget)
    (next : Nat) (output : List valtype) (after : List instr) (index : Nat)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (typed : Abs.FrameTyped (Store.decodeStore view code store) {f with code := .GLOBAL_SET (.mk_uN index) :: after} [])
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := .GLOBAL_SET (.mk_uN index) :: after} compiled C targets next output) :
    (∃ target : U32, raw.pc.val < target.val ∧ compiled.code.val[raw.pc.val]? = some (.Jump target) ∧
      FramePoint (Store.decodeStore view code store) {raw with pc := target} {f with code := .GLOBAL_SET (.mk_uN index) :: after} compiled C targets next output) ∨
    (∃ front value idx src address object, index = idx.val ∧ f.vals = front ++ [value] ∧ wf_val value ∧
      (∀ label ∈ f.labels, label.height ≤ front.length) ∧
      inst.globals.val[index]? = some address ∧ store.globals.val[address.index.val]? = some object ∧
      object.ty.mutability = .Var ∧ sourceType object.ty.valtype = Code.valueType value ∧
      src.val = Code.slots ((f.locals ++ front).map Code.valueType) ∧
      compiled.code.val[raw.pc.val]? = some (Code.globalSetInstruction (decide (Code.width (sourceType object.ty.valtype) = 2)) src idx) ∧
      Code.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS compiled.code.val compiled.jump_tables.val targets
        (front.map Code.valueType) after (raw.pc.val+1) next output) := by
  rcases corePoint_globalSet_head index after point.code with ⟨target,forward,fetch,tail⟩ | ⟨types,ty,idx,src,indexEq,input,lookup,position,fetch,tail⟩
  · exact Or.inl ⟨target,forward,fetch,⟨point.bindings,point.locals,point.labels,tail⟩⟩
  · obtain ⟨address,object,mapped,issued,mutEq,typeEq⟩ := coreGlobal_lookup view code store inst f C index (some .MUT) ty moduleEq point.bindings lookup
    obtain ⟨front,value,values,valueWf,heights⟩ := global_set_typed_operand f after index typed
    have shape := input
    simp only [values,List.map_append,List.map_cons,List.map_nil] at shape
    have lengthEq : (front.map Code.valueType).length = types.length := by
      have lengths := congrArg List.length shape
      simp only [List.length_append,List.length_cons,List.length_nil] at lengths
      omega
    obtain ⟨typesEq,valueEq⟩ := List.append_inj shape lengthEq
    have valueType : Code.valueType value = ty := by simpa using valueEq
    have mutable : object.ty.mutability = .Var := by
      cases eq : object.ty.mutability <;> simp_all [Store.decodeMut]
    refine Or.inr ⟨front,value,idx,src,address,object,indexEq,values,valueWf,heights,mapped,issued,mutable,typeEq.trans valueType.symm,?_,?_,?_⟩
    · simpa only [point.locals,List.map_append,Code.slots_append,typesEq] using position
    · simpa only [typeEq] using fetch
    · simpa only [typesEq] using tail
end Itasca.Runtime.Interp.StructuredMachine.Global

end

/-! ## Global Continue -/

section

namespace Itasca.Runtime.Interp.StructuredMachine.Global
open Aeneas Aeneas.Std SpecExt

theorem decode_words_valueType (ty : Itasca.types.ValueType) (lo hi : U64) :
    Code.valueType (Store.decodeWords ty lo hi) = sourceType ty := by
  cases ty <;> simp only [Store.decodeWords,Store.decodeRef,Store.decodeElemType,sourceType]
  all_goals first | rfl | (split <;> rfl)

theorem corePoint_globalGet_continue {sourceStore raw f compiled C targets next output}
    (point : FramePoint sourceStore raw f compiled C targets next output)
    (value : val) (ty : valtype) (after : List instr)
    (heights : ∀ label ∈ f.labels, label.height ≤ f.vals.length)
    (valueType : Code.valueType value = ty)
    (tail : Code.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val compiled.jump_tables.val targets (f.vals.map Code.valueType ++ [ty]) after (raw.pc.val+1) next output)
    (pc : U32) (pcNext : pc.val = raw.pc.val+1) :
    FramePoint sourceStore {raw with pc := pc} {f with code := after,vals := f.vals ++ [value]}
      compiled C targets next output := by
  refine ⟨point.bindings,point.locals,?_,?_⟩
  · have labels : LabelsMatch (f.vals ++ []) f.labels targets := by simpa only [List.append_nil] using point.labels
    exact labels.replace_suffix heights
  · simpa only [List.map_append,List.map_cons,List.map_nil,valueType,pcNext] using tail

theorem corePoint_globalSet_continue {before afterStore raw f compiled C targets next output}
    (point : FramePoint before raw f compiled C targets next output)
    (extension : Extend_store before afterStore)
    (front : List val) (value : val) (after : List instr)
    (values : f.vals = front ++ [value])
    (heights : ∀ label ∈ f.labels, label.height ≤ front.length)
    (tail : Code.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val compiled.jump_tables.val targets (front.map Code.valueType) after (raw.pc.val+1) next output)
    (pc : U32) (pcNext : pc.val = raw.pc.val+1) :
    FramePoint afterStore {raw with pc := pc} {f with code := after,vals := front}
      compiled C targets next output := by
  refine ⟨point.bindings.extend extension,point.locals,?_,?_⟩
  · have labels := point.labels
    rw [values] at labels
    simpa only [List.append_nil] using labels.replace_suffix (after := []) heights
  · simpa only [pcNext] using tail
end Itasca.Runtime.Interp.StructuredMachine.Global

end

/-! ## Global Certified Step Owned -/

section

namespace Itasca.Runtime.Interp.StructuredMachine.Global
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Spec
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem coreFramePoint_globalGet_step_owned (platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (index : Nat)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
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
    (typed : Abs.CoreTyped ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_GET (.mk_uN index) :: after} :: rest,[]⟩) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_GET (.mk_uN index) :: after} :: rest,[]⟩
    (∃ target : U32, raw.pc.val < target.val ∧ compiled.code.val[raw.pc.val]? = some (.Jump target) ∧
      FramePoint (Store.decodeStore view code store) {raw with pc := target} {f with code := .GLOBAL_GET (.mk_uN index) :: after} compiled C targets next output) ∨
    (runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ nextFrame pc, pc.val = raw.pc.val+1 ∧
        {out.2.1 with slots := exec.slots} = {exec with frames := exec.frames.set frameIndex {raw with pc := pc}} ∧
        Abs.CoreTyped {initial with frames := nextFrame :: rest} ∧
        StepH (Abs.decode initial) [] (Abs.decode {initial with frames := nextFrame :: rest}) ∧
        FrameSlots out.2.1 {raw with pc := pc} nextFrame ∧
        FramePoint (Store.decodeStore view code store) {raw with pc := pc} nextFrame compiled C targets next output ∧ (∃ values, nextFrame = {f with code := after,vals := values}) ∧ SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ∧
        Abs.Core.step initial = .next {initial with frames := nextFrame :: rest} ⦄) := by
  dsimp only
  have frameTyped : Abs.FrameTyped (Store.decodeStore view code store) {f with code := .GLOBAL_GET (.mk_uN index) :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  rcases coreFramePoint_globalGet_prepare view code store inst raw f compiled C targets next output after index moduleEq point with jump | operation
  · exact Or.inl jump
  · apply Or.inr
    obtain ⟨idx,dst,address,object,indexEq,mapped,issued,position,fetch,tail⟩ := operation
    subst index
    have valid := Code.well_formed_fetched compiled checked raw.pc.val _ fetch
    have bound := Code.global_get_valid_bounds compiled (sourceType object.ty.valtype) dst idx valid
    have allocated := binding.capacity inst compiled found codeFound
    have capacity : raw.base.val + dst.val + Code.width (sourceType object.ty.valtype) ≤ exec.slots.length := by omega
    apply WP.spec_mono (step_global_get_simulation memory hooks floats allocator view code exec store raw dst idx inst address object ambient f rest after platform frameIndex found mapped issued moduleEq slots position capacity
      (small object (List.mem_of_getElem? issued)) compiled last frameFound codeFound fetch pcBound typed)
    intro out effect
    obtain ⟨success,platformSame,storeSame,nextFrame,actual,fresh,source,represented,pc,pcNext,unchanged,prefixEffect⟩ := effect
    have coreStep : Abs.Core.step ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_GET (.mk_uN idx.val) :: after} :: rest,[]⟩ =
        .next ⟨Store.decodeStore view code store,ambient,nextFrame::rest,[]⟩ := by
      simpa only [Abs.Core.step,Abs.Core.instruction,Abs.Core.globalGet] using actual
    have exactStep := core_global_get_value view code store inst address object ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_GET (.mk_uN idx.val) :: after} :: rest,[]⟩ f rest after idx rfl moduleEq mapped issued
    rw [exactStep] at actual
    have frameEq := (List.cons.inj (congrArg Abs.AState.frames (Abs.AResult.next.inj actual))).1
    refine ⟨success,storeSame,platformSame,nextFrame,pc,pcNext,unchanged,fresh,source,represented,?_,?_,prefixEffect,coreStep⟩
    · rw [←frameEq]
      exact corePoint_globalGet_continue point _ _ after (Abs.frameTyped_heights frameTyped)
        (decode_words_valueType _ _ _) tail pc pcNext
    · exact ⟨_,frameEq.symm⟩

theorem coreFramePoint_globalSet_step_owned (platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (index : Nat)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := .GLOBAL_SET (.mk_uN index) :: after} compiled C targets next output)
    (typed : Abs.CoreTyped ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_SET (.mk_uN index) :: after} :: rest,[]⟩) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_SET (.mk_uN index) :: after} :: rest,[]⟩
    (∃ target : U32, raw.pc.val < target.val ∧ compiled.code.val[raw.pc.val]? = some (.Jump target) ∧
      FramePoint (Store.decodeStore view code store) {raw with pc := target} {f with code := .GLOBAL_SET (.mk_uN index) :: after} compiled C targets next output) ∨
    (runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.2 = platform ∧ FrameStoreMetadata store out.2.2.1 ∧
      ∃ nextFrame pc, pc.val = raw.pc.val+1 ∧
        out.2.1 = {exec with frames := exec.frames.set frameIndex {raw with pc := pc}} ∧
        Abs.CoreTyped {initial with store := Store.decodeStore view code out.2.2.1,frames := nextFrame :: rest} ∧
        Extend_store initial.store (Store.decodeStore view code out.2.2.1) ∧
        StepH (Abs.decode initial) [] (Abs.decode {initial with store := Store.decodeStore view code out.2.2.1,frames := nextFrame :: rest}) ∧
        FrameSlots out.2.1 {raw with pc := pc} nextFrame ∧
        FramePoint (Store.decodeStore view code out.2.2.1) {raw with pc := pc} nextFrame compiled C targets next output ∧ (∃ values, nextFrame = {f with code := after,vals := values}) ∧
        Abs.Core.step initial = .next {initial with store := Store.decodeStore view code out.2.2.1,frames := nextFrame :: rest} ⦄) := by
  dsimp only
  have frameTyped : Abs.FrameTyped (Store.decodeStore view code store) {f with code := .GLOBAL_SET (.mk_uN index) :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  rcases coreFramePoint_globalSet_prepare view code store inst raw f compiled C targets next output after index moduleEq frameTyped point with jump | operation
  · exact Or.inl jump
  · apply Or.inr
    obtain ⟨front,value,idx,src,address,object,indexEq,values,valueWf,heights,mapped,issued,mutable,valueType,position,fetch,tail⟩ := operation
    subst index
    apply WP.spec_mono (step_global_set_simulation memory hooks floats allocator view code exec store raw src idx inst address object ambient f rest after front value platform frameIndex found mapped issued moduleEq slots values position mutable valueWf valueType compiled last frameFound codeFound fetch pcBound typed)
    intro out effect
    obtain ⟨platformSame,success,⟨pc,pcNext,unchanged⟩,metadata,nextFrame,actual,fresh,extension,source,represented⟩ := effect
    have coreStep : Abs.Core.step ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_SET (.mk_uN idx.val) :: after} :: rest,[]⟩ =
        .next ⟨Store.decodeStore view code out.2.2.1,ambient,nextFrame::rest,[]⟩ := by
      simpa only [Abs.Core.step,Abs.Core.instruction,Abs.Core.globalSet,Abs.AFrame.toFrame] using actual
    have typeEq : Abs.valueType value = sourceType object.ty.valtype := by rw [←valueType_eq_abs]; exact valueType.symm
    have exactStep := core_global_set_value view code store inst address object ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_SET (.mk_uN idx.val) :: after} :: rest,[]⟩ f rest after idx front value rfl moduleEq mapped issued values mutable typeEq
    rw [exactStep] at actual
    have frameEq := (List.cons.inj (congrArg Abs.AState.frames (Abs.AResult.next.inj actual))).1
    refine ⟨success,platformSame,metadata,nextFrame,pc,pcNext,unchanged,fresh,extension,source,represented,?_,?_,coreStep⟩
    · rw [←frameEq]
      exact corePoint_globalSet_continue point extension front value after values heights tail pc pcNext
    · exact ⟨_,frameEq.symm⟩

end Itasca.Runtime.Interp.StructuredMachine.Global

end
