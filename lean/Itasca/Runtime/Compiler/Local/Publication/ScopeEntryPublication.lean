import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerTerminalMetadata
import Itasca.Runtime.Compiler.Local.Callbacks.CodeGrowth.CompilerCodeMonotoneLiteral
import Itasca.Runtime.Compiler.Local.Source.SourceCursorTactic
import Itasca.Runtime.Compiler.Local.Callbacks.Control.EnterIf
import Itasca.Runtime.Compiler.Local.Callbacks.Function.EnterDead
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CompilerCodeMonotoneControl
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchCertificates
import Itasca.Runtime.Compiler.Local.Coordinates.ControlSourceCoordinates

/-!
Sections, each formerly its own module: ControlMapBounds, ControlMapPublication, OrdinaryMapPublication, ScopeEntryPublication.
-/

/-! ## ControlMapBounds -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Numerical bounds for a closed control map. Intermediate closing targets
may equal the current code length; the final root return makes them strict. -/
def ClosedControlMapBounds (function : runtime.bytecode.CompiledFunction)
    (entry : runtime.compiler.ControlMap) : Prop :=
  entry.start_pc.val ≤ entry.end_pc.val ∧ entry.end_pc.val ≤ function.code.length ∧
    function.body_start.val ≤ entry.source_start.val ∧ entry.source_end.val ≤ function.body_end.val ∧
    entry.source_start.val < entry.source_end.val

/-- A closed map survives later code emission with the same source interval. -/
theorem ClosedControlMapBounds.grow {before after : runtime.bytecode.CompiledFunction}
    {entry : runtime.compiler.ControlMap} (held : ClosedControlMapBounds before entry)
    (code : before.code.length ≤ after.code.length)
    (start : after.body_start = before.body_start) (finish : after.body_end = before.body_end) :
    ClosedControlMapBounds after entry := by
  obtain ⟨ordered,bounded,lower,upper,positive⟩ := held
  exact ⟨ordered,bounded.trans code,by simpa only [start] using lower,
    by simpa only [finish] using upper,positive⟩

/-- Strict code growth after closing establishes the exact numeric contract
used by the actual publication checker. -/
theorem ClosedControlMapBounds.publish {before after : runtime.bytecode.CompiledFunction}
    {entry : runtime.compiler.ControlMap} (held : ClosedControlMapBounds before entry)
    (code : before.code.length < after.code.length)
    (start : after.body_start = before.body_start) (finish : after.body_end = before.body_end) :
    entry.start_pc.val ≤ entry.end_pc.val ∧ entry.end_pc.val < after.code.length ∧
      after.body_start.val ≤ entry.source_start.val ∧ entry.source_end.val ≤ after.body_end.val ∧
      entry.source_start.val < entry.source_end.val := by
  obtain ⟨ordered,bounded,lower,upper,positive⟩ := held
  exact ⟨ordered,bounded.trans_lt code,by simpa only [start] using lower,
    by simpa only [finish] using upper,positive⟩

/-- A still-open control map has a bounded entry PC and source origin. Its
owner is retained separately until the corresponding frame is popped. -/
def OpenControlMapBounds (compiler : runtime.compiler.FunctionCompiler A)
    (entry : runtime.compiler.ControlMap) : Prop :=
  entry.start_pc.val ≤ compiler.function.code.length ∧
    compiler.function.body_start.val ≤ entry.source_start.val ∧
    entry.source_start.val ≤ compiler.function.body_start.val+compiler.next_source.val

/-- Closing bounds depend on the preserved entry fields and computed exit
coordinates, so callback effects need not expose a record representation. -/
theorem OpenControlMapBounds.close_fields {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {entry closed : runtime.compiler.ControlMap} (held : OpenControlMapBounds compiler entry)
    (startPc : closed.start_pc = entry.start_pc) (startSource : closed.source_start = entry.source_start)
    (position : closed.end_pc.val = compiler.function.code.length)
    (endSource : closed.source_end.val = compiler.function.body_start.val+positionSource)
    (progress : compiler.next_source.val < positionSource)
    (endBound : compiler.function.body_start.val+positionSource ≤ compiler.function.body_end.val) :
    ClosedControlMapBounds compiler.function closed := by
  obtain ⟨pc,lower,prior⟩ := held
  unfold ClosedControlMapBounds
  rw [startPc,startSource,position,endSource]
  exact ⟨pc,le_rfl,lower,endBound,by omega⟩

end Itasca.Runtime.Compiler

end

/-! ## ControlMapPublication -/

section

/-!
Publication of control maps when entering and closing scopes, retaining source coordinates and target bounds.
-/

/-! ## Control Map Publication -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Physical frame owners of still-open control maps, in nesting order. -/
def activeControlMaps (compiler : runtime.compiler.FunctionCompiler A) : List Nat :=
  compiler.frames.val.map (fun frame => frame.map.val)

/-- Every map has a bounded entry and source origin. Maps whose owning frame
has closed additionally have ordered, bounded exit coordinates. Open frame
indices remain distinct and in their original declaration order. -/
structure ControlMapPublication (compiler : runtime.compiler.FunctionCompiler A) : Prop where
  ordered : (activeControlMaps compiler).Pairwise (· < ·)
  owners : ∀ index ∈ activeControlMaps compiler, index < compiler.function.controls.length
  entries : ∀ (index : Nat) (entry : runtime.compiler.ControlMap), compiler.function.controls.val[index]? = some entry → OpenControlMapBounds compiler entry
  closed : ∀ (index : Nat) (entry : runtime.compiler.ControlMap), compiler.function.controls.val[index]? = some entry →
    index ∉ activeControlMaps compiler → ClosedControlMapBounds compiler.function entry

/-- Ordinary metadata and code growth retain all control-map publication
bounds when frame ownership is unchanged and the source cursor advances. -/
theorem ControlMapPublication.retained {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (held : ControlMapPublication before) (stable : CompilerStable before after)
    (controls : after.function.controls = before.function.controls)
    (active : activeControlMaps after = activeControlMaps before)
    (code : before.function.code.length ≤ after.function.code.length)
    (cursor : before.next_source.val ≤ after.next_source.val) : ControlMapPublication after := by
  obtain ⟨_,_,_,_,_,_,_,start,finish,_⟩ := stable.fields
  refine ⟨by simpa only [active] using held.ordered,?_,?_,?_⟩
  · simpa only [active,controls] using held.owners
  · intro index entry lookup
    rw [controls] at lookup
    obtain ⟨pc,lower,source⟩ := held.entries index entry lookup
    refine ⟨pc.trans code,by simpa only [start] using lower,?_⟩
    rw [start]
    omega
  · intro index entry lookup inactive
    rw [controls] at lookup
    rw [active] at inactive
    exact (held.closed index entry lookup inactive).grow code start finish

/-- Fresh function-start metadata establishes the control-map invariant before
any body instruction, independently of any completed compilation certificate. -/
theorem ControlMapPublication.initial {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (entry : runtime.compiler.ControlMap) (frame : runtime.compiler.Frame)
    (controls : compiler.function.controls.val = [entry]) (frames : compiler.frames.val = [frame])
    (owner : frame.map.val = 0) (pc : entry.start_pc.val = 0)
    (source : entry.source_start = compiler.function.body_start) : ControlMapPublication compiler := by
  have active : activeControlMaps compiler = [0] := by simp [activeControlMaps,frames,owner]
  refine ⟨by simp [active],?_,?_,?_⟩
  · intro index member
    simp only [active,List.mem_singleton] at member
    subst index
    change 0 < compiler.function.controls.val.length
    simp [controls]
  · intro index map lookup
    have bound := (List.getElem?_eq_some_iff.mp lookup).1
    rw [controls,List.length_singleton] at bound
    have zero : index = 0 := by omega
    subst index
    simp only [controls,List.getElem?_cons_zero,Option.some.injEq] at lookup
    subst map
    exact ⟨by rw [pc]; omega,by rw [source],by rw [source]; omega⟩
  · intro index map lookup inactive
    have bound := (List.getElem?_eq_some_iff.mp lookup).1
    rw [controls,List.length_singleton] at bound
    have zero : index = 0 := by omega
    subst index
    simp [active] at inactive

end Itasca.Runtime.Compiler

end

/-! ## Control Map Publication Close -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Popping the innermost owner and recording its bounded exit preserves all
other control-map ranges. The source origin remains the one established at entry. -/
theorem ControlMapPublication.close {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (held : ControlMapPublication before) (stable : CompilerStable before after)
    (index : Nat) (entry closed : runtime.compiler.ControlMap) (remaining : List Nat)
    (found : before.function.controls.val[index]? = some entry)
    (controls : after.function.controls.val = before.function.controls.val.set index closed)
    (owners : activeControlMaps before = remaining ++ [index])
    (active : activeControlMaps after = remaining)
    (source : closed.source_start = entry.source_start)
    (bounded : ClosedControlMapBounds before.function closed)
    (code : before.function.code.length ≤ after.function.code.length)
    (cursor : before.next_source.val ≤ after.next_source.val) : ControlMapPublication after := by
  obtain ⟨_,_,_,_,_,_,_,start,finish,_⟩ := stable.fields
  have indexBound := (List.getElem?_eq_some_iff.mp found).1
  have length : after.function.controls.val.length = before.function.controls.val.length := by simp [controls]
  have preserve (map : runtime.compiler.ControlMap) (bounds : OpenControlMapBounds before map) :
      OpenControlMapBounds after map := by
    obtain ⟨pc,lower,prior⟩ := bounds
    refine ⟨pc.trans code,by simpa only [start] using lower,?_⟩
    rw [start]
    omega
  have newBounds : OpenControlMapBounds after closed := by
    obtain ⟨ordered,pc,lower,upper,positive⟩ := bounded
    obtain ⟨_,_,origin⟩ := held.entries index entry found
    refine ⟨(ordered.trans pc).trans code,by simpa only [start] using lower,?_⟩
    rw [start,source]
    omega
  refine ⟨?_,?_,?_,?_⟩
  · have ordered := held.ordered
    rw [owners,List.pairwise_append] at ordered
    simpa only [active] using ordered.1
  · intro owner member
    rw [active] at member
    have prior := held.owners owner (by rw [owners]; exact List.mem_append_left _ member)
    change owner < after.function.controls.val.length
    change owner < before.function.controls.val.length at prior
    omega
  · intro other map lookup
    by_cases same : index = other
    · subst other
      rw [controls,List.getElem?_set_self indexBound] at lookup
      have equal := Option.some.inj lookup
      subst map
      exact newBounds
    · rw [controls,List.getElem?_set_ne same] at lookup
      exact preserve map (held.entries other map lookup)
  · intro other map lookup inactive
    by_cases same : index = other
    · subst other
      rw [controls,List.getElem?_set_self indexBound] at lookup
      have equal := Option.some.inj lookup
      subst map
      exact bounded.grow code start finish
    · rw [controls,List.getElem?_set_ne same] at lookup
      have priorInactive : other ∉ activeControlMaps before := by
        intro member
        rw [owners] at member
        simp only [List.mem_append,List.mem_singleton] at member
        rcases member with old | equal
        · apply inactive
          simpa only [active] using old
        · exact same equal.symm
      exact (held.closed other map lookup priorInactive).grow code start finish

/-- After the last owner closes, the actual root-return emission makes every
control-map target strictly smaller than the completed code length. -/
theorem ControlMapPublication.close_last_publish {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (held : ControlMapPublication before) (stable : CompilerStable before after)
    (index : Nat) (entry closed : runtime.compiler.ControlMap)
    (found : before.function.controls.val[index]? = some entry)
    (controls : after.function.controls.val = before.function.controls.val.set index closed)
    (owners : activeControlMaps before = [index])
    (bounded : ClosedControlMapBounds before.function closed)
    (code : before.function.code.length < after.function.code.length) :
    ∀ map ∈ after.function.controls.val,
      map.start_pc.val ≤ map.end_pc.val ∧ map.end_pc.val < after.function.code.length ∧
      after.function.body_start.val ≤ map.source_start.val ∧ map.source_end.val ≤ after.function.body_end.val ∧
      map.source_start.val < map.source_end.val := by
  obtain ⟨_,_,_,_,_,_,_,start,finish,_⟩ := stable.fields
  have indexBound := (List.getElem?_eq_some_iff.mp found).1
  intro map member
  obtain ⟨other,lookup⟩ := List.mem_iff_getElem?.mp member
  by_cases same : index = other
  · subst other
    rw [controls,List.getElem?_set_self indexBound] at lookup
    have equal := Option.some.inj lookup
    subst map
    exact bounded.publish code start finish
  · rw [controls,List.getElem?_set_ne same] at lookup
    have inactive : other ∉ activeControlMaps before := by simpa only [owners,List.mem_singleton] using Ne.symm same
    exact (held.closed other map lookup inactive).publish code start finish

end Itasca.Runtime.Compiler

end

/-! ## Control Map Publication Enter -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Appending a fresh map and its uniquely indexed owner preserves every
closed range and the nesting order of all still-open map indices. -/
theorem ControlMapPublication.push {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (held : ControlMapPublication before) (stable : CompilerStable before after)
    (entry : runtime.compiler.ControlMap)
    (controls : after.function.controls.val = before.function.controls.val ++ [entry])
    (active : activeControlMaps after = activeControlMaps before ++ [before.function.controls.length])
    (code : before.function.code.length ≤ after.function.code.length)
    (cursor : before.next_source.val ≤ after.next_source.val)
    (fresh : OpenControlMapBounds after entry) : ControlMapPublication after := by
  obtain ⟨_,_,_,_,_,_,_,start,finish,_⟩ := stable.fields
  have length : after.function.controls.val.length = before.function.controls.val.length+1 := by
    simp [controls]
  have preserve (map : runtime.compiler.ControlMap) (bounds : OpenControlMapBounds before map) :
      OpenControlMapBounds after map := by
    obtain ⟨pc,lower,source⟩ := bounds
    refine ⟨pc.trans code,by simpa only [start] using lower,?_⟩
    rw [start]
    omega
  refine ⟨?_,?_,?_,?_⟩
  · rw [active,List.pairwise_append]
    refine ⟨held.ordered,by simp,?_⟩
    intro index member next singleton
    simp only [List.mem_singleton] at singleton
    subst next
    exact held.owners index member
  · intro index member
    rw [active] at member
    simp only [List.mem_append,List.mem_singleton] at member
    rcases member with old | rfl
    · have oldBound := held.owners index old
      change index < after.function.controls.val.length
      change index < before.function.controls.val.length at oldBound
      omega
    · change before.function.controls.val.length < after.function.controls.val.length
      omega
  · intro index map lookup
    have bound := (List.getElem?_eq_some_iff.mp lookup).1
    by_cases old : index < before.function.controls.val.length
    · rw [controls,List.getElem?_append_left old] at lookup
      exact preserve map (held.entries index map lookup)
    · have same : index = before.function.controls.val.length := by omega
      subst index
      simp [controls,List.getElem?_append] at lookup
      subst map
      exact fresh
  · intro index map lookup inactive
    have bound := (List.getElem?_eq_some_iff.mp lookup).1
    have old : index < before.function.controls.val.length := by
      have different : index ≠ before.function.controls.val.length := by
        intro same
        apply inactive
        rw [active]
        apply List.mem_append_right
        simpa only [same,alloc.vec.Vec.length] using (List.mem_singleton_self before.function.controls.val.length)
      omega
    rw [controls,List.getElem?_append_left old] at lookup
    have oldInactive : index ∉ activeControlMaps before := by
      intro member
      apply inactive
      rw [active]
      exact List.mem_append_left _ member
    exact (held.closed index map lookup oldInactive).grow code start finish

end Itasca.Runtime.Compiler

end

end

/-! ## OrdinaryMapPublication -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Ordinary callbacks retain map entries and owners. Code growth and source
progress are enough to preserve their publication bounds. -/
theorem ControlMapPublication.ordinary {A : Type}
    {before after : runtime.compiler.FunctionCompiler A}
    (held : ControlMapPublication before) (stable : CompilerOrdinaryStable before after)
    (code : before.function.code.length ≤ after.function.code.length)
    (cursor : before.next_source.val ≤ after.next_source.val) : ControlMapPublication after := by
  apply held.retained stable.stable stable.controls _ code cursor
  simp only [activeControlMaps,stable.frames]

/-- Actual bytecode emission retains all control-map bounds. -/
theorem compiler_emit_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (instruction : runtime.bytecode.Instr)
    (held : ControlMapPublication before)
    (called : runtime.compiler.FunctionCompiler.emit ops before instruction = .ok (.Ok (),after)) :
    ControlMapPublication after := by
  apply held.ordinary (compiler_emit_ordinary_result ops before after instruction (.Ok ()) called)
    (compiler_emit_code_mono ops law before after instruction (.Ok ()) called)
  rw [compiler_emit_cursor ops before after instruction (.Ok ()) called]

/-- Actual observation preserves control-map bounds while advancing the reader cursor. -/
theorem compiler_observe_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (held : ControlMapPublication before)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.FunctionCompiler.observe ops before state = .ok (.Ok (),after)) :
    ControlMapPublication after := by
  apply held.ordinary (compiler_observe_ordinary_result ops law before after state (.Ok ()) called)
    (compiler_observe_code_mono ops law before after state (.Ok ()) called)
  rw [compiler_observe_cursor ops law before after state (.Ok ()) called rfl]
  exact forward

end Itasca.Runtime.Compiler

end

/-! ## ScopeEntryPublication -/

section

/-!
Publication of entered scope maps. Block, loop and if effects establish the common ScopeEntryGeometry and publication result.
-/

/-! ## Control Map Enter Effect -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Exact frame and map appends from the enter callbacks establish ownership
and the new map's bounds from its emitted position and source origin. -/
theorem ControlMapPublication.enter_effect {A : Type}
    {before after : runtime.compiler.FunctionCompiler A}
    (held : ControlMapPublication before) (stable : CompilerStable before after)
    (frame : runtime.compiler.Frame) (entry : runtime.compiler.ControlMap)
    (frames : after.frames.val = before.frames.val ++ [frame])
    (owner : frame.map.val = before.function.controls.length)
    (controls : after.function.controls.val = before.function.controls.val ++ [entry])
    (position : entry.start_pc.val ≤ after.function.code.length)
    (origin : entry.source_start.val = before.function.body_start.val+before.next_source.val)
    (code : before.function.code.length ≤ after.function.code.length)
    (cursor : before.next_source.val ≤ after.next_source.val) : ControlMapPublication after := by
  have active : activeControlMaps after = activeControlMaps before ++ [before.function.controls.length] := by
    simp [activeControlMaps,frames,owner]
  apply held.push stable entry controls active code cursor
  obtain ⟨_,_,_,_,_,_,_,start,_,_⟩ := stable.fields
  unfold OpenControlMapBounds
  rw [origin,start]
  exact ⟨position,by omega,by omega⟩

end Itasca.Runtime.Compiler

end

/-! ## Enter Map Publication -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Actual BLOCK entry establishes the newly owned map bounds. -/
theorem compiler_enter_block_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature) (pc : U32)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt compiler.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (heightFits : compiler.function.local_slots.val +
      stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max)
    (sourceFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (position : pc.val = compiler.function.code.val.length)
    (mapsFit : compiler.function.controls.val.length < Usize.max)
    (framesFit : compiler.frames.val.length < Usize.max)
    (reachable : compiler.reachable = true)
    (held : ControlMapPublication compiler) (forward : compiler.next_source.val ≤ state.pos.val)
    (after : runtime.compiler.FunctionCompiler A)
    (called : runtime.compiler.control.FunctionCompiler.enter ops compiler state .Block bt = .ok (.Ok (),after)) :
    ControlMapPublication after := by
  have effect := enter_block ops law compiler state ctrl prior bt signature pc controls selected valuesFit heightFits sourceFits position mapsFit framesFit reachable
  rw [called,WP.spec_ok] at effect
  obtain ⟨code,_,height,source,_,origin,frames,maps⟩ := effect rfl
  have stable := compiler_enter_stable_result ops law compiler after state .Block bt (.Ok ()) called
  have growth := compiler_enter_code_mono ops law compiler after state .Block bt called
  have cursor := compiler_enter_cursor ops law compiler after state .Block bt called
  have pcBound : pc.val ≤ after.function.code.val.length := by
    rw [code]
    omega
  apply held.enter_effect stable _ _ frames (by simp [alloc.vec.Vec.len]) maps
    (by change (UScalar.cast .Usize pc).val ≤ after.function.code.length; scalar_tac) origin growth
  rw [cursor]
  exact forward

/-- Actual LOOP entry establishes the newly owned map bounds. -/
theorem compiler_enter_loop_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature) (pc : U32)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt compiler.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (heightFits : compiler.function.local_slots.val +
      stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max)
    (sourceFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (position : pc.val = compiler.function.code.val.length)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length < Usize.max)
    (mapsFit : compiler.function.controls.val.length < Usize.max)
    (framesFit : compiler.frames.val.length < Usize.max)
    (reachable : compiler.reachable = true)
    (held : ControlMapPublication compiler) (forward : compiler.next_source.val ≤ state.pos.val)
    (after : runtime.compiler.FunctionCompiler A)
    (called : runtime.compiler.control.FunctionCompiler.enter ops compiler state .Loop bt = .ok (.Ok (),after)) :
    ControlMapPublication after := by
  have effect := enter_loop ops law compiler state ctrl prior bt signature pc controls selected valuesFit heightFits sourceFits position codeFits offsetsFit mapsFit framesFit reachable
  rw [called,WP.spec_ok] at effect
  obtain ⟨code,_,height,source,_,origin,frames,maps⟩ := effect rfl
  have stable := compiler_enter_stable_result ops law compiler after state .Loop bt (.Ok ()) called
  have growth := compiler_enter_code_mono ops law compiler after state .Loop bt called
  have cursor := compiler_enter_cursor ops law compiler after state .Loop bt called
  have pcBound : pc.val ≤ after.function.code.val.length := by
    rw [code]
    simp only [List.length_append,List.length_singleton]
    omega
  apply held.enter_effect stable _ _ frames (by simp [alloc.vec.Vec.len]) maps
    (by change (UScalar.cast .Usize pc).val ≤ after.function.code.length; scalar_tac) origin growth
  rw [cursor]
  exact forward

/-- Actual IF entry establishes the newly owned map bounds. -/
theorem compiler_enter_if_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature) (pc : U32)
    (stack : List valtype) (layout : CompilerLayout compiler (stack ++ [.I32]))
    (codeFits : compiler.function.code.val.length < Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length < Usize.max)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt compiler.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (heightFits : compiler.function.local_slots.val +
      stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max)
    (sourceFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (position : pc.val = compiler.function.code.val.length + 1)
    (mapsFit : compiler.function.controls.val.length < Usize.max)
    (framesFit : compiler.frames.val.length < Usize.max)
    (reachable : compiler.reachable = true)
    (held : ControlMapPublication compiler) (forward : compiler.next_source.val ≤ state.pos.val)
    (after : runtime.compiler.FunctionCompiler A)
    (called : runtime.compiler.control.FunctionCompiler.enter ops compiler state .Then bt = .ok (.Ok (),after)) :
    ControlMapPublication after := by
  have effect := enter_if ops law compiler state ctrl prior bt signature pc stack layout codeFits offsetsFit controls selected valuesFit heightFits sourceFits position mapsFit framesFit reachable
  rw [called,WP.spec_ok] at effect
  obtain ⟨_,condition,height,source,_,code,_,origin,frames,maps⟩ := effect rfl
  have stable := compiler_enter_stable_result ops law compiler after state .Then bt (.Ok ()) called
  have growth := compiler_enter_code_mono ops law compiler after state .Then bt called
  have cursor := compiler_enter_cursor ops law compiler after state .Then bt called
  have pcBound : pc.val ≤ after.function.code.val.length := by
    rw [code]
    simp only [List.length_append,List.length_singleton]
    omega
  apply held.enter_effect stable _ _ frames (by simp [alloc.vec.Vec.len]) maps
    (by change (UScalar.cast .Usize pc).val ≤ after.function.code.length; scalar_tac) origin growth
  rw [cursor]
  exact forward

/-- Actual DEAD entry establishes the newly owned map bounds. -/
theorem compiler_enter_dead_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature) (pc : U32)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt compiler.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (heightFits : compiler.function.local_slots.val +
      stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max)
    (sourceFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (position : pc.val = compiler.function.code.val.length)
    (mapsFit : compiler.function.controls.val.length < Usize.max)
    (framesFit : compiler.frames.val.length < Usize.max)
    (reachable : compiler.reachable = false)
    (held : ControlMapPublication compiler) (forward : compiler.next_source.val ≤ state.pos.val)
    (after : runtime.compiler.FunctionCompiler A)
    (called : runtime.compiler.control.FunctionCompiler.enter ops compiler state kind bt = .ok (.Ok (),after)) :
    ControlMapPublication after := by
  have effect := enter_dead ops law compiler state ctrl prior kind bt signature pc controls selected valuesFit heightFits sourceFits position mapsFit framesFit reachable
  rw [called,WP.spec_ok] at effect
  obtain ⟨code,_,height,source,_,origin,frames,maps⟩ := effect rfl
  have stable := compiler_enter_stable_result ops law compiler after state kind bt (.Ok ()) called
  have growth := compiler_enter_code_mono ops law compiler after state kind bt called
  have cursor := compiler_enter_cursor ops law compiler after state kind bt called
  have pcBound : pc.val ≤ after.function.code.val.length := by
    rw [code]
    omega
  apply held.enter_effect stable _ _ frames (by simp [alloc.vec.Vec.len]) maps
    (by change (UScalar.cast .Usize pc).val ≤ after.function.code.length; scalar_tac) origin growth
  rw [cursor]
  exact forward

end Itasca.Runtime.Compiler

end

/-! ## Scope Entry Publication -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Source-reader geometry needed to open a frame. These are local stack,
signature, coordinate and reserve bounds, independent of completed code. -/
structure ScopeEntryGeometry {A : Type} (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType) where
  ctrl : Itasca.code.Ctrl
  prior : List Itasca.code.Ctrl
  signature : runtime.compiler.Signature
  pc : U32
  controls : state.ctrls.val = prior ++ [ctrl]
  selected : SignatureAt before.signatures bt signature
  valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length
  heightFits : before.function.local_slots.val+stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max
  sourceFits : before.function.body_start.val+before.next_source.val ≤ Usize.max
  mapsFit : before.function.controls.val.length < Usize.max
  framesFit : before.frames.val.length < Usize.max

/-- Live IF accounts for its guard, live LOOP for its hook, and dead entry
emits neither. Reachability and PC premises refer to the current prefix. -/
inductive ScopeEntryMode {A : Type} {before : runtime.compiler.FunctionCompiler A}
    {state : Itasca.code.OpIterState} {bt : Itasca.signature.BlockType}
    (geometry : ScopeEntryGeometry before state bt) : Itasca.code.LabelKind → Prop where
  | block (live : before.reachable = true)
      (position : geometry.pc.val = before.function.code.val.length) : ScopeEntryMode geometry .Block
  | loop (live : before.reachable = true)
      (position : geometry.pc.val = before.function.code.val.length)
      (codeFits : before.function.code.val.length < Usize.max)
      (offsetsFit : before.function.source_offsets.val.length < Usize.max) : ScopeEntryMode geometry .Loop
  | if_ (stack : List valtype) (layout : CompilerLayout before (stack ++ [.I32]))
      (live : before.reachable = true)
      (position : geometry.pc.val = before.function.code.val.length+1)
      (codeFits : before.function.code.val.length < Usize.max)
      (offsetsFit : before.function.source_offsets.val.length < Usize.max) : ScopeEntryMode geometry .Then
  | dead (kind : Itasca.code.LabelKind) (dormant : before.reachable = false)
      (position : geometry.pc.val = before.function.code.val.length) : ScopeEntryMode geometry kind

/-- Actual frame entry preserves source coordinates and control-map bounds
from the source reader's local geometry, in every live and dormant mode. -/
theorem compiler_scope_entry_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (geometry : ScopeEntryGeometry before state bt) (mode : ScopeEntryMode geometry kind)
    (coordinates : SourceCoordinates before) (maps : ControlMapPublication before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.control.FunctionCompiler.enter ops before state kind bt = .ok (.Ok (),after)) :
    SourceCoordinates after ∧ ControlMapPublication after := by
  refine ⟨compiler_enter_source_coordinates ops law before after state kind bt coordinates inside forward called,?_⟩
  cases mode with
  | block live position =>
    exact compiler_enter_block_map_publication ops law before state geometry.ctrl geometry.prior bt geometry.signature geometry.pc
      geometry.controls geometry.selected geometry.valuesFit geometry.heightFits geometry.sourceFits position
      geometry.mapsFit geometry.framesFit live maps forward after called
  | loop live position codeFits offsetsFit =>
    exact compiler_enter_loop_map_publication ops law before state geometry.ctrl geometry.prior bt geometry.signature geometry.pc
      geometry.controls geometry.selected geometry.valuesFit geometry.heightFits geometry.sourceFits position codeFits offsetsFit
      geometry.mapsFit geometry.framesFit live maps forward after called
  | if_ stack layout live position codeFits offsetsFit =>
    exact compiler_enter_if_map_publication ops law before state geometry.ctrl geometry.prior bt geometry.signature geometry.pc
      stack layout codeFits offsetsFit geometry.controls geometry.selected geometry.valuesFit geometry.heightFits
      geometry.sourceFits position geometry.mapsFit geometry.framesFit live maps forward after called
  | dead kind dormant position =>
    exact compiler_enter_dead_map_publication ops law before state geometry.ctrl geometry.prior kind bt geometry.signature geometry.pc
      geometry.controls geometry.selected geometry.valuesFit geometry.heightFits geometry.sourceFits position
      geometry.mapsFit geometry.framesFit dormant maps forward after called

end Itasca.Runtime.Compiler

end

end
