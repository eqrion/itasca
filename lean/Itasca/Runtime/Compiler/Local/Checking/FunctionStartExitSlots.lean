import Itasca.Runtime.Compiler.Local.Checking.ScopeEntryInstructionPrefix
import Itasca.Runtime.Compiler.Local.Publication.StartMapPublication
import Itasca.Runtime.Compiler.Local.Relations.Table.ControlTablePreservation

/-!
Sections, each formerly its own module: PendingInstructionClose, ScopeCloseInstructionPrefix, ScopeCloseExitSlots, ScopeEntryExitSlots, RootInstructionPublication, RootCloseInstructionPrefix, FunctionStartExitSlots.
-/

/-! ## PendingInstructionClose -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Exact pending sites owned by one physical frame. IF guards are patched
before its ordinary forward-branch fixups. -/
def frameInstructionSites (frame : runtime.compiler.Frame) : List Usize :=
  frame.if_pc.toList++frame.fixups.val

/-- Once all sites of the popped frame have been patched, any remaining
pending instruction still has an owner in the retained physical frame stack. -/
theorem pending_instruction_pop {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (frame : runtime.compiler.Frame) (rest : alloc.vec.Vec runtime.compiler.Frame)
    (beforeFrames : before.frames.val = rest.val++[frame]) (afterFrames : after.frames = rest)
    (index : Nat) (unpatched : ∀ site ∈ frameInstructionSites frame, site.val ≠ index)
    (owned : PendingInstructionSite before index) : PendingInstructionSite after index := by
  obtain ⟨owner,member,site,position,kind⟩ := owned
  rw [beforeFrames] at member
  rcases List.mem_append.mp member with remaining | closing
  · exact ⟨owner,by simpa only [afterFrames] using remaining,site,position,kind⟩
  · have same : owner = frame := by simpa only [List.mem_singleton] using closing
    subst owner
    have selected : site ∈ frameInstructionSites frame := by
      rcases kind with guard | branch
      · simp [frameInstructionSites,guard]
      · exact List.mem_append_right _ branch
    exact False.elim (unpatched site selected position)

/-- Popping and patching a complete frame preserves checks of every stored
instruction, including instructions skipped by source reachability. -/
theorem compiler_instruction_prefix_close {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (held : CompilerInstructionPrefix before) (frame : runtime.compiler.Frame)
    (rest : alloc.vec.Vec runtime.compiler.Frame) (target : U32)
    (beforeFrames : before.frames.val = rest.val++[frame]) (afterFrames : after.frames = rest)
    (growth : InstructionCheckExtends before.function after.function)
    (code : after.function.code.val = patchCode before.function.code.val (frameInstructionSites frame) target)
    (inside : target.val ≤ after.function.code.length) : CompilerInstructionPrefix after :=
  held.patch growth (frameInstructionSites frame) target code inside
    (pending_instruction_pop frame rest beforeFrames afterFrames)

end Itasca.Runtime.Compiler

end

/-! ## ScopeCloseInstructionPrefix -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Actual nested END patches all sites of its closing frame, removes that
owner, and preserves every instruction's local check. Function-root END also
emits an epilogue and is treated separately. -/
theorem compiler_scope_close_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (geometry : ScopeCloseGeometry before) (mode : ScopeCloseMode geometry)
    (nonBody : geometry.frame.kind ≠ .Body) (maps : ControlMapPublication before)
    (coordinateFits : before.function.body_start.val+state.pos.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after := by
  have growth := InstructionCheckExtends.of_tables_equal before.function after.function
    (compiler_end_tables ops law before after state kind bt called)
    (compiler_end_stable_result ops law before after state kind bt (.Ok ()) called).capacity
    (compiler_end_code_mono ops law before after state kind bt called)
  have inside : geometry.target.val ≤ after.function.code.length := by
    change geometry.target.val ≤ after.function.code.val.length
    rw [geometry.position]
    exact growth.code
  have mapFits : geometry.frame.map.val < before.function.controls.val.length := by
    apply maps.owners
    simp [activeControlMaps,geometry.frames]
  have canonical : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state .Block .Empty =
      .ok (.Ok (),after) := called
  cases mode with
  | unguarded noIf codeFits sourceFits emitCoordinateFits =>
    have effect := close_scope_effect ops law before state geometry.frame geometry.rest geometry.target
      geometry.frames nonBody noIf geometry.position geometry.branches mapFits coordinateFits
    rw [canonical,WP.spec_ok] at effect
    obtain ⟨frames,_,code,_⟩ := effect rfl
    apply compiler_instruction_prefix_close held geometry.frame geometry.rest geometry.target geometry.frames frames growth _ inside
    simpa only [frameInstructionSites,noIf,Option.toList_none,List.nil_append] using code
  | guarded guard condition old _ hasIf guardCode =>
    have effect := close_guarded_map_effect ops law before state geometry.frame geometry.rest geometry.target geometry.frames
      guard condition old nonBody hasIf guardCode geometry.position geometry.branches mapFits coordinateFits
    rw [canonical,WP.spec_ok] at effect
    obtain ⟨frames,code,_⟩ := effect rfl
    have patched : patchCode before.function.code.val [guard] geometry.target =
        before.function.code.val.set guard.val (.JumpIfZero condition geometry.target) := by
      simp [patchCode,guardCode,retarget]
    apply compiler_instruction_prefix_close held geometry.frame geometry.rest geometry.target geometry.frames frames growth _ inside
    rw [frameInstructionSites,hasIf]
    simp only [Option.toList_some]
    rw [patch_code_append_sites,patched]
    exact code

end Itasca.Runtime.Compiler

end

/-! ## ScopeCloseExitSlots -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Actual nested END removes its frame while retaining slot bounds of every
outer forward exit, including guarded scope closure. -/
theorem compiler_scope_close_exit_slots {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (geometry : ScopeCloseGeometry before) (mode : ScopeCloseMode geometry)
    (nonBody : geometry.frame.kind ≠ .Body) (maps : ControlMapPublication before)
    (coordinateFits : before.function.body_start.val+state.pos.val ≤ Usize.max)
    (held : FrameExitSlotBounds before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (),after)) :
    FrameExitSlotBounds after := by
  have capacity := (compiler_end_stable_result ops law before after state kind bt (.Ok ()) called).capacity
  have mapFits : geometry.frame.map.val < before.function.controls.val.length := by
    apply maps.owners
    simp [activeControlMaps,geometry.frames]
  have canonical : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state .Block .Empty =
      .ok (.Ok (),after) := called
  cases mode with
  | unguarded noIf codeFits sourceFits emitCoordinateFits =>
    have effect := close_scope_effect ops law before state geometry.frame geometry.rest geometry.target
      geometry.frames nonBody noIf geometry.position geometry.branches mapFits coordinateFits
    rw [canonical,WP.spec_ok] at effect
    obtain ⟨frames,_,code,_⟩ := effect rfl
    exact held.pop geometry.frame (by rw [frames]; exact geometry.frames) capacity
  | guarded guard condition old _ hasIf guardCode =>
    have effect := close_guarded_map_effect ops law before state geometry.frame geometry.rest geometry.target geometry.frames
      guard condition old nonBody hasIf guardCode geometry.position geometry.branches mapFits coordinateFits
    rw [canonical,WP.spec_ok] at effect
    obtain ⟨frames,code,_⟩ := effect rfl
    exact held.pop geometry.frame (by rw [frames]; exact geometry.frames) capacity

end Itasca.Runtime.Compiler

end

/-! ## ScopeEntryExitSlots -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Actual scope entry retains previous result bounds and introduces a frame
with no recorded forward exit, in both live and dormant source code. -/
theorem compiler_scope_entry_exit_slots {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (geometry : ScopeEntryGeometry before state bt) (mode : ScopeEntryMode geometry kind)
    (held : FrameExitSlotBounds before)
    (called : runtime.compiler.control.FunctionCompiler.enter ops before state kind bt = .ok (.Ok (),after)) :
    FrameExitSlotBounds after := by
  have capacity := (compiler_enter_stable_result ops law before after state kind bt (.Ok ()) called).capacity
  cases mode with
  | block live position =>
    have effect := enter_block ops law before state geometry.ctrl geometry.prior bt geometry.signature geometry.pc
      geometry.controls geometry.selected geometry.valuesFit geometry.heightFits geometry.sourceFits position
      geometry.mapsFit geometry.framesFit live
    rw [called,WP.spec_ok] at effect
    obtain ⟨code,_,height,source,_,_,frames,_⟩ := effect rfl
    exact held.push _ frames rfl capacity
  | loop live position codeFits offsetsFit =>
    have effect := enter_loop ops law before state geometry.ctrl geometry.prior bt geometry.signature geometry.pc
      geometry.controls geometry.selected geometry.valuesFit geometry.heightFits geometry.sourceFits position codeFits offsetsFit
      geometry.mapsFit geometry.framesFit live
    rw [called,WP.spec_ok] at effect
    obtain ⟨code,_,height,source,_,_,frames,_⟩ := effect rfl
    exact held.push _ frames rfl capacity
  | if_ stack layout live position codeFits offsetsFit =>
    have effect := enter_if ops law before state geometry.ctrl geometry.prior bt geometry.signature geometry.pc
      stack layout codeFits offsetsFit geometry.controls geometry.selected geometry.valuesFit geometry.heightFits
      geometry.sourceFits position geometry.mapsFit geometry.framesFit live
    rw [called,WP.spec_ok] at effect
    obtain ⟨_,condition,height,source,conditionPosition,code,_,_,frames,_⟩ := effect rfl
    exact held.push _ frames rfl capacity
  | dead kind dormant position =>
    have effect := enter_dead ops law before state geometry.ctrl geometry.prior kind bt geometry.signature geometry.pc
      geometry.controls geometry.selected geometry.valuesFit geometry.heightFits geometry.sourceFits position
      geometry.mapsFit geometry.framesFit dormant
    rw [called,WP.spec_ok] at effect
    obtain ⟨code,_,height,source,_,_,frames,_⟩ := effect rfl
    exact held.push _ frames rfl capacity

end Itasca.Runtime.Compiler

end

/-! ## RootInstructionPublication -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Patching the last frame and appending a checked epilogue discharges every
pending branch obligation. Earlier resolved end targets become strict because
the actual code vector grows. -/
theorem compiler_instruction_root_publish {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (held : CompilerInstructionPrefix before) (frame : runtime.compiler.Frame)
    (rest : alloc.vec.Vec runtime.compiler.Frame) (target : U32)
    (beforeFrames : before.frames.val = rest.val++[frame]) (afterFrames : after.frames = rest)
    (closed : rest.val = []) (growth : InstructionCheckExtends before.function after.function)
    (fragment : List runtime.bytecode.Instr)
    (code : after.function.code.val = patchCode before.function.code.val (frameInstructionSites frame) target++fragment)
    (nonempty : 0 < fragment.length) (inside : target.val < after.function.code.length)
    (fresh : ∀ instruction ∈ fragment,
      runtime.bytecode.CompiledFunction.instruction_valid after.function instruction = .ok true) :
    CheckedInstructionPrefix after.function := by
  have strict : before.function.code.length < after.function.code.length := by
    change before.function.code.val.length < after.function.code.val.length
    rw [code,List.length_append,patch_code_length]
    omega
  intro instruction member
  rw [code] at member
  rcases List.mem_append.mp member with old | new
  · obtain ⟨index,bound,found⟩ := List.getElem_of_mem old
    have fetched : (patchCode before.function.code.val (frameInstructionSites frame) target)[index]? = some instruction := by
      simp [List.getElem?_eq_getElem bound,found]
    rw [patch_code_get] at fetched
    split at fetched
    · cases original : before.function.code.val[index]? with
      | none => simp [original] at fetched
      | some prior =>
        have same : retarget prior target = instruction := by simpa [original] using fetched
        rw [← same]
        exact (held index prior original).retarget_accepts growth target inside
    · rename_i unchanged
      have old := held index instruction fetched
      have noOwner : PendingInstructionSite before index → False := by
        intro owned
        have remaining := pending_instruction_pop frame rest beforeFrames afterFrames index (by simpa using unchanged) owned
        obtain ⟨owner,member,_⟩ := remaining
        rw [afterFrames,closed] at member
        cases member
      have checked : OpenInstructionCheck before.function (fun _ => False) index instruction :=
        old.grow (.refl _) noOwner
      exact checked.publish growth strict
  · exact fresh instruction new

end Itasca.Runtime.Compiler

end

/-! ## RootCloseInstructionPrefix -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- The actual final END patches the root frame and emits a checked return.
Source result layout bounds the epilogue. No final checker success or completed
function instruction certificate is assumed. -/
theorem compiler_root_close_checked_instructions_of_slots {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (geometry : ScopeCloseGeometry before) (body : geometry.frame.kind = .Body)
    (closed : geometry.rest.val = []) (noIf : geometry.frame.if_pc = none)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (emitCoordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max)
    (coordinateFits : before.function.body_start.val+state.pos.val ≤ Usize.max)
    (maps : ControlMapPublication before) (held : CompilerInstructionPrefix before)
    (returnFits : geometry.frame.height.val+
      (if scopeExitLive before.reachable geometry.frame then geometry.frame.results else 0#u32).val ≤ after.function.slot_count.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (),after)) :
    CheckedInstructionPrefix after.function := by
  have growth := InstructionCheckExtends.of_tables_equal before.function after.function
    (compiler_end_tables ops law before after state kind bt called)
    (compiler_end_stable_result ops law before after state kind bt (.Ok ()) called).capacity
    (compiler_end_code_mono ops law before after state kind bt called)
  have mapFits : geometry.frame.map.val < before.function.controls.val.length := by
    apply maps.owners
    simp [activeControlMaps,geometry.frames]
  have canonical : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state .Block .Empty =
      .ok (.Ok (),after) := called
  have effect := close_function_effect ops law before state geometry.frame geometry.rest geometry.target geometry.frames body noIf
    geometry.position geometry.branches mapFits coordinateFits codeFits sourceFits emitCoordinateFits
  rw [canonical,WP.spec_ok] at effect
  obtain ⟨frames,reachable,code,_⟩ := effect rfl
  apply compiler_instruction_root_publish held geometry.frame geometry.rest geometry.target geometry.frames frames closed growth
    [.Return geometry.frame.height (if scopeExitLive before.reachable geometry.frame then geometry.frame.results else 0#u32)]
    (by simpa only [frameInstructionSites,noIf,Option.toList_none,List.nil_append] using code) (by simp)
  · change geometry.target.val < after.function.code.val.length
    rw [code,List.length_append,patch_code_length,List.length_singleton,geometry.position]
    omega
  · intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    exact (CoreInstructionBounds.return_ returnFits).accepts

end Itasca.Runtime.Compiler

end

/-! ## FunctionStartExitSlots -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Actual fresh construction and function-start introduce only the root frame,
whose forward-exit flag is initially clear. -/
theorem compiler_start_exit_slots {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (signatures : Slice runtime.compiler.Signature)
    (functionSlots : Slice U32) (budget : runtime.compiler.Budget A) (batchStart : Usize)
    (initial started : runtime.compiler.FunctionCompiler A)
    (ctx : Itasca.code.Context) (typeIndex : U32) (signature : runtime.compiler.Signature)
    (bodyBegin bodyEnd : Usize)
    (lookup : signatures.val[typeIndex.val]? = some signature)
    (beginFits : batchStart.val+bodyBegin.val ≤ Usize.max)
    (endFits : batchStart.val+bodyEnd.val ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    (begun : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops initial ctx typeIndex bodyBegin bodyEnd = .ok (.Ok (),started)) : FrameExitSlotBounds started := by
  have newPost := compiler_new ops signatures functionSlots budget batchStart
  rw [created,WP.spec_ok] at newPost
  obtain ⟨layout,emptyLocals,emptyOperands,emptyMaps,emptyFrames,emptyCode,reachable,sigs,widths,coordinate⟩ := newPost
  have startPost := compiler_function_start_raw ops law initial ctx typeIndex signature bodyBegin bodyEnd
    (by simpa only [sigs] using lookup) (by simpa only [coordinate] using beginFits)
    (by simpa only [coordinate] using endFits) emptyLocals layout emptyOperands
    (by simp [emptyMaps]; scalar_tac) (by simp [emptyFrames]; scalar_tac)
  rw [begun,WP.spec_ok] at startPost
  obtain ⟨_,_,frames,_⟩ := startPost rfl
  intro frame member live
  rw [frames,emptyFrames,List.nil_append] at member
  have same := List.mem_singleton.mp member
  subst frame
  simp at live

end Itasca.Runtime.Compiler

end
