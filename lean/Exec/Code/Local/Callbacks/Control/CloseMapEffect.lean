import Exec.Code.Local.Callbacks.Common.CloseFunction

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Only the root frame emits an epilogue when its map is closed. -/
def closeMapEpilogue (reachable : Bool) (frame : runtime.compiler.Frame) : List runtime.bytecode.Instr :=
  match frame.kind with
  | .Body => [.Return frame.height (if scopeExitLive reachable frame then frame.results else 0#u32)]
  | _ => []

/-- Exact map mutation by an unguarded scope close. This retains the original
map entry and complete updated vector, rather than only the two exit fields. -/
theorem close_unguarded_map_effect {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (frame : runtime.compiler.Frame)
    (rest : alloc.vec.Vec runtime.compiler.Frame) (target : U32)
    (frames : compiler.frames.val = rest.val ++ [frame]) (noIf : frame.if_pc = none)
    (position : target.val = compiler.function.code.val.length)
    (branches : BranchSites compiler.function.code.val frame.fixups.val)
    (mapFits : frame.map.val < compiler.function.controls.val.length)
    (coordinateFits : compiler.function.body_start.val+state.pos.val ≤ Usize.max)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (emitCoordinateFits : compiler.function.body_start.val+compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops compiler state .Block .Empty ⦃ out =>
      out.1 = .Ok () → out.2.frames = rest ∧
        out.2.function.code.val = patchCode compiler.function.code.val frame.fixups.val target ++
          closeMapEpilogue compiler.reachable frame ∧
        ∃ original closed, compiler.function.controls.val[frame.map.val]? = some original ∧
          out.2.function.controls.val = compiler.function.controls.val.set frame.map.val closed ∧
          closed.start_pc = original.start_pc ∧ closed.source_start = original.source_start ∧
          closed.end_pc.val = target.val ∧
          closed.source_end.val = compiler.function.body_start.val+state.pos.val ⦄ := by
  have pop : alloc.vec.Vec.pop Global compiler.frames = .ok (some frame,rest) := by
    simp only [alloc.vec.Vec.pop,frames,List.getLast?_concat,List.dropLast_concat]
    congr 2
    apply alloc.vec.Vec.ext
    simp
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end
  have popSpec : alloc.vec.Vec.pop Global compiler.frames ⦃ out => out = (some frame,rest) ⦄ := by
    rw [pop]
    simp [WP.spec_ok]
  step with popSpec as ⟨o,remaining,ho,hremaining⟩
  subst o remaining
  simp only [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  rw [compiler_pc_eq ops {compiler with frames := rest} target position]
  simp only [bind_ok,noIf]
  step with compiler_fixups ops {compiler with frames := rest} frame.fixups target 0#usize
    (by simp) branches as ⟨s,params,budget,batch,func,frames',reach,source,before,height,offsets,depths,
      result,after,hsnapshot,onlyCode,effect⟩
  simp only [compilerSnapshot,Prod.mk.injEq] at hsnapshot
  rcases hsnapshot with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  obtain ⟨code,rfl⟩ := onlyCode
  simp only [bind_ok]
  step as ⟨map,back,hmap,hback⟩
  step as ⟨pcword,hpcword⟩
  step as ⟨coordinate,hcoordinate⟩
  have choice : (if compiler.reachable then .ok (frame.kind,true)
      else if frame.end_reachable then .ok (frame.kind,true)
      else Aeneas.Std.bind (match frame.kind with
        | .Body | .Block | .Loop => (.ok false : Result Bool)
        | .Then => .ok true | .Else => .ok false) (fun thenLabel =>
        Aeneas.Std.bind (if thenLabel then .ok frame.entry_reachable else .ok false)
          (fun entered => .ok (frame.kind,entered)))) = .ok (frame.kind,scopeExitLive compiler.reachable frame) := by
    cases kind : frame.kind <;> cases live : compiler.reachable <;> cases ends : frame.end_reachable <;>
      simp [scopeExitLive,kind,live,ends,bind_ok]
  change WP.spec (Aeneas.Std.bind (if compiler.reachable then .ok (frame.kind,true)
      else if frame.end_reachable then .ok (frame.kind,true)
      else Aeneas.Std.bind (match frame.kind with
        | .Body | .Block | .Loop => (.ok false : Result Bool)
        | .Then => .ok true | .Else => .ok false) (fun thenLabel =>
        Aeneas.Std.bind (if thenLabel then .ok frame.entry_reachable else .ok false)
          (fun entered => .ok (frame.kind,entered)))) _) _
  rw [choice,bind_ok]
  have mapLookup : compiler.function.controls.val[frame.map.val]? = some map := by
    simp [List.getElem?_eq_getElem mapFits,hmap]
  let closed := {map with source_end := coordinate,end_pc := pcword}
  let updated := {compiler with frames := rest,reachable := scopeExitLive compiler.reachable frame,function := {compiler.function with code,controls := back closed}}
  have mapEffect : updated.function.controls.val = compiler.function.controls.val.set frame.map.val closed := by
    simp [updated,hback,alloc.vec.Vec.set_val_eq]
  have exitPc : closed.end_pc.val = target.val := by
    dsimp only [closed]
    rw [hpcword]
    scalar_tac
  have exitSource : closed.source_end.val = compiler.function.body_start.val+state.pos.val := hcoordinate
  have codeLength : code.val.length = compiler.function.code.val.length := by
    simpa only [patchCode_length] using congrArg List.length effect
  cases kind : frame.kind
  case Body =>
    change WP.spec (Aeneas.Std.bind (.ok true) _) _
    rw [bind_ok]
    simp only [ite_true]
    change WP.spec (Aeneas.Std.bind (if scopeExitLive compiler.reachable frame then .ok frame.results else .ok 0#u32) _) _
    have choose : (if scopeExitLive compiler.reachable frame then .ok frame.results else .ok 0#u32) =
        (.ok (if scopeExitLive compiler.reachable frame then frame.results else 0#u32) : Result U32) := by split <;> rfl
    rw [choose,bind_ok]
    step with compiler_emit ops law updated _ (by simpa [updated,codeLength] using codeFits)
      (by simpa [updated] using sourceFits) (by simpa [updated] using emitCoordinateFits)
      as ⟨status,emitted,hEmitted⟩
    cases status with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok unit =>
      obtain ⟨budget,instructions,sources,rfl,emittedCode,_⟩ := hEmitted rfl
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      step with compiler_observe ops law _ state as ⟨out,hout,success⟩
      obtain ⟨_,_,_,_,_,_,hcode,_,_,_,_,hframes,hcontrols⟩ := hout success
      refine ⟨hframes,?_,map,closed,mapLookup,?_,rfl,rfl,exitPc,exitSource⟩
      · rw [hcode]
        simpa only [updated,effect,List.drop_zero,closeMapEpilogue,kind,ite_true] using emittedCode
      · rw [hcontrols]
        exact mapEffect
  all_goals
    change WP.spec (Aeneas.Std.bind (.ok false) _) _
    rw [bind_ok]
    simp only [Bool.false_eq_true,ite_false]
    step with compiler_observe ops law updated state as ⟨out,hout,success⟩
    obtain ⟨_,_,_,_,_,_,hcode,_,_,_,_,hframes,hcontrols⟩ := hout success
    refine ⟨hframes,?_,map,closed,mapLookup,?_,rfl,rfl,exitPc,exitSource⟩
    · rw [hcode]
      simpa [closeMapEpilogue,kind] using effect
    · rw [hcontrols]
      exact mapEffect

end Itasca.Runtime.Code
