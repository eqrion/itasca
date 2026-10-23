import Exec.Abs.ReferencePreservation
import Exec.Interp.StructuredMachine.CallLookup
import Exec.Interp.StructuredMachine.CallSemantics
import Exec.Abs.Bound
import Exec.Interp.StructuredMachine.CallPoint
import Exec.Interp.StructuredMachine.OrdinaryExecution
import Exec.Spec.Extend
import Exec.Interp.Relations.SourceCallCause
import Exec.Interp.StructuredMachine.PrepareCallStack
import Exec.Interp.StructuredMachine.CallStackEntry
import Exec.Interp.Calls.CallReturnPoint
import Exec.Interp.Relations.Capacity
import Exec.Abs.SliceSafety
import Exec.Abs.Results

namespace Exec.Interp.StructuredMachine
open Aeneas Aeneas.Std

theorem saved_source_base {M : Type} {emission : FunctionEmission} {store : runtime.store.Store M} {s : _root_.store}
    {exec raws sources waiting base} (saved : SavedFrames emission store s exec raws sources waiting base) :
    base = suspendedSourceWords sources := by
  induction saved with
  | nil => rfl
  | cons head tail ih => simp only [suspendedSourceWords,head.destination,ih,Nat.add_comm]

/-- A direct call derives its callee, signature, argument layout, defaults, and
retained caller continuation from structural compilation/store certificates.
The actual interpreter returns normally under allocation/interrupt laws; a
successful result preserves the whole typed source slice and frame stack. -/
theorem step_call_structured {M P F A : Type} {emission : FunctionEmission} {supported owned}
    (semantics : CallSemantics supported owned)
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex : Usize) (raw : runtime.interp.Frame)
    (caller : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)]
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (index : U32) (after : List instr)
    (decoded : s = Store.decodeStore view code store)
    (compiledFunctions : CompiledFunctions emission code store)
    (functionTyping : CoreFunctionsTyped view code store)
    (last : frameIndex.val + 1 = exec.frames.length)
    (hf : exec.frames.val[frameIndex.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some caller)
    (hc : caller.module.functions.val[raw.function.val]? = some compiled)
    (typed : Abs.ATyped ⟨s, ambient, { f with code := .CALL (.mk_uN index.val) :: after } :: rest, []⟩)
    (covered : supported ⟨s, ambient, { f with code := .CALL (.mk_uN index.val) :: after } :: rest, []⟩)
    (binding : FrameBinding store exec raw f)
    (slots : FrameSlots exec raw f)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint emission s raw { f with code := .CALL (.mk_uN index.val) :: after }
      compiled C targets next output)
    (relation : FrameStackRel emission store s exec ({ f with code := .CALL (.mk_uN index.val) :: after } :: rest)) :
    (∃ address function host offset, compiled.code.val[raw.pc.val]? = some (.Call index offset) ∧
      caller.funcs.val[index.val]? = some address ∧
      store.funcs.val[address.index.val]? = some function ∧ function.code = .Host host) ∨
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ (out.1 = .Ok () →
        ∃ pc frames, (out.2.1.frames.val.getLast?).map (fun frame => frame.pc) = some pc ∧
          FrameStackRel emission store s out.2.1 frames ∧
          Abs.ATyped ⟨s, ambient, frames, []⟩ ∧
          supported ⟨s, ambient, frames, []⟩ ∧
          ConcreteSim compiled.code.length raw.pc.val pc.val false false
            ⟨s, ambient, { f with code := .CALL (.mk_uN index.val) :: after } :: rest, []⟩
            ⟨s, ambient, frames, []⟩ ∧
          ReadyState emission store out.2.1 ⟨s, ambient, frames, []⟩ ∧
          (∀ expected, Abs.InvocationResult expected
              ⟨s, ambient, { f with code := .CALL (.mk_uN index.val) :: after } :: rest, []⟩ →
            Abs.InvocationResult expected ⟨s, ambient, frames, []⟩) ∧
          (∀ bounds, owned bounds ⟨s,ambient,{f with code := .CALL (.mk_uN index.val)::after}::rest,[]⟩ →
            owned bounds ⟨s,ambient,frames,[]⟩) ∧
          (∀ bound, Abs.CodeBound bound ⟨s,ambient,{f with code := .CALL (.mk_uN index.val)::after}::rest,[]⟩ →
            Abs.CodeBound bound ⟨s,ambient,frames,[]⟩)) ∧
      (∀ error, out.1 = .Err error →
        SourceDirectCallCause allocator hooks exec store platform frameIndex raw caller compiled
          ⟨s, ambient, { f with code := .CALL (.mk_uN index.val) :: after } :: rest, []⟩ error) ⦄ := by
  have current := point.code.current
  rw [point.locals] at current
  rcases codeRel_call_values index f.locals f.vals current with skip | actual
  · obtain ⟨target, forward, fetched, continuation⟩ := skip
    have targetPoint : FramePoint emission s { raw with pc := target }
        { f with code := .CALL (.mk_uN index.val) :: after } compiled C targets next output :=
      ⟨point.bindings,point.locals,point.labels, by simpa only [point.locals] using continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩
    apply Or.inr
    apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform
      frameIndex raw caller compiled target last hf hi hc (program.fetched_bound _ fetched) fetched)
    intro out result
    obtain ⟨success, exactState, sameStore, samePlatform⟩ := result
    refine ⟨sameStore, (fun _ => ⟨target, { f with code := .CALL (.mk_uN index.val) :: after } :: rest,
      ?_, ?_, typed, covered, ?_, ?_, (fun _ invariant => invariant), (fun _ invariant => invariant), (fun _ invariant => invariant)⟩), ?_⟩
    · rw [exactState, frames_set_last exec frameIndex _ last]
      simp
    · rw [exactState]
      exact FrameStackRel.ordinary relation (.refl store) (Exec.Spec.extend_store_refl _ typed.store)
        raw frameIndex target last hf binding program (.ready targetPoint) slots ⟨rfl,rfl,rfl,rfl⟩ rfl (.refl _ _)
    · exact Or.inl ⟨rfl, dispatchMeasure_forward _ _ _ _ forward continuation.entry_bound⟩
    · refine ⟨{ raw with pc := target }, compiled, C, targets, next, output, ?_,
        ⟨program.lookup, program.checked, program.fetchBound, program.localSlots, program.epilogue⟩, targetPoint⟩
      rw [exactState, frames_set_last exec frameIndex _ last]
      simp
    · intro error rejected
      rw [success] at rejected
      cases rejected
  · obtain ⟨front, args, params, results, offset, split, argumentTypes, signatureAt,
      argumentOffset, fetched, continuation⟩ := actual
    obtain ⟨address, function, signature, addressAt, owned, functionAt, signatureAtStore, signatureEq⟩ :=
      program.resolve_call caller hi index.val ⟨.mk_list params, .mk_list results⟩ signatureAt
    cases defined : function.code with
    | Host host => exact Or.inl ⟨address,function,host,offset,fetched,addressAt,functionAt,defined⟩
    | Wasm instanceIndex functionIndex =>
      apply Or.inr
      obtain ⟨inst, calleeCode, actualSignature, declared, body, epilogue,
        instanceAt, calleeAt, actualSignatureAt, table, certificate, calleeBindings, sourceAt⟩ :=
        compiledFunctions.defined view functionTyping address function instanceIndex functionIndex functionAt defined
      have sameSignature : actualSignature = signature := Option.some.inj (actualSignatureAt.symm.trans signatureAtStore)
      subst actualSignature
      have signatureTypes : signature.params.val.map sourceType = params ∧ signature.results.val.map sourceType = results := by
        simpa only [Store.decodeFuncType, functype.mk_functype.injEq, list.mk_list.injEq] using signatureEq
      have argumentTypes' : args.map Code.valueType = signature.params.val.map sourceType := argumentTypes.trans signatureTypes.1.symm
      obtain ⟨defaults, default, defaultTyped⟩ := Abs.defaultLocals_typed typed.store declared (declared_types_not_bottom certificate)
      have resolve := binding.resolve_call caller hi index.val address addressAt
      have sourceAt' : s.FUNCS[address.index.val]? = some
          ⟨Store.decodeFuncType signature, Store.decodeInstance store inst,
            .FUNC (.mk_uN calleeCode.type_index.val) (declared.map local.LOCAL) body⟩ := by rw [decoded]; exact sourceAt
      have nextStep := call_next s ambient f rest after index.val address.index.val (Store.decodeInstance store inst)
        (signature.params.val.map sourceType) (signature.results.val.map sourceType) declared
        (.mk_uN calleeCode.type_index.val) body front args defaults resolve sourceAt' argumentTypes' default
      have actualStep : Abs.astep ⟨s, ambient, { f with code := .CALL (.mk_uN index.val) :: after } :: rest, []⟩ =
          .next ⟨s, ambient,
            callCallee address.index.val (Store.decodeInstance store inst) (signature.results.val.map sourceType)
              args defaults body :: { f with code := after, vals := front } :: rest, []⟩ := by
        simpa only [← split] using nextStep
      have nextTyped := Abs.instruction_preservation s ambient f rest (.CALL (.mk_uN index.val)) after _ (.call _) typed actualStep
      have nextCovered := semantics.covered s ambient f rest index.val after _ covered actualStep
      have simulation := Abs.instruction_simulation s ambient f rest (.CALL (.mk_uN index.val)) after _ (.call _) typed actualStep
      have heights : ∀ label ∈ f.labels, label.height ≤ front.length := by
        exact nextTyped.heights { f with code := after, vals := front } (by simp)
      have capacity := slots.capacity binding
      have baseFits : raw.base.val + offset.val ≤ Usize.max := by
        have prefixBound : Code.slots ((f.locals ++ front).map Code.valueType) ≤
            Code.slots ((f.locals ++ f.vals).map Code.valueType) := by
          simp only [split, List.map_append, Code.slots_append]
          omega
        scalar_tac
      have encodedBound : raw.base.val + offset.val < 2 ^ UScalarTy.Usize.numBits := by scalar_tac
      let calleeBase : Usize := UScalar.ofNatCore (raw.base.val + offset.val) encodedBound
      have baseOffset : calleeBase.val = raw.base.val + offset.val := UScalar.ofNatCore_val_eq encodedBound
      have arguments : ValuesAt exec.slots.val calleeBase.val args := by
        have words : WordsAt exec.slots.val raw.base.val
            (Code.encodeValues (f.locals ++ front) ++ Code.encodeValues args) := by
          simpa only [FrameSlots, ValuesAt, split, Code.encodeValues_append, List.append_assoc] using slots
        simpa only [ValuesAt, Code.encodeValues_length, baseOffset, argumentOffset] using words.append_right
      have identity : exec.store = store.id := by
        obtain ⟨_, _, _, _, identity, _⟩ := binding
        exact identity
      apply step_direct_call memory hooks floats allocator exec store platform frameIndex raw caller compiled
        index offset address calleeBase last hf hi hc fetched (program.fetched_bound _ fetched) addressAt baseOffset
      intro pc hpc
      have tail : Code.StructuredCodeWithTables (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS compiled.code.val compiled.jump_tables.val targets
          (front.map Code.valueType ++ signature.results.val.map sourceType) after pc.val next output := by
        simpa only [hpc, signatureTypes.2,point.locals] using continuation
      obtain ⟨raws, frames, saved⟩ := relation.prepare_call raw frameIndex pc last hf binding slots program point
        front args after (signature.results.val.map sourceType) calleeBase.val split
        (by rw [baseOffset, argumentOffset]) heights tail
      obtain ⟨out, returned, result⟩ := WP.spec_imp_exists (call_wasm_stack memory hooks floats allocator allocation interrupts
        { exec with frames := exec.frames.set frameIndex { raw with pc := pc } } store platform address calleeBase
        function signature instanceIndex functionIndex inst calleeCode epilogue s (Code.moduleFunctionContext inst.module (signature.params.val.map sourceType++declared) (signature.results.val.map sourceType))
        (by simpa only [decoded] using calleeBindings) declared body args defaults
        certificate functionAt signatureAtStore defined instanceAt calleeAt table identity arguments argumentTypes' default raws
        ({ f with code := after, vals := front } :: rest) frames saved)
      have causes := call_wasm_causes memory hooks floats allocator allocation interrupts
        { exec with frames := exec.frames.set frameIndex { raw with pc := pc } } store platform address calleeBase
        function instanceIndex functionIndex inst calleeCode functionAt defined instanceAt calleeAt
        (by rw [certificate.2.parameterSlots, certificate.2.localSlots, Code.slots_append]; omega)
        certificate.2.capacity
      rw [returned] at causes
      simp only [WP.spec_ok] at causes
      rw [returned]
      apply WP.spec.ret
      refine ⟨result.1, ?_, ?_⟩
      · intro success
        obtain ⟨stack, top, ready⟩ := result.2 success
        refine ⟨0#u32, _, ?_, stack, nextTyped, nextCovered, ?_, ready, ?_, ?_, ?_⟩
        · simp only [top, Option.map_some]
        · exact ConcreteSim.of_source compiled.code.length raw.pc.val (0#u32).val false false simulation
        · intro expected invariant
          exact Abs.instruction_result _ _ _ _ _ _ _ expected (.call _) typed invariant actualStep
        · exact semantics.ownership s ambient f rest index.val after _ actualStep
        · intro bound bounded
          exact Abs.instruction_bound bound s ambient f rest (.CALL (.mk_uN index.val)) after _ (.call _) bounded actualStep
      · intro error rejected
        refine ⟨index, offset, pc, address, calleeBase, function, instanceIndex, functionIndex,
          inst, calleeCode, fetched, addressAt, functionAt, defined, instanceAt, calleeAt,
          baseOffset, hpc, causes error rejected, ?_⟩
        refine ⟨f, rest, index.val, after, front, args, _,
          signature.params.val.map sourceType, signature.results.val.map sourceType, 0, ?_,
          resolve, sourceAt', rfl, argumentTypes', ?_⟩
        · simpa only [← split] using (Spec.StepsHN.refl typed.decode_wf)
        · simpa only [suspendedSourceWords, Nat.add_comm] using saved_source_base saved

end Exec.Interp.StructuredMachine
