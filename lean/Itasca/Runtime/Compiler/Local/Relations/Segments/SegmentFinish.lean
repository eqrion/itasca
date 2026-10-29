import Itasca.Runtime.Compiler.Local.Relations.Segments.SegmentData
import Itasca.Runtime.Compiler.Local.Initializer.InitializerElementLoop

/-!
Element/data initializer program prefixes, loops and finishing. SegmentProgram.change_module transports the completed segment certificate to its final module context.
-/

/-! ## Segment Element -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

theorem emit_element_program {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module : runtime.compiler.ExecutableModule)
    (budget afterBudget : runtime.compiler.Budget A)
    (before after : runtime.bytecode.CompiledFunction) (index : Usize)
    (segment : Itasca.module.Element)
    (found : module.module.env.elements.val[index.val]? = some segment)
    (valid : ∀ table offset, segment.mode = .Active table offset →
      Itasca.ModuleConstants.Valid module.module.env offset .I32)
    (success : runtime.compiler.initialize.emit_element ops module budget before index =
      .ok (.Ok (), afterBudget, after)) :
    ∃ instructions, ElementProgram after index.val segment instructions ∧
      after.code.val = before.code.val ++ instructions ∧
      after = {before with code := after.code, slot_count := after.slot_count, indirect := after.indirect} ∧
      after.indirect.val.take before.indirect.length = before.indirect.val ∧
      (instructions.length ≤ 1 ∧ after.slot_count = before.slot_count ∨
        instructions.length = 5 ∧ after.slot_count = 3#u32) := by
  unfold runtime.compiler.initialize.emit_element at success
  simp only [runtime.compiler.ExecutableModule.env,
    Itasca.module.Module.impl.env, Itasca.module.Env.impl.elements, bind_ok] at success
  rw [initializer_slice_index _ _ segment (by simpa [alloc.vec.Vec.deref] using found), bind_ok] at success
  cases mode : segment.mode with
  | Passive =>
    simp only [mode] at success
    have output := Result.ok_injective success
    have same := congrArg (fun out => out.2.2) output
    dsimp only at same
    subst after
    exact ⟨[], .passive mode, by simp, rfl, by simp, .inl ⟨by simp, rfl⟩⟩
  | Declarative =>
    simp only [mode] at success
    obtain ⟨result, boundedIndex, rest⟩ := initializer_bind_success success
    cases result with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok word =>
      have indexSpec := bounded_index index
      rw [boundedIndex, WP.spec_ok] at indexSpec
      have encoded := indexSpec word rfl
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      obtain ⟨⟨result, b1, instructions⟩, emitted, rest⟩ := initializer_bind_success rest
      have output := Result.ok_injective rest
      have resultEq := congrArg Prod.fst output
      dsimp only at resultEq
      subst result
      have fields := congrArg (fun out => out.2.2) output
      dsimp only at fields
      subst after
      have code := initializer_emit_success ops law budget b1 before.code instructions _ emitted
      exact ⟨[.ElemDrop word], .declarative mode word encoded, code, rfl, by simp, .inl ⟨by simp, rfl⟩⟩
  | Active table offset =>
    simp only [mode] at success
    obtain ⟨⟨result, b1, first⟩, constant, rest⟩ := initializer_bind_success success
    cases result with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok unitValue =>
      cases unitValue
      obtain ⟨instruction, firstFields, firstCode, firstInstruction⟩ :=
        initializer_offset_success ops law budget b1 {before with slot_count := 3#u32} first offset
          (valid_offset_shape (valid table offset mode)) constant
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      obtain ⟨⟨result, b2, second⟩, emit1, rest⟩ := initializer_bind_success rest
      cases result with
      | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
      | Ok unitValue =>
        cases unitValue
        have code1 := initializer_emit_success ops law b1 b2 first.code second _ emit1
        simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
        obtain ⟨result, boundedLen, rest⟩ := initializer_bind_success rest
        cases result with
        | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
        | Ok length =>
          have countSpec := bounded_index (alloc.vec.Vec.len segment.init)
          rw [boundedLen, WP.spec_ok] at countSpec
          have count := countSpec length rfl
          simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
          obtain ⟨⟨result, b3, third⟩, emit2, rest⟩ := initializer_bind_success rest
          cases result with
          | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
          | Ok unitValue =>
            cases unitValue
            have code2 := initializer_emit_success ops law b2 b3 second third _ emit2
            simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
            obtain ⟨result, boundedEntry, rest⟩ := initializer_bind_success rest
            cases result with
            | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
            | Ok entry =>
              have entrySpec := bounded_index (alloc.vec.Vec.len first.indirect)
              rw [boundedEntry, WP.spec_ok] at entrySpec
              have entryEncoded := entrySpec entry rfl
              simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
              obtain ⟨result, boundedIndex, rest⟩ := initializer_bind_success rest
              cases result with
              | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
              | Ok word =>
                have indexSpec := bounded_index index
                rw [boundedIndex, WP.spec_ok] at indexSpec
                have encoded := indexSpec word rfl
                simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
                obtain ⟨⟨result, b4, indirect⟩, pushed, rest⟩ := initializer_bind_success rest
                cases result with
                | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
                | Ok unitValue =>
                  cases unitValue
                  have indirectValues := (budget_push_success ops law b3 b4 first.indirect indirect (word, table) pushed).2
                  simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
                  obtain ⟨⟨result, b5, fourth⟩, emit3, rest⟩ := initializer_bind_success rest
                  cases result with
                  | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
                      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
                  | Ok unitValue =>
                    cases unitValue
                    have code3 := initializer_emit_success ops law b4 b5 third fourth _ emit3
                    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
                    obtain ⟨⟨result, b6, fifth⟩, emit4, rest⟩ := initializer_bind_success rest
                    cases result with
                    | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
                        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
                    | Ok unitValue =>
                      cases unitValue
                      have code4 := initializer_emit_success ops law b5 b6 fourth fifth _ emit4
                      have output := Result.ok_injective rest
                      have fields := congrArg (fun out => out.2.2) output
                      dsimp only at fields
                      subst after
                      refine ⟨[instruction, .Const32 1#u32 0#u32, .Const32 2#u32 length,
                        .TableInit 0#u32 entry, .ElemDrop word], ?_, ?_, ?_, ?_, ?_⟩
                      · exact .active table offset mode word length entry encoded count
                          (by simp [indirectValues, entryEncoded]) instruction (firstInstruction.change_code rfl)
                      · simp [code4, code3, code2, code1, firstCode, List.append_assoc]
                      · rw [firstFields]
                      · have same := congrArg runtime.bytecode.CompiledFunction.indirect firstFields
                        dsimp only at same
                        simp [indirectValues, same]
                      · exact .inr ⟨rfl, by rw [firstFields]⟩

end Itasca.Runtime.Code

end

/-! ## Segment Prefix -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

theorem ElementProgram.extend {before after : runtime.bytecode.CompiledFunction}
    {index segment instructions} (program : ElementProgram before index segment instructions)
    (pool : after.v128_pool = before.v128_pool)
    (indirect : after.indirect.val.take before.indirect.length = before.indirect.val) :
    ElementProgram after index segment instructions := by
  cases program with
  | passive mode => exact .passive mode
  | declarative mode word encoded => exact .declarative mode word encoded
  | active table offset mode word length entry encoded count descriptor instruction constant =>
    refine .active table offset mode word length entry encoded count ?_ instruction (constant.change_code pool)
    have bound := (List.getElem?_eq_some_iff.mp descriptor).1
    have same := congrArg (fun values => values[entry.val]?) indirect
    simp only [List.getElem?_take, bound, if_pos] at same
    exact same.trans descriptor

theorem DataProgram.extend {before after : runtime.bytecode.CompiledFunction}
    {index segment instructions} (program : DataProgram before index segment instructions)
    (pool : after.v128_pool = before.v128_pool) : DataProgram after index segment instructions := by
  cases program with
  | passive mode => exact .passive mode
  | active memory offset mode word length encoded count instruction constant =>
    exact .active memory offset mode word length encoded count instruction (constant.change_code pool)

structure ElementProgramPrefix (module : runtime.compiler.ExecutableModule)
    (seed current : runtime.bytecode.CompiledFunction) (count : Nat)
    (programs : List (List runtime.bytecode.Instr)) : Prop where
  length : programs.length = count
  entries : ∀ index, index < count → ∃ segment instructions,
    module.module.env.elements.val[index]? = some segment ∧ programs[index]? = some instructions ∧
    ElementProgram current index segment instructions
  code : current.code.val = seed.code.val ++ programs.flatten
  fields : current = {seed with code := current.code, indirect := current.indirect, slot_count := current.slot_count}
  indirect : current.indirect.val.take seed.indirect.length = seed.indirect.val
  capacity : current.slot_count = seed.slot_count ∨ current.slot_count = 3#u32
  active : ∀ instructions ∈ programs, instructions.length = 5 → current.slot_count = 3#u32

theorem ElementProgramPrefix.empty (module : runtime.compiler.ExecutableModule)
    (seed : runtime.bytecode.CompiledFunction) : ElementProgramPrefix module seed seed 0 [] := by
  constructor <;> simp

theorem element_program_append {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module : runtime.compiler.ExecutableModule)
    (seed current after : runtime.bytecode.CompiledFunction) (programs : List (List runtime.bytecode.Instr))
    (budget afterBudget : runtime.compiler.Budget A) (index : Usize)
    (prefixInv : ElementProgramPrefix module seed current index.val programs)
    (bound : index.val < module.module.env.elements.length)
    (valid : ∀ segment ∈ module.module.env.elements.val, ∀ table offset,
      segment.mode = .Active table offset → Itasca.ModuleConstants.Valid module.module.env offset .I32)
    (success : runtime.compiler.initialize.emit_element ops module budget current index =
      .ok (.Ok (), afterBudget, after)) :
    ∃ nextPrograms, ElementProgramPrefix module seed after (index.val + 1) nextPrograms := by
  let segment := module.module.env.elements.val[index.val]
  have found : module.module.env.elements.val[index.val]? = some segment := List.getElem?_eq_getElem bound
  obtain ⟨instructions, program, code, fields, indirect, capacity⟩ :=
    emit_element_program ops law module budget afterBudget current after index segment found
      (valid segment (by simp [segment]) ) success
  have pool : after.v128_pool = current.v128_pool := by
    have same := congrArg runtime.bytecode.CompiledFunction.v128_pool fields
    exact same
  refine ⟨programs ++ [instructions], ?_⟩
  constructor
  · simp [prefixInv.length]
  · intro i hi
    by_cases old : i < index.val
    · obtain ⟨oldSegment, oldInstructions, oldFound, oldProgram, oldCertificate⟩ := prefixInv.entries i old
      refine ⟨oldSegment, oldInstructions, oldFound, ?_, oldCertificate.extend pool indirect⟩
      simpa [List.getElem?_append, prefixInv.length, old] using oldProgram
    · have last : i = index.val := by omega
      subst i
      exact ⟨segment, instructions, found, by simp [prefixInv.length], program⟩
  · simp [code, prefixInv.code, List.flatten_append, List.append_assoc]
  · rw [fields, prefixInv.fields]
  · exact initializer_prefix_trans prefixInv.indirect indirect
  · rcases capacity with ⟨_, same⟩ | ⟨_, three⟩
    · simpa only [same] using prefixInv.capacity
    · exact .inr three
  · intro body member five
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with previous | rfl
    · have oldActive := prefixInv.active body previous five
      rcases capacity with ⟨_, same⟩ | ⟨_, three⟩
      · exact same.trans oldActive
      · exact three
    · rcases capacity with ⟨small, _⟩ | ⟨_, three⟩
      · omega
      · exact three

structure DataProgramPrefix (module : runtime.compiler.ExecutableModule)
    (seed current : runtime.bytecode.CompiledFunction) (count : Nat)
    (programs : List (List runtime.bytecode.Instr)) : Prop where
  length : programs.length = count
  entries : ∀ index, index < count → ∃ segment instructions,
    module.module.tail.data.val[index]? = some segment ∧ programs[index]? = some instructions ∧
    DataProgram current index segment instructions
  code : current.code.val = seed.code.val ++ programs.flatten
  fields : current = {seed with code := current.code, slot_count := current.slot_count}
  capacity : current.slot_count = seed.slot_count ∨ current.slot_count = 3#u32
  active : ∀ instructions ∈ programs, instructions.length = 5 → current.slot_count = 3#u32

theorem DataProgramPrefix.empty (module : runtime.compiler.ExecutableModule)
    (seed : runtime.bytecode.CompiledFunction) : DataProgramPrefix module seed seed 0 [] := by
  constructor <;> simp

theorem data_program_append {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module : runtime.compiler.ExecutableModule)
    (seed current after : runtime.bytecode.CompiledFunction) (programs : List (List runtime.bytecode.Instr))
    (budget afterBudget : runtime.compiler.Budget A) (index : Usize)
    (prefixInv : DataProgramPrefix module seed current index.val programs)
    (bound : index.val < module.module.tail.data.length)
    (valid : ∀ segment ∈ module.module.tail.data.val, ∀ memory offset,
      segment.mode = .Active memory offset → Itasca.ModuleConstants.Valid module.module.env offset .I32)
    (success : runtime.compiler.initialize.emit_data ops module budget current index =
      .ok (.Ok (), afterBudget, after)) :
    ∃ nextPrograms, DataProgramPrefix module seed after (index.val + 1) nextPrograms := by
  let segment := module.module.tail.data.val[index.val]
  have found : module.module.tail.data.val[index.val]? = some segment := List.getElem?_eq_getElem bound
  obtain ⟨instructions, program, code, fields, capacity⟩ :=
    emit_data_program ops law module budget afterBudget current after index segment found
      (valid segment (by simp [segment]) ) success
  have pool : after.v128_pool = current.v128_pool := by
    have same := congrArg runtime.bytecode.CompiledFunction.v128_pool fields
    exact same
  refine ⟨programs ++ [instructions], ?_⟩
  constructor
  · simp [prefixInv.length]
  · intro i hi
    by_cases old : i < index.val
    · obtain ⟨oldSegment, oldInstructions, oldFound, oldProgram, oldCertificate⟩ := prefixInv.entries i old
      refine ⟨oldSegment, oldInstructions, oldFound, ?_, oldCertificate.extend pool⟩
      simpa [List.getElem?_append, prefixInv.length, old] using oldProgram
    · have last : i = index.val := by omega
      subst i
      exact ⟨segment, instructions, found, by simp [prefixInv.length], program⟩
  · simp [code, prefixInv.code, List.flatten_append, List.append_assoc]
  · rw [fields, prefixInv.fields]
  · rcases capacity with ⟨_, same⟩ | ⟨_, three⟩
    · simpa only [same] using prefixInv.capacity
    · exact .inr three
  · intro body member five
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with previous | rfl
    · have oldActive := prefixInv.active body previous five
      rcases capacity with ⟨_, same⟩ | ⟨_, three⟩
      · exact same.trans oldActive
      · exact three
    · rcases capacity with ⟨empty, _⟩ | ⟨_, three⟩
      · simp [empty] at five
      · exact three

end Itasca.Runtime.Code

end

/-! ## Segment Loops -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Actual successful segment-emission loop establishes a complete syntactic
prefix; no loop totality or runtime correctness is a premise. -/
theorem element_program_loop {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module : runtime.compiler.ExecutableModule)
    (seed current after : runtime.bytecode.CompiledFunction)
    (budget budgetAfter : runtime.compiler.Budget A) (index : Usize)
    (programs : List (List runtime.bytecode.Instr))
    (prefixInv : ElementProgramPrefix module seed current index.val programs)
    (bound : index.val ≤ module.module.env.elements.length)
    (valid : ∀ segment ∈ module.module.env.elements.val, ∀ table offset,
      segment.mode = .Active table offset → Itasca.ModuleConstants.Valid module.module.env offset .I32)
    (success : runtime.compiler.initialize.lower_loop3 ops module budget index (.Ok ()) current =
      .ok (budgetAfter, .Ok (), after)) :
    ∃ finalPrograms, ElementProgramPrefix module seed after module.module.env.elements.length finalPrograms := by
  classical
  let measure := fun state : runtime.compiler.Budget A × Usize ×
      core.result.Result Unit Itasca.error.VisitError × runtime.bytecode.CompiledFunction =>
    if state.2.2.1 = .Ok () then module.module.env.elements.length - state.2.1.val + 1 else 0
  let inv := fun state : runtime.compiler.Budget A × Usize ×
      core.result.Result Unit Itasca.error.VisitError × runtime.bytecode.CompiledFunction =>
    state.2.2.1 = .Ok () → state.2.1.val ≤ module.module.env.elements.length ∧
      ∃ programs, ElementProgramPrefix module seed state.2.2.2 state.2.1.val programs
  let post := fun state : runtime.compiler.Budget A × core.result.Result Unit Itasca.error.VisitError ×
      runtime.bytecode.CompiledFunction =>
    state.2.1 = .Ok () → ∃ programs, ElementProgramPrefix module seed state.2.2 module.module.env.elements.length programs
  have sound : ∀ state, inv state → ∀ flow,
      runtime.compiler.initialize.lower_loop3.body ops module state.1 state.2.1 state.2.2.1 state.2.2.2 = .ok flow →
      match flow with
      | .cont next => inv next ∧ measure next < measure state
      | .done out => post out := by
    rintro ⟨b, i, status, function⟩ hinv flow body
    dsimp only [inv] at hinv
    unfold runtime.compiler.initialize.lower_loop3.body at body
    simp only [runtime.compiler.ExecutableModule.env,
      Itasca.module.Module.impl.env, Itasca.module.Env.impl.elements, bind_ok] at body
    cases status with
    | Err error =>
      simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte] at body
      split at body <;> (have hf := Result.ok_injective body; subst flow; simp [post])
    | Ok unitValue =>
      cases unitValue
      obtain ⟨hi, programs, prefixInv⟩ := hinv rfl
      simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte] at body
      split at body
      · rename_i more
        have hmore : i.val < module.module.env.elements.length := by
          simpa [alloc.vec.Vec.deref] using more
        obtain ⟨⟨result, nextBudget, nextFunction⟩, lowered, rest⟩ := initializer_bind_success body
        obtain ⟨nextIndex, added, rest⟩ := initializer_bind_success rest
        have output := Result.ok_injective rest
        subst flow
        have addSpec : i + 1#usize ⦃ next => next.val = i.val + 1 ⦄ := by
          have size := module.module.env.elements.property
          step as ⟨next, hnext⟩
          scalar_tac
        rw [added, WP.spec_ok] at addSpec
        cases result with
        | Err error => simp [inv, measure]
        | Ok unitValue =>
          cases unitValue
          obtain ⟨nextPrograms, nextPrefix⟩ := element_program_append ops law module seed function nextFunction
            programs b nextBudget i prefixInv hmore valid lowered
          refine ⟨?_, ?_⟩
          · dsimp only [inv]
            intro _
            exact ⟨by omega, nextPrograms, by simpa only [addSpec] using nextPrefix⟩
          · simp only [measure, ↓reduceIte]
            omega
      · rename_i stopped
        have stop : i.val = module.module.env.elements.length := by
          simp [alloc.vec.Vec.deref] at stopped
          simp only [alloc.vec.Vec.length] at hi ⊢
          omega
        have output := Result.ok_injective body
        subst flow
        dsimp only [post]
        intro _
        exact ⟨programs, by simpa only [stop] using prefixInv⟩
  have result := initializer_loop_success
    (fun state => runtime.compiler.initialize.lower_loop3.body ops module state.1 state.2.1 state.2.2.1 state.2.2.2)
    measure inv post (by
      intro state hstate flow hflow
      cases flow <;> exact sound state hstate _ hflow) (budget, index, .Ok (), current)
    (by exact fun _ => ⟨bound, programs, prefixInv⟩) (budgetAfter, .Ok (), after) success
  exact result rfl

/-- Actual successful segment-emission loop establishes a complete syntactic
prefix; no loop totality or runtime correctness is a premise. -/
theorem data_program_loop {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module : runtime.compiler.ExecutableModule)
    (seed current after : runtime.bytecode.CompiledFunction)
    (budget budgetAfter : runtime.compiler.Budget A) (index : Usize)
    (programs : List (List runtime.bytecode.Instr))
    (prefixInv : DataProgramPrefix module seed current index.val programs)
    (bound : index.val ≤ module.module.tail.data.length)
    (valid : ∀ segment ∈ module.module.tail.data.val, ∀ memory offset,
      segment.mode = .Active memory offset → Itasca.ModuleConstants.Valid module.module.env offset .I32)
    (success : runtime.compiler.initialize.lower_loop4 ops module budget index (.Ok ()) current =
      .ok (budgetAfter, .Ok (), after)) :
    ∃ finalPrograms, DataProgramPrefix module seed after module.module.tail.data.length finalPrograms := by
  classical
  let measure := fun state : runtime.compiler.Budget A × Usize ×
      core.result.Result Unit Itasca.error.VisitError × runtime.bytecode.CompiledFunction =>
    if state.2.2.1 = .Ok () then module.module.tail.data.length - state.2.1.val + 1 else 0
  let inv := fun state : runtime.compiler.Budget A × Usize ×
      core.result.Result Unit Itasca.error.VisitError × runtime.bytecode.CompiledFunction =>
    state.2.2.1 = .Ok () → state.2.1.val ≤ module.module.tail.data.length ∧
      ∃ programs, DataProgramPrefix module seed state.2.2.2 state.2.1.val programs
  let post := fun state : runtime.compiler.Budget A × core.result.Result Unit Itasca.error.VisitError ×
      runtime.bytecode.CompiledFunction =>
    state.2.1 = .Ok () → ∃ programs, DataProgramPrefix module seed state.2.2 module.module.tail.data.length programs
  have sound : ∀ state, inv state → ∀ flow,
      runtime.compiler.initialize.lower_loop4.body ops module state.1 state.2.1 state.2.2.1 state.2.2.2 = .ok flow →
      match flow with
      | .cont next => inv next ∧ measure next < measure state
      | .done out => post out := by
    rintro ⟨b, i, status, function⟩ hinv flow body
    dsimp only [inv] at hinv
    unfold runtime.compiler.initialize.lower_loop4.body at body
    simp only [runtime.compiler.ExecutableModule.tail,
      Itasca.module.Module.impl.tail, bind_ok] at body
    cases status with
    | Err error =>
      simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte] at body
      split at body <;> (have hf := Result.ok_injective body; subst flow; simp [post])
    | Ok unitValue =>
      cases unitValue
      obtain ⟨hi, programs, prefixInv⟩ := hinv rfl
      simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte] at body
      split at body
      · rename_i more
        have hmore : i.val < module.module.tail.data.length := by
          simpa [alloc.vec.Vec.deref] using more
        obtain ⟨⟨result, nextBudget, nextFunction⟩, lowered, rest⟩ := initializer_bind_success body
        obtain ⟨nextIndex, added, rest⟩ := initializer_bind_success rest
        have output := Result.ok_injective rest
        subst flow
        have addSpec : i + 1#usize ⦃ next => next.val = i.val + 1 ⦄ := by
          have size := module.module.tail.data.property
          step as ⟨next, hnext⟩
          scalar_tac
        rw [added, WP.spec_ok] at addSpec
        cases result with
        | Err error => simp [inv, measure]
        | Ok unitValue =>
          cases unitValue
          obtain ⟨nextPrograms, nextPrefix⟩ := data_program_append ops law module seed function nextFunction
            programs b nextBudget i prefixInv hmore valid lowered
          refine ⟨?_, ?_⟩
          · dsimp only [inv]
            intro _
            exact ⟨by omega, nextPrograms, by simpa only [addSpec] using nextPrefix⟩
          · simp only [measure, ↓reduceIte]
            omega
      · rename_i stopped
        have stop : i.val = module.module.tail.data.length := by
          simp [alloc.vec.Vec.deref] at stopped
          simp only [alloc.vec.Vec.length] at hi ⊢
          omega
        have output := Result.ok_injective body
        subst flow
        dsimp only [post]
        intro _
        exact ⟨programs, by simpa only [stop] using prefixInv⟩
  have result := initializer_loop_success
    (fun state => runtime.compiler.initialize.lower_loop4.body ops module state.1 state.2.1 state.2.2.1 state.2.2.2)
    measure inv post (by
      intro state hstate flow hflow
      cases flow <;> exact sound state hstate _ hflow) (budget, index, .Ok (), current)
    (by exact fun _ => ⟨bound, programs, prefixInv⟩) (budgetAfter, .Ok (), after) success
  exact result rfl

end Itasca.Runtime.Code

end

/-! ## Segment Finish -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

theorem segment_program_finish (module : runtime.compiler.ExecutableModule)
    (seed first second : runtime.bytecode.CompiledFunction)
    (instructions : alloc.vec.Vec runtime.bytecode.Instr)
    (elements datas : List (List runtime.bytecode.Instr))
    (elementPrefix : ElementProgramPrefix module seed first module.module.env.elements.length elements)
    (dataPrefix : DataProgramPrefix module first second module.module.tail.data.length datas)
    (appended : instructions.val = second.code.val ++ [.Return 0#u32 0#u32])
    (emptyCode : seed.code.val = []) (emptyLocals : seed.locals.val = [])
    (localSlots : seed.local_slots = 0#u32) (paramSlots : seed.param_slots = 0#u32)
    (capacity : seed.slot_count = 0#u32) :
    SegmentProgram module {second with code := instructions} := by
  have secondPool : second.v128_pool = first.v128_pool := by
    have same := congrArg runtime.bytecode.CompiledFunction.v128_pool dataPrefix.fields
    exact same
  have secondIndirect : second.indirect = first.indirect := by
    have same := congrArg runtime.bytecode.CompiledFunction.indirect dataPrefix.fields
    exact same
  have secondCapacity : second.slot_count = 0#u32 ∨ second.slot_count = 3#u32 := by
    rcases dataPrefix.capacity with same | three
    · rcases elementPrefix.capacity with original | three
      · exact .inl (same.trans (original.trans capacity))
      · exact .inr (same.trans three)
    · exact .inr three
  refine ⟨elements, datas, ?_⟩
  constructor
  · exact elementPrefix.length
  · exact dataPrefix.length
  · intro index segment found
    obtain ⟨actual, body, actualFound, bodyFound, program⟩ := elementPrefix.entries index
      (List.getElem?_eq_some_iff.mp found).1
    have same : actual = segment := Option.some.inj (actualFound.symm.trans found)
    subst actual
    exact ⟨body, bodyFound, program.extend secondPool (by simp only [secondIndirect, List.take_length])⟩
  · intro index segment found
    obtain ⟨actual, body, actualFound, bodyFound, program⟩ := dataPrefix.entries index
      (List.getElem?_eq_some_iff.mp found).1
    have same : actual = segment := Option.some.inj (actualFound.symm.trans found)
    subst actual
    exact ⟨body, bodyFound, program.extend rfl⟩
  · simp [appended, dataPrefix.code, elementPrefix.code, emptyCode, List.append_assoc]
  · exact secondCapacity
  · rintro (⟨index, body, found, five⟩ | ⟨index, body, found, five⟩)
    · have firstThree := elementPrefix.active body (List.mem_of_getElem? found) five
      rcases dataPrefix.capacity with same | three
      · exact same.trans firstThree
      · exact three
    · exact dataPrefix.active body (List.mem_of_getElem? found) five
  · have secondFields := congrArg runtime.bytecode.CompiledFunction.local_slots dataPrefix.fields
    have firstFields := congrArg runtime.bytecode.CompiledFunction.local_slots elementPrefix.fields
    exact secondFields.trans (firstFields.trans localSlots)
  · have secondFields := congrArg runtime.bytecode.CompiledFunction.param_slots dataPrefix.fields
    have firstFields := congrArg runtime.bytecode.CompiledFunction.param_slots elementPrefix.fields
    exact secondFields.trans (firstFields.trans paramSlots)
  · have secondFields := congrArg (fun f => f.locals.val) dataPrefix.fields
    have firstFields := congrArg (fun f => f.locals.val) elementPrefix.fields
    exact secondFields.trans (firstFields.trans emptyLocals)

theorem SegmentProgram.change_module {before after : runtime.compiler.ExecutableModule}
    {function} (program : SegmentProgram before function) (source : after.module = before.module) :
    SegmentProgram after function := by
  obtain ⟨elements, datas, certificate⟩ := program
  refine ⟨elements, datas, ?_⟩
  cases certificate
  constructor <;> (try simp only [source]) <;> assumption

end Itasca.Runtime.Code

end
