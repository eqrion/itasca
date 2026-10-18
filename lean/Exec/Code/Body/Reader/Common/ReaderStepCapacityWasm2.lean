import Exec.Code.Body.Reader.Common.ReaderNumericCapacity
import Exec.Code.Body.Reader.Common.ReaderSignCapacity
import Exec.Code.Body.Reader.Common.ReaderStepCapacityWasm1
import Exec.Code.Body.Reader.Control.ReaderControlCapacity
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
theorem reader_step_base_capacity_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (index : U32) (opcode : U8) (supported : SliceBaseOpcode opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 opcode before = .ok (.Ok (), out, after)) :
    CapacityStep before after out.core := by
  simp only [SliceBaseOpcode, List.mem_cons, List.not_mem_nil, or_false] at supported
  rcases supported with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have equal : opcode = 0#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    obtain ⟨_, run⟩ := profile_base_success_wasm2
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index _ before after
      (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
    exact reader_step_base_capacity_wasm1 ops law before after st.core out.core data env ctx _ (by unfold SliceBaseOpcode; decide) run
  · have equal : opcode = 1#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    obtain ⟨_, run⟩ := profile_base_success_wasm2
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index _ before after
      (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
    exact reader_step_base_capacity_wasm1 ops law before after st.core out.core data env ctx _ (by unfold SliceBaseOpcode; decide) run
  · have equal : opcode = 2#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact reader_block_capacity_wasm2 ops law before after st out data env ctx index accepted
  · have equal : opcode = 3#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact reader_loop_capacity_wasm2 ops law before after st out data env ctx index accepted
  · have equal : opcode = 4#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact reader_if_capacity_wasm2 ops law before after st out data env ctx index accepted
  · have equal : opcode = 5#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact reader_else_capacity_wasm2 ops law before after st out data env ctx index accepted
  · have equal : opcode = 11#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact reader_end_capacity_wasm2 ops law before after st out data env ctx index accepted
  · have equal : opcode = 12#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact reader_br_capacity_wasm2 ops law before after st out data env ctx index accepted
  · have equal : opcode = 13#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact reader_br_if_capacity_wasm2 ops law before after st out data env ctx index accepted
  · have equal : opcode = 15#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact reader_return_capacity_wasm2 ops law before after st out data env ctx index accepted
  · have equal : opcode = 16#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact reader_call_capacity_wasm2 ops law before after st out data env ctx index accepted
  · have equal : opcode = 26#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    obtain ⟨_, run⟩ := profile_base_success_wasm2
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index _ before after
      (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
    exact reader_step_base_capacity_wasm1 ops law before after st.core out.core data env ctx _ (by unfold SliceBaseOpcode; decide) run
  · have equal : opcode = 32#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    obtain ⟨_, run⟩ := profile_base_success_wasm2
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index _ before after
      (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
    exact reader_step_base_capacity_wasm1 ops law before after st.core out.core data env ctx _ (by unfold SliceBaseOpcode; decide) run
  · have equal : opcode = 33#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    obtain ⟨_, run⟩ := profile_base_success_wasm2
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index _ before after
      (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
    exact reader_step_base_capacity_wasm1 ops law before after st.core out.core data env ctx _ (by unfold SliceBaseOpcode; decide) run
  · have equal : opcode = 34#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    obtain ⟨_, run⟩ := profile_base_success_wasm2
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index _ before after
      (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
    exact reader_step_base_capacity_wasm1 ops law before after st.core out.core data env ctx _ (by unfold SliceBaseOpcode; decide) run
  · have equal : opcode = 65#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    obtain ⟨_, run⟩ := profile_base_success_wasm2
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index _ before after
      (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
    exact reader_step_base_capacity_wasm1 ops law before after st.core out.core data env ctx _ (by unfold SliceBaseOpcode; decide) run
  · have equal : opcode = 66#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    obtain ⟨_, run⟩ := profile_base_success_wasm2
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index _ before after
      (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
    exact reader_step_base_capacity_wasm1 ops law before after st.core out.core data env ctx _ (by unfold SliceBaseOpcode; decide) run
  · have equal : opcode = 69#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    obtain ⟨_, run⟩ := profile_base_success_wasm2
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index _ before after
      (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
    exact reader_step_base_capacity_wasm1 ops law before after st.core out.core data env ctx _ (by unfold SliceBaseOpcode; decide) run
  · have equal : opcode = 70#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    obtain ⟨_, run⟩ := profile_base_success_wasm2
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index _ before after
      (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
    exact reader_step_base_capacity_wasm1 ops law before after st.core out.core data env ctx _ (by unfold SliceBaseOpcode; decide) run
  · have equal : opcode = 73#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    obtain ⟨_, run⟩ := profile_base_success_wasm2
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index _ before after
      (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
    exact reader_step_base_capacity_wasm1 ops law before after st.core out.core data env ctx _ (by unfold SliceBaseOpcode; decide) run
  · have equal : opcode = 80#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    obtain ⟨_, run⟩ := profile_base_success_wasm2
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index _ before after
      (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
    exact reader_step_base_capacity_wasm1 ops law before after st.core out.core data env ctx _ (by unfold SliceBaseOpcode; decide) run
  · have equal : opcode = 81#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    obtain ⟨_, run⟩ := profile_base_success_wasm2
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index _ before after
      (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
    exact reader_step_base_capacity_wasm1 ops law before after st.core out.core data env ctx _ (by unfold SliceBaseOpcode; decide) run
  · have equal : opcode = 84#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    obtain ⟨_, run⟩ := profile_base_success_wasm2
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index _ before after
      (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
    exact reader_step_base_capacity_wasm1 ops law before after st.core out.core data env ctx _ (by unfold SliceBaseOpcode; decide) run
  · have equal : opcode = 106#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    obtain ⟨_, run⟩ := profile_base_success_wasm2
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index _ before after
      (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
    exact reader_step_base_capacity_wasm1 ops law before after st.core out.core data env ctx _ (by unfold SliceBaseOpcode; decide) run
  · have equal : opcode = 107#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    obtain ⟨_, run⟩ := profile_base_success_wasm2
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index _ before after
      (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
    exact reader_step_base_capacity_wasm1 ops law before after st.core out.core data env ctx _ (by unfold SliceBaseOpcode; decide) run
  · have equal : opcode = 124#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    obtain ⟨_, run⟩ := profile_base_success_wasm2
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index _ before after
      (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
    exact reader_step_base_capacity_wasm1 ops law before after st.core out.core data env ctx _ (by unfold SliceBaseOpcode; decide) run
  · have equal : opcode = 125#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    obtain ⟨_, run⟩ := profile_base_success_wasm2
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index _ before after
      (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
    exact reader_step_base_capacity_wasm1 ops law before after st.core out.core data env ctx _ (by unfold SliceBaseOpcode; decide) run
theorem reader_step_capacity_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (index : U32) (opcode : U8) (supported : SliceOpcode opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 opcode before = .ok (.Ok (), out, after)) :
    CapacityStep before after out.core := by
  rcases supported.base_or_numeric with base | ⟨operation, rfl⟩
  · exact reader_step_base_capacity_wasm2 ops law before after st out data env ctx index opcode base accepted
  · by_cases standard : (integerOpcode operation).val < 192
    · exact reader_numeric_capacity_wasm2 ops law before after st out data env ctx index operation standard accepted
    · exact reader_sign_capacity ops law before after st out data env ctx index operation (by omega) accepted
end Exec.Code
