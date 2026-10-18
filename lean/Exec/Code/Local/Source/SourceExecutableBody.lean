import Exec.Code.Local.Source.SourceExecutableImmediate
namespace Exec.Code.SourceExecutable
open Aeneas Aeneas.Std Itasca

theorem token_wasm1 {token bytes} (encoded : Wasm1.TokenEncoding token bytes) : TokenWasm1 token := by
  obtain ⟨opcode, immediate, _, encoded⟩ := encoded
  exact immediate_wasm1 encoded

theorem consumed_wasm1 {data start tokens next} (encoded : Wasm1.Consumed data start tokens next) :
    Forall TokenWasm1 tokens := by
  induction encoded with
  | nil => simp [Forall]
  | snoc _ atToken ih =>
    obtain ⟨bytes, encoded, _⟩ := atToken
    simpa [Forall, or_imp, forall_and] using And.intro ih (token_wasm1 encoded)

theorem emits_wasm1 {tokens source} (emitted : Wasm1.Emits tokens source)
    (known : Forall TokenWasm1 tokens) : Forall Abs.ExecutableInstr source := by
  induction emitted with
  | nil => simp [Forall]
  | simple _ simple ih =>
    simp only [Forall, List.mem_append, List.mem_singleton, or_imp, forall_and] at known
    cases simple
    simpa [Forall, or_imp, forall_and, TokenWasm1, TokenWasm2] using And.intro (ih known.1) (known.2 _ rfl)
  | block bt _ _ ih body =>
    simp only [Forall, List.mem_append, List.mem_singleton, or_imp, forall_and] at known
    have hbody := body known.1.2
    have prior := ih known.1.1.1
    simpa [Forall, or_imp, forall_and] using And.intro prior (Abs.ExecutableInstr.block _ _ hbody)
  | loop bt _ _ ih body =>
    simp only [Forall, List.mem_append, List.mem_singleton, or_imp, forall_and] at known
    have hbody := body known.1.2
    have prior := ih known.1.1.1
    simpa [Forall, or_imp, forall_and] using And.intro prior (Abs.ExecutableInstr.loop _ _ hbody)
  | ifElse bt _ _ _ ih yes no =>
    simp only [Forall, List.mem_append, List.mem_singleton, or_imp, forall_and] at known
    have hyes := yes known.1.1.1.2
    have hno := no known.1.2
    have prior := ih known.1.1.1.1.1
    simpa [Forall, or_imp, forall_and] using And.intro prior (Abs.ExecutableInstr.ifelse _ _ _ hyes hno)
  | ifEnd bt _ _ ih body =>
    simp only [Forall, List.mem_append, List.mem_singleton, or_imp, forall_and] at known
    have hbody := body known.1.2
    have prior := ih known.1.1.1
    simpa [Forall, or_imp, forall_and] using And.intro prior
      (Abs.ExecutableInstr.ifelse _ _ [] hbody (by simp [Forall]))

theorem body_wasm1 {data source} (encoded : Wasm1.BodyEncoding data source) :
    Forall Abs.ExecutableInstr source := by
  obtain ⟨tokens, next, consumed, _, inner, rfl, emitted⟩ := encoded
  have known := consumed_wasm1 consumed
  exact emits_wasm1 emitted (fun token member => known token (List.mem_append_left _ member))

theorem token_wasm2 {token bytes} (encoded : Wasm2.TokenEncoding token bytes) : TokenWasm2 token := by
  obtain ⟨opcode, immediate, _, encoded⟩ := encoded
  exact immediate_wasm2 encoded

theorem consumed_wasm2 {data start tokens next} (encoded : Wasm2.Consumed data start tokens next) :
    Forall TokenWasm2 tokens := by
  induction encoded with
  | nil => simp [Forall]
  | snoc _ atToken ih =>
    obtain ⟨bytes, encoded, _⟩ := atToken
    simpa [Forall, or_imp, forall_and] using And.intro ih (token_wasm2 encoded)

theorem emits_wasm2 {tokens source} (emitted : Wasm2.Emits tokens source)
    (known : Forall TokenWasm2 tokens) : Forall Abs.ExecutableInstr source := by
  induction emitted with
  | nil => simp [Forall]
  | simple _ simple ih =>
    simp only [Forall, List.mem_append, List.mem_singleton, or_imp, forall_and] at known
    cases simple
    simpa [Forall, or_imp, forall_and, TokenWasm1, TokenWasm2] using And.intro (ih known.1) (known.2 _ rfl)
  | block bt _ _ ih body =>
    simp only [Forall, List.mem_append, List.mem_singleton, or_imp, forall_and] at known
    have hbody := body known.1.2
    have prior := ih known.1.1.1
    simpa [Forall, or_imp, forall_and] using And.intro prior (Abs.ExecutableInstr.block _ _ hbody)
  | loop bt _ _ ih body =>
    simp only [Forall, List.mem_append, List.mem_singleton, or_imp, forall_and] at known
    have hbody := body known.1.2
    have prior := ih known.1.1.1
    simpa [Forall, or_imp, forall_and] using And.intro prior (Abs.ExecutableInstr.loop _ _ hbody)
  | ifElse bt _ _ _ ih yes no =>
    simp only [Forall, List.mem_append, List.mem_singleton, or_imp, forall_and] at known
    have hyes := yes known.1.1.1.2
    have hno := no known.1.2
    have prior := ih known.1.1.1.1.1
    simpa [Forall, or_imp, forall_and] using And.intro prior (Abs.ExecutableInstr.ifelse _ _ _ hyes hno)
  | ifEnd bt _ _ ih body =>
    simp only [Forall, List.mem_append, List.mem_singleton, or_imp, forall_and] at known
    have hbody := body known.1.2
    have prior := ih known.1.1.1
    simpa [Forall, or_imp, forall_and] using And.intro prior
      (Abs.ExecutableInstr.ifelse _ _ [] hbody (by simp [Forall]))

theorem body_wasm2 {data source} (encoded : Wasm2.BodyEncoding data source) :
    Forall Abs.ExecutableInstr source := by
  obtain ⟨tokens, next, consumed, _, inner, rfl, emitted⟩ := encoded
  have known := consumed_wasm2 consumed
  exact emits_wasm2 emitted (fun token member => known token (List.mem_append_left _ member))
end Exec.Code.SourceExecutable
