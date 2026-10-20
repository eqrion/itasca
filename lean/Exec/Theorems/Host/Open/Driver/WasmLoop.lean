import Exec.Interp.Host.OpenJump
import Exec.Theorems.Host.Open.Driver.ReentrantHistory
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp Exec.Interp.OpenCall

/-- An actual two-instruction Wasm loop advances through the continuing
interrupt marker and jumps back. The explicit host continuation remains pending
through every tick; this divergence occurs inside Wasm, not host control. -/
theorem wasm_loop_waiting_host {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A) (select : Selector)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (index : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
    (last : index.val+1=exec.frames.length) (hf : exec.frames.val[index.val]?=some raw)
    (hi : store.instances.val[raw.instance.val]?=some inst)
    (hc : inst.module.functions.val[raw.function.val]?=some compiled)
    (pc : raw.pc=0#u32) (head : compiled.code.val[0]?=some .LoopHead)
    (back : compiled.code.val[1]?=some (.Jump 0#u32))
    (root : runtime.FuncAddr) (results : alloc.vec.Vec runtime.Value)
    (host : HostState) (next : Nat) (tail : List Continuation) (history : List Observation) :
    let state : State M := ⟨store,.wasm exec (.Ok ()) root results,.host host next::tail,history⟩
    let advanced := {exec with frames:=exec.frames.set index {raw with pc:=1#u32}}
    let second : State M := {state with mode:=.wasm advanced (.Ok ()) root results}
    tick memory floats allocator select state=.ok (.cont second) ∧
      tick memory floats allocator select second=.ok (.cont state) ∧
      run memory floats allocator select state=.div := by
  let advanced := {exec with frames:=exec.frames.set index {raw with pc:=1#u32}}
  let state : State M := ⟨store,.wasm exec (.Ok ()) root results,.host host next::tail,history⟩
  let second : State M := {state with mode:=.wasm advanced (.Ok ()) root results}
  have valid : index.val<exec.frames.val.length := (List.getElem?_eq_some_iff.mp hf).1
  have rawAt := (List.getElem?_eq_some_iff.mp hf).2
  have restored : (advanced.frames.set index {{raw with pc:=1#u32} with pc:=0#u32})=exec.frames := by
    apply alloc.vec.Vec.ext
    simp only [advanced,alloc.vec.Vec.set_val_eq,List.set_set]
    have same : {raw with pc:=0#u32}=raw := by rw [←pc]
    rw [same,←rawAt,List.set_getElem_self valid]
  have zeroVal : (0#u32).val=0 := by scalar_tac
  have oneVal : (1#u32).val=1 := by scalar_tac
  have firstStep := prepare_loopHead_exact memory (inert memory) floats allocator exec store () index raw inst compiled 1#u32
    (by rw [pc]; scalar_tac) last hf hi hc (by rw [pc]; scalar_tac) (by simpa only [pc,zeroVal] using head) rfl
  have secondLookup : advanced.frames.val[index.val]?=some {raw with pc:=1#u32} := by
    simp [advanced,alloc.vec.Vec.set_val_eq,valid]
  have secondLast : index.val+1=advanced.frames.length := by simpa [advanced,alloc.vec.Vec.set_val_eq] using last
  have secondStep := prepare_jump_exact memory (inert memory) floats allocator advanced store () index {raw with pc:=1#u32} inst compiled 0#u32
    secondLast secondLookup hi hc (by scalar_tac) (by simpa only [oneVal] using back)
  have sameExec : {advanced with frames:=advanced.frames.set index {{raw with pc:=1#u32} with pc:=0#u32}}=exec := by
    rw [restored]
  rw [sameExec] at secondStep
  have active : exec.frames.len>0#usize := by scalar_tac
  have activeSecond : advanced.frames.len>0#usize := by
    have same : advanced.frames.length=exec.frames.length := by simp [advanced,alloc.vec.Vec.set_val_eq]
    scalar_tac
  have tickFirst : tick memory floats allocator select state=.ok (.cont second) := by
    simp [tick,state,prepareLoop,core.result.Result.is_ok,active,firstStep,acceptCall,second,advanced]
  have tickSecond : tick memory floats allocator select second=.ok (.cont state) := by
    simp [tick,second,state,prepareLoop,core.result.Result.is_ok,activeSecond,secondStep,acceptCall]
  refine ⟨tickFirst,tickSecond,?_⟩
  let states : Nat → State M := fun n=>if n%2=0 then state else second
  have stream : ∀n,tick memory floats allocator select (states n)=.ok (.cont (states (n+1))) := by
    intro n
    by_cases even : n%2=0
    · have odd : (n+1)%2≠0 := by omega
      simpa only [states,if_pos even,if_neg odd] using tickFirst
    · have evenNext : (n+1)%2=0 := by omega
      simpa only [states,if_neg even,if_pos evenNext] using tickSecond
  exact loop_diverges_of_stream (tick memory floats allocator select) states stream
end Exec.Theorems.OpenReentrantControl
