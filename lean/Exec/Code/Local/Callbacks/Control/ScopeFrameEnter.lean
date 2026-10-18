import Exec.Code.Local.Callbacks.Control.ScopeFramePatch
namespace Exec.Code
open Aeneas Aeneas.Std

def SourceScope.enterBlock (bt : blocktype) (front params results : List valtype)
    (entry : Nat) (entered : Bool) : SourceScope :=
  ⟨.block bt, front, params, results, [], entry, entry, entered⟩

def SourceScope.enterLoop (bt : blocktype) (front params results : List valtype)
    (entry : Nat) (entered : Bool) : SourceScope :=
  ⟨.loop bt, front, params, results, [], entry, entry + (if entered then 1 else 0), entered⟩

def SourceScope.enterIf (bt : blocktype) (condition : U32) (front params results : List valtype)
    (entry : Nat) (entered : Bool) : SourceScope :=
  ⟨.then_ bt condition, front, params, results, [], entry, entry + (if entered then 1 else 0), entered⟩

/-- The exact freshly pushed BLOCK frame matches its new source scope. -/
theorem FrameScope.enter_block {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (locals front params results : List valtype) (bt : blocktype) (map : Usize)
    (height paramWidth resultWidth pc : U32) (entered : Bool)
    (paramsEq : paramWidth.val = slots params) (resultsEq : resultWidth.val = slots results)
    (heightEq : entered = true → height.val = slots locals + slots front)
    (mapBound : map.val < compiler.function.controls.val.length)
    (position : pc.val ≤ compiler.function.code.val.length) :
    FrameScope locals compiler (SourceScope.enterBlock bt front params results pc.val entered)
      ⟨map, .Block, height, paramWidth, resultWidth, pc, none, entered, false, alloc.vec.Vec.new Usize⟩ := by
  constructor
  · constructor <;> simp_all [SourceScope.enterBlock, ScopeForm.kind, SourceScope.frameStart,
      SourceScope.bodyStart, SourceScope.guardPosition]
  · exact mapBound
  · exact position
  · exact position
  · trivial

/-- A freshly pushed LOOP retains its hook only when source entry was live. -/
theorem FrameScope.enter_loop {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (locals front params results : List valtype) (bt : blocktype) (map : Usize)
    (height paramWidth resultWidth pc : U32) (entered : Bool)
    (paramsEq : paramWidth.val = slots params) (resultsEq : resultWidth.val = slots results)
    (heightEq : entered = true → height.val = slots locals + slots front)
    (mapBound : map.val < compiler.function.controls.val.length)
    (position : pc.val + (if entered then 1 else 0) ≤ compiler.function.code.val.length)
    (hook : entered = true → compiler.function.code.val[pc.val]? = some .LoopHead) :
    FrameScope locals compiler (SourceScope.enterLoop bt front params results pc.val entered)
      ⟨map, .Loop, height, paramWidth, resultWidth, pc, none, entered, false, alloc.vec.Vec.new Usize⟩ := by
  constructor
  · constructor <;> simp_all [SourceScope.enterLoop, ScopeForm.kind, SourceScope.frameStart,
      SourceScope.bodyStart, SourceScope.guardPosition, alloc.vec.Vec.new]
  · exact mapBound
  · change pc.val ≤ compiler.function.code.val.length
    omega
  · exact position
  · exact hook

/-- An entered IF owns a fresh guard immediately before its frame's start PC. -/
theorem FrameScope.enter_if {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (locals front params results : List valtype) (bt : blocktype) (condition : U32) (map entry : Usize)
    (height paramWidth resultWidth pc : U32) (entered : Bool)
    (paramsEq : paramWidth.val = slots params) (resultsEq : resultWidth.val = slots results)
    (heightEq : entered = true → height.val = slots locals + slots front)
    (mapBound : map.val < compiler.function.controls.val.length)
    (start : pc.val = entry.val + (if entered then 1 else 0))
    (position : pc.val ≤ compiler.function.code.val.length)
    (guard : entered = true → compiler.function.code.val[entry.val]? = some (.JumpIfZero condition core.num.U32.MAX)) :
    FrameScope locals compiler (SourceScope.enterIf bt condition front params results entry.val entered)
      ⟨map, .Then, height, paramWidth, resultWidth, pc, (if entered then some entry else none),
        entered, false, alloc.vec.Vec.new Usize⟩ := by
  constructor
  · constructor <;> simp_all [SourceScope.enterIf, ScopeForm.kind, SourceScope.frameStart,
      SourceScope.bodyStart, SourceScope.guardPosition]
  · exact mapBound
  · change entry.val ≤ compiler.function.code.val.length
    omega
  · change entry.val + (if entered then 1 else 0) ≤ compiler.function.code.val.length
    omega
  · exact guard
end Exec.Code
