import Itasca.Runtime.Code.Local.Relations.Table.BranchTableLayout
namespace Itasca.Runtime.Code
open Aeneas.Std
/-- Structured compiler evidence parameterized only by its syntactic emitted-head relation. -/
inductive StructuredCode (emission : List valtype → instr → List Bytecode → List valtype → Prop)
    (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) : List U32 → List LabelTarget → List valtype → List instr → Nat → Nat → List valtype → Prop where
  | nil (labels stack pc) (bound : pc ≤ code.length) (live : NormalLive labels) :
      StructuredCode emission types functions returns locals code jumpTables labels stack [] pc pc stack
  | linear {labels before middle after instruction source emitted pc tail next}
      (head : emission before instruction emitted middle)
      (ordinary : ∀ depths fallback, instruction ≠ .BR_TABLE depths fallback)
      (fragment : Segment code pc emitted tail)
      (rest : StructuredCode emission types functions returns locals code jumpTables labels middle source tail next after) :
      StructuredCode emission types functions returns locals code jumpTables labels before (instruction :: source) pc next after
  | skip {labels stack source pc target next final}
      (forward : pc < target.val)
      (instruction : code[pc]? = some (.Jump target))
      (rest : StructuredCode emission types functions returns locals code jumpTables labels stack source target.val next final) :
      StructuredCode emission types functions returns locals code jumpTables labels stack source pc next final
  | block {labels front params results after body bt pc normalExit branchExit next final normalLive branchLive}
      (signature : BlockSignature types bt params results)
      (bodyCode : StructuredCode emission types functions returns locals code jumpTables
        (⟨front, results, results, branchExit, normalExit, [], after, normalLive, branchLive⟩ :: labels)
        (front ++ params) body pc normalExit (front ++ results))
      (rest : normalLive = true → StructuredCode emission types functions returns locals code jumpTables labels (front ++ results) after normalExit next final)
      (targetRest : branchLive = true → StructuredCode emission types functions returns locals code jumpTables labels (front ++ results) after branchExit.val next final)
      (bounds : pc ≤ next ∧ next ≤ code.length) :
      StructuredCode emission types functions returns locals code jumpTables labels (front ++ params) (.BLOCK bt body :: after) pc next final
  | loop {labels front params results after body bt entry exit next final normalLive}
      (signature : BlockSignature types bt params results)
      (head : code[entry.val]? = some .LoopHead)
      (bodyCode : StructuredCode emission types functions returns locals code jumpTables
        (⟨front, params, results, entry, exit, [.LOOP bt body], after, normalLive, true⟩ :: labels)
        (front ++ params) body (entry.val + 1) exit (front ++ results))
      (rest : normalLive = true → StructuredCode emission types functions returns locals code jumpTables labels (front ++ results) after exit next final)
      (bounds : entry.val ≤ next ∧ next ≤ code.length) :
      StructuredCode emission types functions returns locals code jumpTables labels (front ++ params) (.LOOP bt body :: after) entry.val next final
  | ifElse {labels front params results after yes no bt pc yesExit noEntry exit next final cond yesNormal yesBranch noNormal noBranch}
      (signature : BlockSignature types bt params results)
      (condition : cond.val = slots locals + slots (front ++ params))
      (guard : code[pc]? = some (.JumpIfZero cond noEntry))
      (yesCode : StructuredCode emission types functions returns locals code jumpTables
        (⟨front, results, results, exit, yesExit, [], after, yesNormal, yesBranch⟩ :: labels)
        (front ++ params) yes (pc + 1) yesExit (front ++ results))
      (skip : IfSkip code yesExit noEntry exit yesNormal)
      (noCode : StructuredCode emission types functions returns locals code jumpTables
        (⟨front, results, results, exit, exit.val, [], after, noNormal, noBranch⟩ :: labels)
        (front ++ params) no noEntry.val exit.val (front ++ results))
      (rest : yesNormal = true ∨ yesBranch = true ∨ noNormal = true ∨ noBranch = true →
        StructuredCode emission types functions returns locals code jumpTables labels (front ++ results) after exit.val next final)
      (bounds : pc + 1 ≤ next ∧ noEntry.val ≤ next ∧ next ≤ code.length) :
      StructuredCode emission types functions returns locals code jumpTables labels (front ++ params ++ [.I32])
        (.IFELSE bt yes no :: after) pc next final
  | branch {labels stack after depth label dst src count pc fragmentEnd next final}
      (lookup : labels[depth]? = some label)
      (live : label.branchLive = true)
      (layout : BranchLayout locals stack label dst src count)
      (fragment : Segment code pc (branchInstructions dst src count label.target) fragmentEnd)
      (remaining : fragmentEnd ≤ next) (scope : next ≤ code.length) :
      StructuredCode emission types functions returns locals code jumpTables labels stack (.BR (.mk_uN depth) :: after) pc next final
  | branchIf {labels stack after depth label dst src count cond resume pc next final}
      (lookup : labels[depth]? = some label)
      (live : label.branchLive = true)
      (layout : BranchLayout locals stack label dst src count)
      (condition : cond.val = slots locals + slots stack)
      (fragment : Segment code pc (branchIfInstructions dst src count label.target cond resume) resume.val)
      (rest : StructuredCode emission types functions returns locals code jumpTables labels stack after resume.val next final) :
      StructuredCode emission types functions returns locals code jumpTables labels (stack ++ [.I32])
        (.BR_IF (.mk_uN depth) :: after) pc next final
  | call {labels front params results after index base pc next final}
      (signature : functions[index.val]? = some ⟨.mk_list params, .mk_list results⟩)
      (arguments : base.val = slots locals + slots front)
      (instruction : code[pc]? = some (.Call index base))
      (rest : StructuredCode emission types functions returns locals code jumpTables labels (front ++ results) after (pc + 1) next final) :
      StructuredCode emission types functions returns locals code jumpTables labels (front ++ params) (.CALL (.mk_uN index.val) :: after) pc next final
  | unreachable {labels stack after pc next final}
      (instruction : code[pc]? = some .Unreachable)
      (remaining : pc + 1 ≤ next) (scope : next ≤ code.length) :
      StructuredCode emission types functions returns locals code jumpTables labels stack (.UNREACHABLE :: after) pc next final
  | return_ {labels front after src count pc next final}
      (source : src.val = slots locals + slots front)
      (size : count.val = slots returns)
      (instruction : code[pc]? = some (.Return src count))
      (remaining : pc + 1 ≤ next) (scope : next ≤ code.length) :
      StructuredCode emission types functions returns locals code jumpTables labels (front ++ returns) (.RETURN :: after) pc next final

  | branchTable {first rest labels stack after depths fallback pc next final selector start len}
      (gate : emission (stack ++ [.I32]) (.BR_TABLE depths fallback) [.JumpTable selector start len] stack)
      (table : BranchTableLayout (first :: rest) locals labels stack code depths fallback pc next selector start len)
      (bounds : pc + 1 ≤ next ∧ next ≤ code.length) :
      StructuredCode emission types functions returns locals code (first :: rest) labels
        (stack ++ [.I32]) (.BR_TABLE depths fallback :: after) pc next final

theorem StructuredCode.map_emission {first second types functions returns locals code jumpTables labels stack source pc next final}
    (relation : StructuredCode first types functions returns locals code jumpTables labels stack source pc next final)
    (map : ∀ before instruction emitted after, first before instruction emitted after → second before instruction emitted after) :
    StructuredCode second types functions returns locals code jumpTables labels stack source pc next final := by
  induction relation using StructuredCode.rec with
  | nil labels stack pc bound live => exact .nil labels stack pc bound live
  | linear head ordinary fragment rest ih => exact .linear (map _ _ _ _ head) ordinary fragment ih
  | skip forward fetched rest ih => exact .skip forward fetched ih
  | block signature bodyCode rest targetRest bounds bodyIH restIH targetIH =>
    exact .block signature bodyIH restIH targetIH bounds
  | loop signature head bodyCode rest bounds bodyIH restIH =>
    exact .loop signature head bodyIH restIH bounds
  | ifElse signature condition guard yesCode skip noCode rest bounds yesIH noIH restIH =>
    exact .ifElse signature condition guard yesIH skip noIH restIH bounds
  | branch lookup live layout fragment remaining scope =>
    exact .branch lookup live layout fragment remaining scope
  | branchIf lookup live layout condition fragment rest ih =>
    exact .branchIf lookup live layout condition fragment ih
  | call signature arguments fetched rest ih => exact .call signature arguments fetched ih
  | unreachable fetched remaining scope => exact .unreachable fetched remaining scope
  | return_ source size fetched remaining scope => exact .return_ source size fetched remaining scope
  | branchTable gate table bounds => exact .branchTable (map _ _ _ _ gate) table bounds

end Itasca.Runtime.Code
