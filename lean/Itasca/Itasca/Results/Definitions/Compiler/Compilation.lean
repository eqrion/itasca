import Aeneas
import ItascaRust.Funs
import ItascaRust.Types
import Itasca.Results.Definitions.Binary
import Itasca.Results.Definitions.Compiler.Source
import Itasca.Results.Definitions.Platform
import Itasca.Results.Definitions.Streaming
import Itasca.Results.Definitions.Validation
import WebAssembly

/-!
# Whole-module compilation guarantees

Compilation associates accepted bytes with a typed source module and matching
public metadata. Eligibility states independent source-size resource bounds.
The runtime protocol connects actual acceptance to instantiation and execution;
this compilation unit stays independent of the extracted interpreter.

-/

section CompilationEligibility

/-!
## Compiler completeness premises

`ValidCompilationSource` and `CompileEligible` separate independent module validity from
the conservative source-only resource envelope needed for successful compilation.
-/

namespace Itasca.Compiler

open Aeneas Aeneas.Std Itasca

/-- Independent module validity, including intrinsic binary
and signature limits. No compiler run or emitted object occurs in these fields. -/
structure ValidCompilationSource (bytes : Slice U8)
    (raw : Binary.Module) : Prop where
  encoding : Binary.ModuleEncodingWithinLimits raw bytes.val
  signatures : Binary.ModuleSignaturesWithinLimits raw
  elaborated : Module.Elaboration.Elaborates raw (Module.Elaboration.moduleOf raw)
  typed : Module_ok (Module.Elaboration.moduleOf raw)
  restrictions : Module.Elaboration.Restrictions raw

/-- Conservative compilation requirements, expressed as source counts. The first
seven fields correspond to the configurable compiler limits. `allocation` bounds
individual reservations; `frameWords` is the intrinsic 32-bit frame-size bound. -/
structure CompilationBudget where
  moduleBytes : Nat
  functions : Nat
  types : Nat
  instructions : Nat
  branches : Nat
  controls : Nat
  locals : Nat
  allocation : Nat
  frameWords : Nat

/-- Compute the existing conservative estimates directly from the source.
`body` is capped module byte length; `locals` allows the largest parameter list
plus the supported declared-local cap; operands allow 500 values per body byte.
Initializers retain the existing element/global/data charges. An empty function
section has zero body/local/operand demand. Allocation is the maximum of the
source-table, preparation, initializer, and fixed small reservation allowances. -/
def compilationBudget (byteCount : Nat) (raw : Binary.Module) : CompilationBudget :=
  let functions := raw.functions.length
  let body := if functions = 0 then 0 else Nat.min byteCount Itasca.limits.MAX_FUNCTION_BYTES.val
  let parameters := (raw.types.map (fun signature => signature.params.val.length)).foldr max 0
  let locals := if functions = 0 then 0 else parameters + Itasca.limits.MAX_LOCALS.val
  let operands := 500 * body
  let mappings := 2 * raw.globals.length + (raw.elements.map (fun e => e.init.length + 3)).sum + 2 * raw.data.length
  let segments := 5 * (raw.elements.length + raw.data.length) + 1
  { moduleBytes := byteCount, functions, types := raw.types.length
    instructions := functions * (3 * body) + 2 * mappings + segments
    branches := functions * body, controls := functions * (1 + body)
    locals := functions * locals, frameWords := 2 * locals + 2 * operands
    allocation := max 4 (max raw.types.length (max (raw.imports.length + functions)
      (max (3 * body + 3) (max locals (max operands (max (functions + mappings + 1) segments)))))) }

/-- The configured limits cover the computed budget, and its intrinsic frame
and reservation sizes are representable. No compiler state or metadata witness
is quantified over. -/
structure CompilationBudget.Fits (budget : CompilationBudget)
    (limits : runtime.compiler.CompileLimits) : Prop where
  moduleBytes : budget.moduleBytes ≤ limits.max_module_bytes.val
  functions : budget.functions ≤ limits.max_functions.val
  types : budget.types ≤ limits.max_types.val
  instructions : budget.instructions ≤ limits.max_instructions.val
  branches : budget.branches ≤ limits.max_branch_table_entries.val
  controls : budget.controls ≤ limits.max_controls.val
  locals : budget.locals ≤ limits.max_locals.val
  frameWords : budget.frameWords ≤ U32.max
  allocation : budget.allocation ≤ Usize.max

/-- Source validity is separate; eligibility only compares the deterministic
source budget with configured and intrinsic limits. -/
def CompileEligible (bytes : Slice U8) (raw : Binary.Module)
    (limits : runtime.compiler.CompileLimits) : Prop :=
  (compilationBudget bytes.length raw).Fits limits

end Itasca.Compiler

end CompilationEligibility

/-! ## Compilation -/

namespace Itasca.Integration
open Aeneas Aeneas.Std Itasca

/-- Accepted bytes and public metadata describe one well-typed source module.
Execution of the compiled artifact is specified by instantiation and invocation
in RuntimeContract; bytecode layout is not part of this source association. -/
def CompilationSource (bytes : Slice U8) (executable : runtime.compiler.ExecutableModule) : Prop :=
  ∃ raw, Binary.ModuleEncodingWith CodeEntry.CodeEncoding raw bytes.val ∧
    Module.Elaboration.Elaborates raw (Module.Elaboration.moduleOf raw) ∧
    Module_ok (Module.Elaboration.moduleOf raw) ∧ Module.Elaboration.Restrictions raw ∧
    Module.Elaboration.Matches executable.module.env executable.module.tail raw ∧
    Module.Elaboration.AccessorTypes executable.module.env raw

end Itasca.Integration
