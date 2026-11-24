import Itasca.Main

/-!
Regression check for the public runtime protocol's transitive statement vocabulary.
Run after the integrated build: `lake env lean scripts/RuntimeContract.lean`.
The walk follows definition bodies and constructors, never theorem proofs, so an
abstract predicate cannot conceal a referenced private construction certificate.
-/
open Lean

namespace RuntimeReading

private def owner (env : Environment) (declName : Name) : Name :=
  match env.getModuleIdxFor? declName with
  | some index => env.header.moduleNames[index.toNat]!
  | none => `_local

private def expanded (moduleName : Name) : Bool :=
  [ `Itasca, `SpecExt, `«wasm2.0», `ExtendedDeriveDecEq ].contains moduleName.getRoot

private partial def reading (env : Environment) (pending : List Name) (seen : NameSet) : NameSet :=
  match pending with
  | [] => seen
  | declName :: rest =>
    if seen.contains declName then reading env rest seen else
    let seen := seen.insert declName
    if !expanded (owner env declName) then reading env rest seen else
    match env.find? declName with
    | none => reading env rest seen
    | some info =>
      let children := info.type.getUsedConstants ++ (match info with
        | .defnInfo declaration => declaration.value.getUsedConstants
        | .opaqueInfo declaration => declaration.value.getUsedConstants
        | .inductInfo declaration => declaration.ctors.toArray
        | _ => #[])
      reading env (children.toList ++ rest) seen


private def report (roots : List Name) (label : String) : CoreM Unit := do
  let env ← getEnv
  let seeds := roots.flatMap fun root => match env.find? root with
    | some (.thmInfo declaration) => declaration.type.getUsedConstants.toList
    | _ => [root]
  let names := reading env seeds {}
  let forbidden := ["Itasca.Stream.Run", "Itasca.Integration.ExecutableInv", "Itasca.Integration.CertifiedApiStore",
    "Itasca.Integration.CertifiedSupportedStore", "Itasca.Integration.ModuleCodeRel",
    "Itasca.Integration.CompilationCertificate", "Itasca.Integration.CumulativeStoreMutation",
    "Itasca.Integration.InvocationRejected", "Itasca.Interp.Machine.CompiledFunctions",
    "Itasca.Compiler.FunctionCode", "Itasca.Compiler.InitializerCode", "Itasca.Compiler.SegmentProgram",
    "Itasca.Representation.Shape", "Itasca.Representation.CompiledFunctionCapacity",
    "Itasca.Store.PreparationPhase", "Itasca.Store.PreparationResourcePath",
    "Itasca.Store.PrecommitResourceEvidence", "Itasca.Store.PreparationRefusal",
    "Itasca.Store.storeParts", "Itasca.Store.typeParts", "Itasca.Store.emptyInstance",
    "Itasca.Store.TypePreparationResource", "Itasca.Store.FunctionPreparationResource",
    "Itasca.Store.TablePreparationResource", "Itasca.Store.MemoryPreparationResource",
    "Itasca.Store.GlobalPreparationResource", "Itasca.Store.ElementStagingResource",
    "Itasca.Store.DataPreparationResource", "Itasca.Store.PreparationCalls", "Itasca.Store.typeStageCall", "Itasca.Store.functionStageCall",
    "Itasca.Store.tableStageCall", "Itasca.Store.memoryStageCall", "Itasca.Store.globalStageCall",
    "Itasca.Store.elementStageCall", "Itasca.Store.dataStageCall",
    "Itasca.Store.TypeStagingCause", "Itasca.Store.FunctionStagingCause",
    "Itasca.Store.TableStagingCause", "Itasca.Store.MemoryStagingCause",
    "Itasca.Store.GlobalStagingCause", "Itasca.Store.ElementStagingCause", "Itasca.Store.DataStagingCause"]
  let sourceCompiler := ["SourceEnvironmentDemand", "SourceFunctionDemand", "SourcePreparationMaxima",
    "SourceCompilationDemand", "ValidCompilationSource", "CompileEligible", "signatureSlots",
    "sourceFunctionCode", "sourceFunctions", "sourceFunctionContext", "sourceInitializerInstructions",
    "initializerElementCost", "initializerMappingCost"].map ("Itasca.Compiler." ++ ·)
  let mut starts : Std.HashSet (Name × Nat) := {}
  let mut lines := 0
  for declName in names.toList do
    if forbidden.any (fun stem => declName.toString == stem || declName.toString.startsWith (stem ++ ".")) then
      throwError "public protocol leaked private construction vocabulary: {declName}"
    if declName.toString.startsWith "Itasca.Compiler." &&
        !(sourceCompiler.any (fun stem => declName.toString == stem || declName.toString.startsWith (stem ++ "."))) then
      throwError "public protocol leaked non-source compiler vocabulary: {declName}"
    if declName.isInternalDetail then continue
    let moduleName := owner env declName
    if moduleName.getRoot != `Itasca && moduleName.getRoot != `SpecExt then continue
    if moduleName.toString.startsWith "Itasca.Generated." then continue
    if let some range ← findDeclarationRanges? declName then
      let key := (moduleName, range.range.pos.line)
      unless starts.contains key do
        starts := starts.insert key
        lines := lines + range.range.endPos.line - range.range.pos.line + 1
  IO.println s!"{label}: {starts.size} handwritten declarations, {lines} lines"

#eval report [`Itasca.Integration.RuntimeContract] "Runtime protocol"
#eval report [`Itasca.Integration.CompilationSource] "Compilation source association"
#eval report (((include_str "public-results.txt").splitOn "\n").filter (· != "") |>.map String.toName) "All public Results"

end RuntimeReading

-- Object exhaustion requires the original quota to be reached within the
-- complete source allowance, without a phase or implementation-path premise.
example {M A : Type} (allocator : Itasca.runtime.platform.Alloc A)
    (before current : Itasca.runtime.store.Store M) (source : Itasca.metadata.Module)
    (bounds : Itasca.Store.PreparationBounds before current source)
    (cause : Itasca.Store.FunctionAllocationCause allocator current (.Exhausted .Objects)) :
    before.limits.max_objects.val ≤ Itasca.Store.objectCount before +
      (Itasca.Store.PreparationDemand.source source).objects := by
  change current.limits.max_objects.val ≤ Itasca.Store.objectCount current at cause
  rw [bounds.growth.limits] at cause
  exact cause.trans bounds.growth.objects

-- An empty source cannot manufacture an object-allocation explanation, even
-- with an arbitrary hypothetical store. Metadata reservations are separate.
example {M A : Type} (memory : Itasca.runtime.platform.MemoryBuffer M)
    (allocator : Itasca.runtime.platform.Alloc A) (current : Itasca.runtime.store.Store M)
    (source : Itasca.metadata.Module) (error : Itasca.runtime.ExecError)
    (types : source.env.types.val = []) (functions : source.env.func_type_indices.val = [])
    (tables : source.env.table_types.val = []) (memories : source.env.mem_types.val = [])
    (globals : source.env.globals.val = []) (elements : source.env.elements.val = [])
    (datas : source.tail.data.val = [])
    (cause : Itasca.Store.PreparationResourceRefusal memory allocator current source error) : False := by
  simp only [Itasca.Store.PreparationResourceRefusal, types, functions, tables, memories,
    globals, elements, datas, List.not_mem_nil, List.length_nil, lt_self_iff_false,
    false_and, and_false, or_false, exists_false] at cause
