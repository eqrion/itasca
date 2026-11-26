# Semantic namespaces

Namespaces identify semantic subjects. Module paths identify dependency owners.
The two should agree on the subject, but organizational directories such as
`Results/Definitions`, `Results`, `Runtime`, `Support` and compiler proof stages
do not become extra namespace prefixes. Definitions and their construction proofs
extend the same subject namespace from different modules.

The nineteen public-definition reading units group definitions by guarantee and shared semantic subject.
Their named sections retain the original semantic namespaces: for example,
`Definitions/Validation.lean` collects Body, CodeEntry and Module vocabulary, while
`Definitions/Runtime.lean` collects the runtime capability contracts. A reading-unit name
is organizational and does not rename those subjects. Compiler stage ownership
remains explicit in `Definitions/Compiler/{Source,Compilation}.lean`; Local, Body and Module are implementation proof stages.

## Subject map

| Subject | Namespace | Principal owners |
| --- | --- | --- |
| Independent module grammar | `Itasca.Binary` | Results/Definitions/Binary and Binary |
| Byte/LEB and bit encodings | `Itasca.Binary.Leb128`, `SignedLeb*`, `FloatBits` | Results/Definitions/Binary and Binary |
| Generated/source translation | `Itasca.Translation`, `.Environment` | Results/Definitions/Foundations and Support/Translation |
| Source judgments and restrictions | `Itasca.Spec`, `.DeclaredReferences`, `.Restrictions`, `.Constants`, `.Completeness` | Results/Definitions/Binary and SourceMachine, Spec and Runtime/Spec |
| Body grammar, state and instruction families | `Itasca.Body`, `.Scalar`, `.Control`, `.Numeric`, `.MemoryMeaning`, `.BrTable`, `.Stack` | Binary, Handler, Results/Definitions/Validation and Body |
| Function entry typing/framing | `Itasca.CodeEntry`, `.Locals` | Results/Definitions/Validation and CodeEntry |
| Whole-module certificates and construction | `Itasca.Module.Environment`, `.Elaboration`, `.Code`, `.Sections`, `.Sound`, and other named module subjects | Results/Definitions/Validation and Module |
| Streaming and issued workers | `Itasca.Stream.Source`, `.Batch`, `.Scheduler`, `.Submission`, `.Retirement`, `.Framing`, `.CompleteRegions`, `.Run`, `.Sync`, `.Split` | Results/Definitions/Streaming and Stream |
| Callback contracts and traces | `Itasca.Visitor`, `.Core`, `.Trace`, `.Erasure`, `.Dispatch` | Results/Definitions/Visitor and Observations, Visitor |
| Compiler certificates and construction | `Itasca.Compiler` | Results/Definitions/Compiler and Runtime/Compiler |
| Slot/value/store representation | `Itasca.Representation` | Results/Definitions/Representation and Runtime/Representation |
| Source execution machine | `Itasca.SourceMachine` | Results/Definitions/SourceMachine and Runtime/SourceMachine |
| Source resource budgets | `Itasca.Spec.Resources` | Results/Definitions/Resources and Runtime/Integration/Api/SourceResourceBounds |
| Concrete interpreter simulation | `Itasca.Interp` | Runtime/Interp; public callback ownership and observations live in Results/Definitions/Host |
| Store invariants and operations | `Itasca.Store` | Results/Definitions/Store/{State,Read,Mutation} and Runtime/Store |
| Joined guarantees and host obligations | `Itasca.Integration` | Results/Definitions/{Host,Instantiation,Invocation,Runtime} and Runtime/Integration |
| Platform laws and checked witnesses | `Itasca.Platform` | Results/Definitions/Platform and Runtime/Platform |
| Aeneas computation and divergence contracts | `Itasca.Computation` | Support/Translation, Body/TableAdapters and generic contracts in Runtime/Platform/Laws |
| Rust-result postconditions | `Itasca.RustResult` | Results/Definitions/Foundations |
| Literal proof automation | `Itasca.Automation.LiteralDispatch` | Support/LiteralDispatch |
| Checked examples | `Itasca.Examples.<subject>` | Examples |

A file can extend an existing record or operation namespace owned elsewhere.
For example, binary body-grammar proofs extend Body grammar concepts and handler
proofs extend the extracted operation being verified. The namespace follows the
concept being extended; the module retains its actual dependency stage. Internal
helper subnamespaces describe a real subject, not the last proof-development step.

Shared representation definitions no longer inherit Compiler/Interp/Store simply
because those proofs first introduced them. `Representation.CompiledFunctionCapacity`
is an internal source-to-compiled-frame bound. Public resource contracts describe
source function demand; stored-code representation certificates remain internal.

## Extracted and upstream boundaries

Generated identities remain exactly as extracted: `Itasca.code`, `metadata`,
`reader`, `stream`, `runtime`, `wasm_types`, and other Rust module namespaces.
Ordinary per-function contracts extend the actual operation with `.spec`, `.total`,
`.sound`, `.complete` and other meaningful theorem suffixes. Upstream/generated
equation lemmas retain their operation-qualified identities too. No generated file
is edited to conform to this policy.

Public theorem wrappers whose statements differ from internal operation contracts
use their semantic API subject: `Itasca.Compiler.compile_with.*`,
`Itasca.Store.define_memory_with.spec`, `Itasca.Store.Instantantiation.instantiate_with.spec`
and `Itasca.Interp.invoke_with.*`. The statement names the exact extracted function.
This avoids both an accidental `Runtime.runtime` prefix and a collision with the
internal operation's existing contract. Validation wrappers already extend their
actual extracted operation without a duplicate identity and keep that convention.

`Computation` describes the outer Aeneas result, normal return and divergence;
`RustResult` describes the inner Rust success/error result. The bind inversion
lemma and `Computation.DivSpec` are generic computation facts even though their
current modules also hold translation and platform proofs. The proved vector-pop
contract extends `Aeneas.Std.alloc.vec.Vec.pop.spec` directly, just as the vector-clear
contract extends `Itasca.runtime.clear.spec`.

`SpecExt`, generated SpecTec judgments, Lean and Aeneas retain their own namespaces.
Proofs intentionally extending their existing operations are boundary extensions,
not additional Itasca subjects.

## Names and dependency boundaries

Use UpperCamelCase for semantic structures/relations, existing lowerCamelCase for
computation descriptors and snake_case for theorem basenames. Fields and attached
lemmas follow their owning declaration. Attach a record directly to its subject:
`Binary.Module` and `Module.Layout`, rather than `Binary.Module.Module` or
`Module.Layout.Layout`. Avoid adjacent duplicate components.
Simple private helpers may retain local names: Lean already qualifies their compiled
identities by their owning module. Explicit namespace extensions still follow this
subject map. Use qualified names where short names would be ambiguous; avoid compatibility aliases that indefinitely duplicate the
old namespace scheme.

Namespace agreement never permits an import that violates layering.
Results/Definitions imports only other public definitions and named foundations.
The other Results modules publish theorem statements, and implementation proofs
do not import those theorem modules. Validator isolation
and compiler Local → Body → Module stages remain properties of the import graph.
