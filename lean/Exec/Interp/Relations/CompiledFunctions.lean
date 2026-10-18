import Exec.Interp.Relations.FrameBindings
import Exec.Representation.FunctionTable
import Exec.Interp.Relations.FrameStack
import Exec.Code.Local.Relations.Common.Function
import Exec.Abs.Slice

namespace Exec.Interp
open Aeneas Aeneas.Std

/-- The compiler's retained local types cannot contain the specification's
polymorphic bottom type; every declared local therefore has a concrete default. -/
theorem declared_types_not_bottom {types functions params declared results body compiled epilogue}
    (certificate : Code.FunctionCode types functions params declared results body compiled epilogue) :
    Forall (fun ty => ty ≠ valtype.BOT) declared := by
  intro ty member
  have present : ty ∈ params ++ declared := List.mem_append_right _ member
  rw [← certificate.locals] at present
  obtain ⟨rawType, _, rfl⟩ := List.mem_map.mp present
  cases rawType <;> decide

/-- A retained defined function has source syntax and a complete compiler
certificate under its actual instance's canonical signature table. This
predicate contains only syntax, table lookups, and bytecode layout facts. -/
def FunctionCompiled {M : Type} (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (function : runtime.store.Function) : Prop :=
  ∀ instanceIndex functionIndex, function.code = .Wasm instanceIndex functionIndex →
    ∃ inst compiled signature functions declared body epilogue,
      store.instances.val[instanceIndex.val]? = some inst ∧
      inst.module.functions.val[functionIndex.val]? = some compiled ∧
      store.types.val[function.signature.val]? = some signature ∧
      code instanceIndex.val inst.module functionIndex.val =
        .FUNC (.mk_uN compiled.type_index.val) (declared.map local.LOCAL) body ∧
      FunctionTable store inst functions ∧
      Code.FunctionCode (Store.decodeInstance store inst).TYPES functions
        (signature.params.val.map sourceType) declared (signature.results.val.map sourceType)
        body compiled epilogue

def CompiledFunctions {M : Type} (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) : Prop :=
  ∀ function ∈ store.funcs.val, FunctionCompiled code store function

/-- A frame's retained signature list belongs to its actual instance. -/
theorem FrameProgram.function_table {M : Type} {store : runtime.store.Store M}
    {raw compiled locals results functions}
    (program : FrameProgram store raw compiled locals results functions)
    (inst : runtime.store.Instance)
    (lookup : store.instances.val[raw.instance.val]? = some inst) :
    FunctionTable store inst functions := by
  obtain ⟨actual, found, _, table⟩ := program.lookup
  have same : actual = inst := Option.some.inj (found.symm.trans lookup)
  exact same ▸ table

/-- Resolving a compiler CALL signature exposes the exact issued raw address,
function entry, and canonical signature consumed by interpreter dispatch. -/
theorem FrameProgram.resolve_call {M : Type} {store : runtime.store.Store M}
    {raw compiled locals results functions}
    (program : FrameProgram store raw compiled locals results functions)
    (inst : runtime.store.Instance)
    (lookup : store.instances.val[raw.instance.val]? = some inst)
    (index : Nat) (ty : functype) (signature : functions[index]? = some ty) :
    ∃ address function rawType, inst.funcs.val[index]? = some address ∧
      address.store = store.id ∧ store.funcs.val[address.index.val]? = some function ∧
      store.types.val[function.signature.val]? = some rawType ∧ Store.decodeFuncType rawType = ty :=
  (program.function_table inst lookup).resolve index ty signature

/-- The integer slice excludes host entries in the decoded function store,
so any actually resolved concrete function is a defined Wasm function. -/
theorem slice_function_defined {M : Type} (view : M → Slice U8)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M)
    (source : Abs.AState) (sameStore : source.store = Store.decodeStore view code store)
    (slice : Abs.SliceState source) (address : runtime.FuncAddr) (function : runtime.store.Function)
    (lookup : store.funcs.val[address.index.val]? = some function) :
    ∃ instanceIndex functionIndex, function.code = .Wasm instanceIndex functionIndex := by
  have found : source.store.FUNCS[address.index.val]? = some (Store.decodeFunction code store function) := by
    simp only [sameStore, Store.decodeStore, List.getElem?_map, lookup, Option.map_some]
  have restriction := slice.functions _ (List.mem_of_getElem? found)
  cases shape : function.code with
  | Host id => simp [Store.decodeFunction, shape] at restriction
  | Wasm inst fn => exact ⟨inst, fn, rfl⟩

/-- Compiled-function coverage exposes a source FUNC at the same retained
address; the decoded signature and owning module agree with concrete lookup. -/
theorem CompiledFunctions.defined {M : Type} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} (compiledFunctions : CompiledFunctions code store)
    (view : M → Slice U8) (address : runtime.FuncAddr) (function : runtime.store.Function)
    (instanceIndex functionIndex : Usize)
    (lookup : store.funcs.val[address.index.val]? = some function)
    (defined : function.code = .Wasm instanceIndex functionIndex) :
    ∃ inst compiled signature functions declared body epilogue,
      store.instances.val[instanceIndex.val]? = some inst ∧
      inst.module.functions.val[functionIndex.val]? = some compiled ∧
      store.types.val[function.signature.val]? = some signature ∧
      FunctionTable store inst functions ∧
      Code.FunctionCode (Store.decodeInstance store inst).TYPES functions
        (signature.params.val.map sourceType) declared (signature.results.val.map sourceType)
        body compiled epilogue ∧
      (Store.decodeStore view code store).FUNCS[address.index.val]? =
        some ⟨Store.decodeFuncType signature, Store.decodeInstance store inst,
          .FUNC (.mk_uN compiled.type_index.val) (declared.map local.LOCAL) body⟩ := by
  obtain ⟨inst, compiled, signature, functions, declared, body, epilogue,
      hi, hc, hs, source, table, certificate⟩ :=
    compiledFunctions function (List.mem_of_getElem? lookup) instanceIndex functionIndex defined
  exact ⟨inst, compiled, signature, functions, declared, body, epilogue,
    hi, hc, hs, table, certificate,
    defined_function_lookup view code store address function signature instanceIndex functionIndex inst _
      lookup hs defined hi source⟩

end Exec.Interp
