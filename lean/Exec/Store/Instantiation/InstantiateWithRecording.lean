import Exec.Store.Instantiation.InstantiateRecording
namespace Exec.Store
open Aeneas Aeneas.Std SpecExt

/-- Public instantiation records the committed start and retains its log across
the exact extracted rollback/commit decision. -/
def recordedInstantiateWith
  {M : Type} {P : Type} {F : Type} {A : Type} (platformMemoryBufferInst :
  runtime.platform.MemoryBuffer M) (platformPlatformInst :
  runtime.platform.Platform P M) (platformFloatOpsInst :
  runtime.platform.FloatOps F) (platformAllocInst : runtime.platform.Alloc A)
  (self : _root_.Exec.runtime.store.Store M)
  (module1 : _root_.Exec.runtime.compiler.ExecutableModule)
  (imports : Slice _root_.Exec.runtime.Extern) (platform : P) (prior : List HostEvent) :
  Result (((core.result.Result _root_.Exec.runtime.InstanceAddr
    _root_.Exec.runtime.ExecError) × (_root_.Exec.runtime.store.Store M) × P) × List HostEvent)
  := do
  let functions := alloc.vec.Vec.len self.funcs
  let tables := alloc.vec.Vec.len self.tables
  let memories := alloc.vec.Vec.len self.memories
  let globals := alloc.vec.Vec.len self.globals
  let types1 := alloc.vec.Vec.len self.types
  let instances := alloc.vec.Vec.len self.instances
  let elems := alloc.vec.Vec.len self.elems
  let datas := alloc.vec.Vec.len self.datas
  let ((result, self1, platform1, committed),trace) ←
    recordedInstantiateInner platformMemoryBufferInst
      platformPlatformInst platformFloatOpsInst platformAllocInst self module1
      imports platform false prior
  let b ← runtime.store.instantiation_failed result
  if b
  then
    if committed
    then .ok ((result, self1, platform1),trace)
    else
      let (i, sl, v, v1, v2, v3, v4, v5, v6, v7, v8, i1) ←
        runtime.store.instantiate.Store.instantiate_with_loop0 self1 elems
      let v9 ← runtime.store.instantiate.Store.instantiate_with_loop1 v7 datas
      let v10 ← runtime.store.instantiate.Store.instantiate_with_loop2 v5 instances
      let v11 ← runtime.store.instantiate.Store.instantiate_with_loop3 v functions
      let v12 ← runtime.store.instantiate.Store.instantiate_with_loop4 v2 tables
      let v13 ← runtime.store.instantiate.Store.instantiate_with_loop5 v3 memories
      let v14 ← runtime.store.instantiate.Store.instantiate_with_loop6 v4 globals
      let v15 ← runtime.store.instantiate.Store.instantiate_with_loop7 v1 types1
      .ok ((result,
        {
          self
            with
            id := i,
            limits := sl,
            funcs := v11,
            types := v15,
            tables := v12,
            memories := v13,
            globals := v14,
            instances := v10,
            elems := v6,
            datas := v9,
            externs := v8,
            instance_items := i1
        }, platform1),trace)
  else .ok ((result, self1, platform1),trace)

end Exec.Store
