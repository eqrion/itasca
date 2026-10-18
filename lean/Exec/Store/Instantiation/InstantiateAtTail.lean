import Exec.Store.Instantiation.InstantiateTail
namespace Exec.Store
open Aeneas Aeneas.Std

/-- The extracted preparation prefix, parameterized only at its returned
precommit outcomes and its final committed initializer/start tail. -/
def instantiateInnerAtTail
  {M : Type} {P : Type} {F : Type} {A : Type} {R : Type} (platformMemoryBufferInst :
  runtime.platform.MemoryBuffer M) (platformPlatformInst :
  runtime.platform.Platform P M) (platformFloatOpsInst :
  runtime.platform.FloatOps F) (platformAllocInst : runtime.platform.Alloc A)
  (self : _root_.Exec.runtime.store.Store M)
  (module1 : _root_.Exec.runtime.compiler.ExecutableModule)
  (imports : Slice _root_.Exec.runtime.Extern) (platform : P)
  (committed : Bool)
  (rejected : (core.result.Result runtime.InstanceAddr runtime.ExecError × runtime.store.Store M × P × Bool) → Result R)
  (committedTail : runtime.InstanceAddr → runtime.store.Store M → P → Result R) : Result R
  := do
  let i := Slice.len imports
  let e ← runtime.compiler.ExecutableModule.env module1
  let s ← module.Env.imports e
  let i1 := Slice.len s
  if i != i1
  then
    rejected (core.result.Result.Err (runtime.ExecError.Link
      runtime.LinkError.MissingImport), self, platform, committed)
  else
    let i2 := alloc.vec.Vec.len self.instances
    if i2 >= self.limits.max_instances
    then
      rejected (core.result.Result.Err (runtime.ExecError.Exhausted
        runtime.ResourceLimit.Objects), self, platform, committed)
    else
      let s1 ← module.Env.types e
      let i3 := Slice.len s1
      let s2 ← module.Env.func_types e
      let i4 := Slice.len s2
      let s3 ← module.Env.table_types e
      let i5 := Slice.len s3
      let s4 ← module.Env.mem_types e
      let i6 := Slice.len s4
      let s5 ← module.Env.global_types e
      let i7 := Slice.len s5
      let s6 ← module.Env.elements e
      let i8 := Slice.len s6
      let t ← runtime.compiler.ExecutableModule.tail module1
      let i9 := alloc.vec.Vec.len t.data
      let (items, status) ←
        runtime.store.instantiate.Store.instantiate_inner_loop0 0#usize
          (core.result.Result.Ok ())
          (Array.make 7#usize [ i3, i4, i5, i6, i7, i8, i9 ]) 0#usize
      let (items1, status1) ←
        runtime.store.instantiate.Store.instantiate_inner_loop1 module1 items status
          0#usize
      let cf ← core.result.Result.Insts.CoreOpsTry.branch status1
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let b ←
          runtime.store.within self.instance_items items1
            self.limits.max_instance_items
        if b
        then
          let e1 ← runtime.compiler.ExecutableModule.env module1
          let s7 ← module.Env.func_types e1
          let i10 := Slice.len s7
          let (r, v) ←
            runtime.reserve platformAllocInst (alloc.vec.Vec.new
              _root_.Exec.runtime.FuncAddr) i10
          let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r
          match cf1 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            let s8 ← module.Env.table_types e1
            let i11 := Slice.len s8
            let (r1, v1) ←
              runtime.reserve platformAllocInst (alloc.vec.Vec.new
                _root_.Exec.runtime.TableAddr) i11
            let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r1
            match cf2 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              let s9 ← module.Env.mem_types e1
              let i12 := Slice.len s9
              let (r2, v2) ←
                runtime.reserve platformAllocInst (alloc.vec.Vec.new
                  _root_.Exec.runtime.MemoryAddr) i12
              let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r2
              match cf3 with
              | core.ops.control_flow.ControlFlow.Continue _ =>
                let s10 ← module.Env.global_types e1
                let i13 := Slice.len s10
                let (r3, v3) ←
                  runtime.reserve platformAllocInst (alloc.vec.Vec.new
                    _root_.Exec.runtime.GlobalAddr) i13
                let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r3
                match cf4 with
                | core.ops.control_flow.ControlFlow.Continue _ =>
                  let (self1, status2, inst) ←
                    runtime.store.instantiate.Store.instantiate_inner_loop2
                      platformMemoryBufferInst self imports status1 0#usize
                      {
                        module := module1,
                        types := (alloc.vec.Vec.new Std.Usize),
                        funcs := v,
                        tables := v1,
                        memories := v2,
                        globals := v3,
                        elements := (alloc.vec.Vec.new Std.Usize),
                        data := (alloc.vec.Vec.new Std.Usize)
                      }
                  let cf5 ←
                    core.result.Result.Insts.CoreOpsTry.branch status2
                  match cf5 with
                  | core.ops.control_flow.ControlFlow.Continue _ =>
                    let i14 := alloc.vec.Vec.len self1.instances
                    let e2 ←
                      runtime.compiler.ExecutableModule.env inst.module
                    let s11 ← module.Env.types e2
                    let i15 := Slice.len s11
                    let (r4, v4) ←
                      runtime.reserve platformAllocInst inst.types i15
                    let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r4
                    match cf6 with
                    | core.ops.control_flow.ControlFlow.Continue _ =>
                      let (self2, status3, em, v5, v6, v7, v8, v9, v10, v11)
                        ←
                        runtime.store.instantiate.Store.instantiate_inner_loop3
                          platformMemoryBufferInst platformAllocInst self1
                          status2 0#usize { inst with types := v4 }
                      let cf7 ←
                        core.result.Result.Insts.CoreOpsTry.branch status3
                      match cf7 with
                      | core.ops.control_flow.ControlFlow.Continue _ =>
                        let (self3, status4, em1, v12, v13, v14, v15, v16, v17,
                          v18) ←
                          runtime.store.instantiate.Store.instantiate_inner_loop4
                            platformMemoryBufferInst platformAllocInst self2
                            status3 0#usize
                            {
                              module := em,
                              types := v5,
                              funcs := v6,
                              tables := v7,
                              memories := v8,
                              globals := v9,
                              elements := v10,
                              data := v11
                            } i14
                        let cf8 ←
                          core.result.Result.Insts.CoreOpsTry.branch status4
                        match cf8 with
                        | core.ops.control_flow.ControlFlow.Continue _ =>
                          let i16 := alloc.vec.Vec.len v14
                          let (self4, status5, em2, v19, v20, v21, v22, v23,
                            v24, v25) ←
                            runtime.store.instantiate.Store.instantiate_inner_loop5
                              platformMemoryBufferInst platformAllocInst self3
                              status4 i16
                              {
                                module := em1,
                                types := v12,
                                funcs := v13,
                                tables := v14,
                                memories := v15,
                                globals := v16,
                                elements := v17,
                                data := v18
                              }
                          let cf9 ←
                            core.result.Result.Insts.CoreOpsTry.branch status5
                          match cf9 with
                          | core.ops.control_flow.ControlFlow.Continue _ =>
                            let i17 := alloc.vec.Vec.len v22
                            let (self5, status6, em3, v26, v27, v28, v29, v30,
                              v31, v32) ←
                              runtime.store.instantiate.Store.instantiate_inner_loop6
                                platformMemoryBufferInst platformAllocInst
                                self4 status5 i17
                                {
                                  module := em2,
                                  types := v19,
                                  funcs := v20,
                                  tables := v21,
                                  memories := v22,
                                  globals := v23,
                                  elements := v24,
                                  data := v25
                                }
                            let cf10 ←
                              core.result.Result.Insts.CoreOpsTry.branch
                                status6
                            match cf10 with
                            | core.ops.control_flow.ControlFlow.Continue _ =>
                              let (r5, v33) ←
                                runtime.reserve platformAllocInst
                                  self5.instances 1#usize
                              let cf11 ←
                                core.result.Result.Insts.CoreOpsTry.branch r5
                              match cf11 with
                              | core.ops.control_flow.ControlFlow.Continue _ =>
                                let v34 ←
                                  alloc.vec.Vec.push v33
                                    ({
                                       module := em3,
                                       types := v26,
                                       funcs := v27,
                                       tables := v28,
                                       memories := v29,
                                       globals := v30,
                                       elements := v31,
                                       data := v32
                                     } : _root_.Exec.runtime.store.Instance)
                                let (i18, sl, v35, v36, v37, v38, v39, v40,
                                  v41, v42, v43, i19, i20, i21, i22, platform1,
                                  status7) ←
                                  runtime.store.instantiate.Store.instantiate_inner_loop7
                                    platformMemoryBufferInst
                                    platformPlatformInst platformFloatOpsInst
                                    platformAllocInst
                                    { self5 with instances := v34 } platform
                                    status6 0#usize i14
                                let cf12 ←
                                  core.result.Result.Insts.CoreOpsTry.branch
                                    status7
                                match cf12 with
                                | core.ops.control_flow.ControlFlow.Continue _
                                  =>
                                  let i23 ←
                                    alloc.vec.Vec.index
                                      (core.slice.index.SliceIndexUsizeSlice
                                      _root_.Exec.runtime.store.Instance) v40
                                      i14
                                  let e3 ←
                                    runtime.compiler.ExecutableModule.env
                                      i23.module
                                  let s12 ← module.Env.elements e3
                                  let element_count := Slice.len s12
                                  let (i24, index_mut_back) ←
                                    alloc.vec.Vec.index_mut
                                      (core.slice.index.SliceIndexUsizeSlice
                                      _root_.Exec.runtime.store.Instance) v40
                                      i14
                                  let (r6, v44) ←
                                    runtime.reserve platformAllocInst
                                      i24.elements element_count
                                  let cf13 ←
                                    core.result.Result.Insts.CoreOpsTry.branch
                                      r6
                                  match cf13 with
                                  | core.ops.control_flow.ControlFlow.Continue
                                    _ =>
                                    let v45 :=
                                      index_mut_back
                                        { i24 with elements := v44 }
                                    let (i25, sl1, v46, v47, v48, v49, v50,
                                      v51, v52, v53, v54, i26, i27, i28, i29,
                                      platform2, status8) ←
                                      runtime.store.instantiate.Store.instantiate_inner_loop8
                                        platformMemoryBufferInst
                                        platformPlatformInst
                                        platformFloatOpsInst platformAllocInst
                                        {
                                          id := i18,
                                          limits := sl,
                                          funcs := v35,
                                          types := v36,
                                          tables := v37,
                                          memories := v38,
                                          globals := v39,
                                          instances := v45,
                                          elems := v41,
                                          datas := v42,
                                          externs := v43,
                                          instance_items := i19,
                                          signature_values := i20,
                                          memory_bytes := i21,
                                          table_elements := i22
                                        } platform1 status7 0#usize i14
                                    let cf14 ←
                                      core.result.Result.Insts.CoreOpsTry.branch
                                        status8
                                    match cf14 with
                                    |
                                      core.ops.control_flow.ControlFlow.Continue
                                      _ =>
                                      let i30 ←
                                        alloc.vec.Vec.index
                                          (core.slice.index.SliceIndexUsizeSlice
                                          _root_.Exec.runtime.store.Instance)
                                          v51 i14
                                      let t1 ←
                                        runtime.compiler.ExecutableModule.tail
                                          i30.module
                                      let data_count :=
                                        alloc.vec.Vec.len t1.data
                                      let (i31, index_mut_back1) ←
                                        alloc.vec.Vec.index_mut
                                          (core.slice.index.SliceIndexUsizeSlice
                                          _root_.Exec.runtime.store.Instance)
                                          v51 i14
                                      let (r7, v55) ←
                                        runtime.reserve platformAllocInst
                                          i31.data data_count
                                      let cf15 ←
                                        core.result.Result.Insts.CoreOpsTry.branch
                                          r7
                                      match cf15 with
                                      |
                                        core.ops.control_flow.ControlFlow.Continue
                                        _ =>
                                        let v56 :=
                                          index_mut_back1
                                            { i31 with data := v55 }
                                        let (i32, sl2, v57, v58, v59, v60, v61,
                                          v62, v63, v64, v65, i33, i34, i35,
                                          i36, status9) ←
                                          runtime.store.instantiate.Store.instantiate_inner_loop9
                                            platformMemoryBufferInst
                                            platformAllocInst
                                            {
                                              id := i25,
                                              limits := sl1,
                                              funcs := v46,
                                              types := v47,
                                              tables := v48,
                                              memories := v49,
                                              globals := v50,
                                              instances := v56,
                                              elems := v52,
                                              datas := v53,
                                              externs := v54,
                                              instance_items := i26,
                                              signature_values := i27,
                                              memory_bytes := i28,
                                              table_elements := i29
                                            } status8 0#usize i14
                                        let cf16 ←
                                          core.result.Result.Insts.CoreOpsTry.branch
                                            status9
                                        match cf16 with
                                        |
                                          core.ops.control_flow.ControlFlow.Continue
                                          _ =>
                                          let i37 ←
                                            alloc.vec.Vec.index
                                              (core.slice.index.SliceIndexUsizeSlice
                                              _root_.Exec.runtime.store.Instance)
                                              v62 i14
                                          let vp ←
                                            runtime.compiler.ExecutableModule.impl.profile
                                              i37.module
                                          let b1 ← runtime.store.wasm1 vp
                                          if b1
                                          then
                                            let (i38, sl3, v66, v67, v68, v69,
                                              v70, v71, v72, v73, v74, i39,
                                              i40, i41, i42, platform3,
                                              status10) ←
                                              runtime.store.instantiate.Store.instantiate_inner_loop10
                                                platformMemoryBufferInst
                                                platformPlatformInst
                                                platformFloatOpsInst
                                                platformAllocInst
                                                {
                                                  id := i32,
                                                  limits := sl2,
                                                  funcs := v57,
                                                  types := v58,
                                                  tables := v59,
                                                  memories := v60,
                                                  globals := v61,
                                                  instances := v62,
                                                  elems := v63,
                                                  datas := v64,
                                                  externs := v65,
                                                  instance_items := i33,
                                                  signature_values := i34,
                                                  memory_bytes := i35,
                                                  table_elements := i36
                                                } platform2 status9 0#usize i14
                                            let cf17 ←
                                              core.result.Result.Insts.CoreOpsTry.branch
                                                status10
                                            match cf17 with
                                            |
                                              core.ops.control_flow.ControlFlow.Continue
                                              _ =>
                                              let (i43, sl4, v75, v76, v77,
                                                v78, v79, v80, v81, v82, v83,
                                                i44, i45, i46, i47, platform4,
                                                status11) ←
                                                runtime.store.instantiate.Store.instantiate_inner_loop11
                                                  platformMemoryBufferInst
                                                  platformPlatformInst
                                                  platformFloatOpsInst
                                                  platformAllocInst
                                                  {
                                                    id := i38,
                                                    limits := sl3,
                                                    funcs := v66,
                                                    types := v67,
                                                    tables := v68,
                                                    memories := v69,
                                                    globals := v70,
                                                    instances := v71,
                                                    elems := v72,
                                                    datas := v73,
                                                    externs := v74,
                                                    instance_items := i39,
                                                    signature_values := i40,
                                                    memory_bytes := i41,
                                                    table_elements := i42
                                                  } platform3 status10 0#usize
                                                  i14
                                              let cf18 ←
                                                core.result.Result.Insts.CoreOpsTry.branch
                                                  status11
                                              match cf18 with
                                              |
                                                core.ops.control_flow.ControlFlow.Continue
                                                _ =>
                                                let i48 ← i44 + items1
                                                committedTail ⟨self1.id, i14⟩
                                                  {
                                                      id := i43,
                                                      limits := sl4,
                                                      funcs := v75,
                                                      types := v76,
                                                      tables := v77,
                                                      memories := v78,
                                                      globals := v79,
                                                      instances := v80,
                                                      elems := v81,
                                                      datas := v82,
                                                      externs := v83,
                                                      instance_items := i48,
                                                      signature_values := i45,
                                                      memory_bytes := i46,
                                                      table_elements := i47
                                                    } platform4
                                              |
                                                core.ops.control_flow.ControlFlow.Break
                                                residual =>
                                                let r8 ←
                                                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                    _root_.Exec.runtime.InstanceAddr
                                                    (core.convert.FromSame
                                                    _root_.Exec.runtime.ExecError)
                                                    residual
                                                rejected (r8,
                                                  {
                                                    id := i43,
                                                    limits := sl4,
                                                    funcs := v75,
                                                    types := v76,
                                                    tables := v77,
                                                    memories := v78,
                                                    globals := v79,
                                                    instances := v80,
                                                    elems := v81,
                                                    datas := v82,
                                                    externs := v83,
                                                    instance_items := i44,
                                                    signature_values := i45,
                                                    memory_bytes := i46,
                                                    table_elements := i47
                                                  }, platform4, committed)
                                            |
                                              core.ops.control_flow.ControlFlow.Break
                                              residual =>
                                              let r8 ←
                                                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                  _root_.Exec.runtime.InstanceAddr
                                                  (core.convert.FromSame
                                                  _root_.Exec.runtime.ExecError)
                                                  residual
                                              rejected (r8,
                                                {
                                                  id := i38,
                                                  limits := sl3,
                                                  funcs := v66,
                                                  types := v67,
                                                  tables := v68,
                                                  memories := v69,
                                                  globals := v70,
                                                  instances := v71,
                                                  elems := v72,
                                                  datas := v73,
                                                  externs := v74,
                                                  instance_items := i39,
                                                  signature_values := i40,
                                                  memory_bytes := i41,
                                                  table_elements := i42
                                                }, platform3, committed)
                                          else
                                            let i38 ← i33 + items1
                                            committedTail ⟨self1.id, i14⟩
                                              {
                                                  id := i32,
                                                  limits := sl2,
                                                  funcs := v57,
                                                  types := v58,
                                                  tables := v59,
                                                  memories := v60,
                                                  globals := v61,
                                                  instances := v62,
                                                  elems := v63,
                                                  datas := v64,
                                                  externs := v65,
                                                  instance_items := i38,
                                                  signature_values := i34,
                                                  memory_bytes := i35,
                                                  table_elements := i36
                                                } platform2
                                        |
                                          core.ops.control_flow.ControlFlow.Break
                                          residual =>
                                          let r8 ←
                                            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                              _root_.Exec.runtime.InstanceAddr
                                              (core.convert.FromSame
                                              _root_.Exec.runtime.ExecError)
                                              residual
                                          rejected (r8,
                                            {
                                              id := i32,
                                              limits := sl2,
                                              funcs := v57,
                                              types := v58,
                                              tables := v59,
                                              memories := v60,
                                              globals := v61,
                                              instances := v62,
                                              elems := v63,
                                              datas := v64,
                                              externs := v65,
                                              instance_items := i33,
                                              signature_values := i34,
                                              memory_bytes := i35,
                                              table_elements := i36
                                            }, platform2, committed)
                                      | core.ops.control_flow.ControlFlow.Break
                                        residual =>
                                        let r8 ←
                                          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                            _root_.Exec.runtime.InstanceAddr
                                            (core.convert.FromSame
                                            _root_.Exec.runtime.ExecError)
                                            residual
                                        let v56 :=
                                          index_mut_back1
                                            { i31 with data := v55 }
                                        rejected (r8,
                                          {
                                            id := i25,
                                            limits := sl1,
                                            funcs := v46,
                                            types := v47,
                                            tables := v48,
                                            memories := v49,
                                            globals := v50,
                                            instances := v56,
                                            elems := v52,
                                            datas := v53,
                                            externs := v54,
                                            instance_items := i26,
                                            signature_values := i27,
                                            memory_bytes := i28,
                                            table_elements := i29
                                          }, platform2, committed)
                                    | core.ops.control_flow.ControlFlow.Break
                                      residual =>
                                      let r7 ←
                                        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                          _root_.Exec.runtime.InstanceAddr
                                          (core.convert.FromSame
                                          _root_.Exec.runtime.ExecError)
                                          residual
                                      rejected (r7,
                                        {
                                          id := i25,
                                          limits := sl1,
                                          funcs := v46,
                                          types := v47,
                                          tables := v48,
                                          memories := v49,
                                          globals := v50,
                                          instances := v51,
                                          elems := v52,
                                          datas := v53,
                                          externs := v54,
                                          instance_items := i26,
                                          signature_values := i27,
                                          memory_bytes := i28,
                                          table_elements := i29
                                        }, platform2, committed)
                                  | core.ops.control_flow.ControlFlow.Break
                                    residual =>
                                    let r7 ←
                                      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                        _root_.Exec.runtime.InstanceAddr
                                        (core.convert.FromSame
                                        _root_.Exec.runtime.ExecError) residual
                                    let v45 :=
                                      index_mut_back
                                        { i24 with elements := v44 }
                                    rejected (r7,
                                      {
                                        id := i18,
                                        limits := sl,
                                        funcs := v35,
                                        types := v36,
                                        tables := v37,
                                        memories := v38,
                                        globals := v39,
                                        instances := v45,
                                        elems := v41,
                                        datas := v42,
                                        externs := v43,
                                        instance_items := i19,
                                        signature_values := i20,
                                        memory_bytes := i21,
                                        table_elements := i22
                                      }, platform1, committed)
                                | core.ops.control_flow.ControlFlow.Break
                                  residual =>
                                  let r6 ←
                                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                      _root_.Exec.runtime.InstanceAddr
                                      (core.convert.FromSame
                                      _root_.Exec.runtime.ExecError) residual
                                  rejected (r6,
                                    {
                                      id := i18,
                                      limits := sl,
                                      funcs := v35,
                                      types := v36,
                                      tables := v37,
                                      memories := v38,
                                      globals := v39,
                                      instances := v40,
                                      elems := v41,
                                      datas := v42,
                                      externs := v43,
                                      instance_items := i19,
                                      signature_values := i20,
                                      memory_bytes := i21,
                                      table_elements := i22
                                    }, platform1, committed)
                              | core.ops.control_flow.ControlFlow.Break
                                residual =>
                                let r6 ←
                                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                    _root_.Exec.runtime.InstanceAddr
                                    (core.convert.FromSame
                                    _root_.Exec.runtime.ExecError) residual
                                rejected (r6, { self5 with instances := v33 },
                                  platform, committed)
                            | core.ops.control_flow.ControlFlow.Break residual
                              =>
                              let r5 ←
                                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                  _root_.Exec.runtime.InstanceAddr
                                  (core.convert.FromSame
                                  _root_.Exec.runtime.ExecError) residual
                              rejected (r5, self5, platform, committed)
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            let r5 ←
                              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                _root_.Exec.runtime.InstanceAddr
                                (core.convert.FromSame
                                _root_.Exec.runtime.ExecError) residual
                            rejected (r5, self4, platform, committed)
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          let r5 ←
                            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                              _root_.Exec.runtime.InstanceAddr
                              (core.convert.FromSame
                              _root_.Exec.runtime.ExecError) residual
                          rejected (r5, self3, platform, committed)
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        let r5 ←
                          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                            _root_.Exec.runtime.InstanceAddr
                            (core.convert.FromSame
                            _root_.Exec.runtime.ExecError) residual
                        rejected (r5, self2, platform, committed)
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      let r5 ←
                        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                          _root_.Exec.runtime.InstanceAddr
                          (core.convert.FromSame _root_.Exec.runtime.ExecError)
                          residual
                      rejected (r5, self1, platform, committed)
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    let r4 ←
                      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                        _root_.Exec.runtime.InstanceAddr (core.convert.FromSame
                        _root_.Exec.runtime.ExecError) residual
                    rejected (r4, self1, platform, committed)
                | core.ops.control_flow.ControlFlow.Break residual =>
                  let r4 ←
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                      _root_.Exec.runtime.InstanceAddr (core.convert.FromSame
                      _root_.Exec.runtime.ExecError) residual
                  rejected (r4, self, platform, committed)
              | core.ops.control_flow.ControlFlow.Break residual =>
                let r3 ←
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                    _root_.Exec.runtime.InstanceAddr (core.convert.FromSame
                    _root_.Exec.runtime.ExecError) residual
                rejected (r3, self, platform, committed)
            | core.ops.control_flow.ControlFlow.Break residual =>
              let r2 ←
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  _root_.Exec.runtime.InstanceAddr (core.convert.FromSame
                  _root_.Exec.runtime.ExecError) residual
              rejected (r2, self, platform, committed)
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r1 ←
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                _root_.Exec.runtime.InstanceAddr (core.convert.FromSame
                _root_.Exec.runtime.ExecError) residual
            rejected (r1, self, platform, committed)
        else
          rejected (core.result.Result.Err (runtime.ExecError.Exhausted
            runtime.ResourceLimit.Objects), self, platform, committed)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            _root_.Exec.runtime.InstanceAddr (core.convert.FromSame
            _root_.Exec.runtime.ExecError) residual
        rejected (r, self, platform, committed)

/-- Instantiating the continuations recovers the extracted computation for all
internal inputs, including failure and divergence. -/
theorem instantiateInnerAtTail_original {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (store : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P) (committed : Bool) :
    instantiateInnerAtTail memory hooks floats allocator store module imports platform committed
      Result.ok (instantiate_tail memory hooks floats allocator) =
      runtime.store.instantiate.Store.instantiate_inner memory hooks floats allocator store module imports platform committed := by
  rfl
end Exec.Store
