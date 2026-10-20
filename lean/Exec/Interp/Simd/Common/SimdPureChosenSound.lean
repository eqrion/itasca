import Exec.Interp.Simd.Common.SimdPureChosenRelation
import Exec.Interp.Simd.Common.SimdChosenPrimitives
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- Every actual source-table pure SIMD operation preserves one fixed vector
policy. Numeric replies are established at the primitive implementations. -/
theorem pure_entries_chosen {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : Platform.FloatOpsCorrect floats)
    {choices : Exec.Spec.SourceChoices} (vector : choices.vector=Exec.Spec.firstVectorChoice) (occurrence : Nat) (opcode : U32) (bounded : opcode.val < 256) :
    PureEntryChosen choices occurrence floats opcode := by
  rcases opcode with ⟨⟨n,hn⟩⟩
  change n < 256 at bounded
  interval_cases n
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_14 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure14 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_15 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure15 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_16 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure16 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_17 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure17 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_18 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure18 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_19 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure19 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_20 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure20 = some op at meaning
    cases meaning
    rfl
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_35 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure35 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_36 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure36 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_37 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure37 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_38 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure38 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_39 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure39 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_40 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure40 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_41 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure41 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_42 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure42 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_43 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure43 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_44 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure44 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_45 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure45 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_46 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure46 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_47 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure47 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_48 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure48 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_49 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure49 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_50 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure50 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_51 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure51 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_52 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure52 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_53 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure53 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_54 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure54 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_55 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure55 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_56 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure56 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_57 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure57 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_58 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure58 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_59 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure59 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_60 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure60 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_61 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure61 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_62 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure62 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_63 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure63 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_64 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure64 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_65 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure65 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_66 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure66 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_67 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure67 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_68 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure68 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_69 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure69 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_70 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure70 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_71 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure71 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_72 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure72 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_73 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure73 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_74 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure74 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_75 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure75 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_76 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure76 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_77 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure77 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_78 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure78 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_79 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure79 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_80 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure80 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_81 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure81 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_82 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure82 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_83 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure83 = some op at meaning
    cases meaning
    rfl
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure94 = some op at meaning
    cases meaning
    with_unfolding_all exact float_resize_simd_chosen_pure floats vector occurrence laws .demote offset laneIndex bits x y z memory
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure95 = some op at meaning
    cases meaning
    with_unfolding_all exact float_resize_simd_chosen_pure floats vector occurrence laws .promote offset laneIndex bits x y z memory
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_96 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure96 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_97 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure97 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_98 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure98 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_99 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure99 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_100 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure100 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_101 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure101 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_102 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure102 = some op at meaning
    cases meaning
    rfl
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure103 = some op at meaning
    cases meaning
    with_unfolding_all exact float_unary_simd_chosen_pure floats vector occurrence laws .F32 .CEIL offset laneIndex bits x y z memory
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure104 = some op at meaning
    cases meaning
    with_unfolding_all exact float_unary_simd_chosen_pure floats vector occurrence laws .F32 .FLOOR offset laneIndex bits x y z memory
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure105 = some op at meaning
    cases meaning
    with_unfolding_all exact float_unary_simd_chosen_pure floats vector occurrence laws .F32 .TRUNC offset laneIndex bits x y z memory
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure106 = some op at meaning
    cases meaning
    with_unfolding_all exact float_unary_simd_chosen_pure floats vector occurrence laws .F32 .NEAREST offset laneIndex bits x y z memory
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_107 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure107 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_108 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure108 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_109 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure109 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_110 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure110 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_111 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure111 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_112 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure112 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_113 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure113 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_114 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure114 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_115 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure115 = some op at meaning
    cases meaning
    rfl
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure116 = some op at meaning
    cases meaning
    with_unfolding_all exact float_unary_simd_chosen_pure floats vector occurrence laws .F64 .CEIL offset laneIndex bits x y z memory
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure117 = some op at meaning
    cases meaning
    with_unfolding_all exact float_unary_simd_chosen_pure floats vector occurrence laws .F64 .FLOOR offset laneIndex bits x y z memory
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_118 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure118 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_119 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure119 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_120 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure120 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_121 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure121 = some op at meaning
    cases meaning
    rfl
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure122 = some op at meaning
    cases meaning
    with_unfolding_all exact float_unary_simd_chosen_pure floats vector occurrence laws .F64 .TRUNC offset laneIndex bits x y z memory
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_123 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure123 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_124 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure124 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_125 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure125 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_126 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure126 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_127 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure127 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_128 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure128 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_129 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure129 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_130 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure130 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_131 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure131 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_132 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure132 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_133 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure133 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_134 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure134 = some op at meaning
    cases meaning
    rfl
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure135 = some op at meaning
    cases meaning
    with_unfolding_all exact extend_simd_chosen_pure floats vector occurrence .i8 false true offset laneIndex bits x y z memory
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure136 = some op at meaning
    cases meaning
    with_unfolding_all exact extend_simd_chosen_pure floats vector occurrence .i8 true true offset laneIndex bits x y z memory
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure137 = some op at meaning
    cases meaning
    with_unfolding_all exact extend_simd_chosen_pure floats vector occurrence .i8 false false offset laneIndex bits x y z memory
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure138 = some op at meaning
    cases meaning
    with_unfolding_all exact extend_simd_chosen_pure floats vector occurrence .i8 true false offset laneIndex bits x y z memory
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_139 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure139 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_140 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure140 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_141 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure141 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_142 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure142 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_143 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure143 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_144 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure144 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_145 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure145 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_146 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure146 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_147 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure147 = some op at meaning
    cases meaning
    rfl
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure148 = some op at meaning
    cases meaning
    with_unfolding_all exact float_unary_simd_chosen_pure floats vector occurrence laws .F64 .NEAREST offset laneIndex bits x y z memory
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_149 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure149 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_150 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure150 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_151 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure151 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_152 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure152 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_153 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure153 = some op at meaning
    cases meaning
    rfl
  · intro op meaning
    change none = some op at meaning
    contradiction
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_155 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure155 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_156 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure156 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_157 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure157 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_158 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure158 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_159 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure159 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_160 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure160 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_161 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure161 = some op at meaning
    cases meaning
    rfl
  · intro op meaning
    change none = some op at meaning
    contradiction
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_163 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure163 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_164 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure164 = some op at meaning
    cases meaning
    rfl
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure167 = some op at meaning
    cases meaning
    with_unfolding_all exact extend_simd_chosen_pure floats vector occurrence .i16 false true offset laneIndex bits x y z memory
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure168 = some op at meaning
    cases meaning
    with_unfolding_all exact extend_simd_chosen_pure floats vector occurrence .i16 true true offset laneIndex bits x y z memory
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure169 = some op at meaning
    cases meaning
    with_unfolding_all exact extend_simd_chosen_pure floats vector occurrence .i16 false false offset laneIndex bits x y z memory
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure170 = some op at meaning
    cases meaning
    with_unfolding_all exact extend_simd_chosen_pure floats vector occurrence .i16 true false offset laneIndex bits x y z memory
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_171 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure171 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_172 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure172 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_173 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure173 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_174 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure174 = some op at meaning
    cases meaning
    rfl
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_177 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure177 = some op at meaning
    cases meaning
    rfl
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_181 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure181 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_182 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure182 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_183 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure183 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_184 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure184 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_185 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure185 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_186 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure186 = some op at meaning
    cases meaning
    rfl
  · intro op meaning
    change none = some op at meaning
    contradiction
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_188 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure188 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_189 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure189 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_190 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure190 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_191 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure191 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_192 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure192 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_193 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure193 = some op at meaning
    cases meaning
    rfl
  · intro op meaning
    change none = some op at meaning
    contradiction
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_195 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure195 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_196 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure196 = some op at meaning
    cases meaning
    rfl
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure199 = some op at meaning
    cases meaning
    with_unfolding_all exact extend_simd_chosen_pure floats vector occurrence .i32 false true offset laneIndex bits x y z memory
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure200 = some op at meaning
    cases meaning
    with_unfolding_all exact extend_simd_chosen_pure floats vector occurrence .i32 true true offset laneIndex bits x y z memory
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure201 = some op at meaning
    cases meaning
    with_unfolding_all exact extend_simd_chosen_pure floats vector occurrence .i32 false false offset laneIndex bits x y z memory
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure202 = some op at meaning
    cases meaning
    with_unfolding_all exact extend_simd_chosen_pure floats vector occurrence .i32 true false offset laneIndex bits x y z memory
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_203 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure203 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_204 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure204 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_205 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure205 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_206 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure206 = some op at meaning
    cases meaning
    rfl
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_209 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure209 = some op at meaning
    cases meaning
    rfl
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_213 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure213 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_214 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure214 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_215 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure215 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_216 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure216 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_217 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure217 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_218 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure218 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_219 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure219 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_220 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure220 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_221 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure221 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_222 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure222 = some op at meaning
    cases meaning
    rfl
  · apply pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_223 floats)
    intro op meaning x y z
    change some Itasca.Wasm2.Simd.pure223 = some op at meaning
    cases meaning
    rfl
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure224 = some op at meaning
    cases meaning
    with_unfolding_all exact float_unary_simd_chosen_pure floats vector occurrence laws .F32 .ABS offset laneIndex bits x y z memory
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure225 = some op at meaning
    cases meaning
    with_unfolding_all exact float_unary_simd_chosen_pure floats vector occurrence laws .F32 .NEG offset laneIndex bits x y z memory
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure227 = some op at meaning
    cases meaning
    with_unfolding_all exact float_unary_simd_chosen_pure floats vector occurrence laws .F32 .SQRT offset laneIndex bits x y z memory
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure228 = some op at meaning
    cases meaning
    with_unfolding_all exact float_binary_simd_chosen_pure floats vector occurrence laws .F32 .ADD offset laneIndex bits x y z memory
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure229 = some op at meaning
    cases meaning
    with_unfolding_all exact float_binary_simd_chosen_pure floats vector occurrence laws .F32 .SUB offset laneIndex bits x y z memory
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure230 = some op at meaning
    cases meaning
    with_unfolding_all exact float_binary_simd_chosen_pure floats vector occurrence laws .F32 .MUL offset laneIndex bits x y z memory
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure231 = some op at meaning
    cases meaning
    with_unfolding_all exact float_binary_simd_chosen_pure floats vector occurrence laws .F32 .DIV offset laneIndex bits x y z memory
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure232 = some op at meaning
    cases meaning
    with_unfolding_all exact float_binary_simd_chosen_pure floats vector occurrence laws .F32 .MIN offset laneIndex bits x y z memory
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure233 = some op at meaning
    cases meaning
    with_unfolding_all exact float_binary_simd_chosen_pure floats vector occurrence laws .F32 .MAX offset laneIndex bits x y z memory
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure234 = some op at meaning
    cases meaning
    with_unfolding_all exact float_binary_simd_chosen_pure floats vector occurrence laws .F32 .PMIN offset laneIndex bits x y z memory
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure235 = some op at meaning
    cases meaning
    with_unfolding_all exact float_binary_simd_chosen_pure floats vector occurrence laws .F32 .PMAX offset laneIndex bits x y z memory
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure236 = some op at meaning
    cases meaning
    with_unfolding_all exact float_unary_simd_chosen_pure floats vector occurrence laws .F64 .ABS offset laneIndex bits x y z memory
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure237 = some op at meaning
    cases meaning
    with_unfolding_all exact float_unary_simd_chosen_pure floats vector occurrence laws .F64 .NEG offset laneIndex bits x y z memory
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure239 = some op at meaning
    cases meaning
    with_unfolding_all exact float_unary_simd_chosen_pure floats vector occurrence laws .F64 .SQRT offset laneIndex bits x y z memory
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure240 = some op at meaning
    cases meaning
    with_unfolding_all exact float_binary_simd_chosen_pure floats vector occurrence laws .F64 .ADD offset laneIndex bits x y z memory
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure241 = some op at meaning
    cases meaning
    with_unfolding_all exact float_binary_simd_chosen_pure floats vector occurrence laws .F64 .SUB offset laneIndex bits x y z memory
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure242 = some op at meaning
    cases meaning
    with_unfolding_all exact float_binary_simd_chosen_pure floats vector occurrence laws .F64 .MUL offset laneIndex bits x y z memory
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure243 = some op at meaning
    cases meaning
    with_unfolding_all exact float_binary_simd_chosen_pure floats vector occurrence laws .F64 .DIV offset laneIndex bits x y z memory
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure244 = some op at meaning
    cases meaning
    with_unfolding_all exact float_binary_simd_chosen_pure floats vector occurrence laws .F64 .MIN offset laneIndex bits x y z memory
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure245 = some op at meaning
    cases meaning
    with_unfolding_all exact float_binary_simd_chosen_pure floats vector occurrence laws .F64 .MAX offset laneIndex bits x y z memory
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure246 = some op at meaning
    cases meaning
    with_unfolding_all exact float_binary_simd_chosen_pure floats vector occurrence laws .F64 .PMIN offset laneIndex bits x y z memory
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure247 = some op at meaning
    cases meaning
    with_unfolding_all exact float_binary_simd_chosen_pure floats vector occurrence laws .F64 .PMAX offset laneIndex bits x y z memory
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure248 = some op at meaning
    cases meaning
    with_unfolding_all exact trunc_sat_simd_chosen_pure floats vector occurrence .F32 true offset laneIndex bits x y z memory
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure249 = some op at meaning
    cases meaning
    with_unfolding_all exact trunc_sat_simd_chosen_pure floats vector occurrence .F32 false offset laneIndex bits x y z memory
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure250 = some op at meaning
    cases meaning
    with_unfolding_all exact convert_integer_simd_chosen_pure floats vector occurrence laws .F32 true offset laneIndex bits x y z memory
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure251 = some op at meaning
    cases meaning
    with_unfolding_all exact convert_integer_simd_chosen_pure floats vector occurrence laws .F32 false offset laneIndex bits x y z memory
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure252 = some op at meaning
    cases meaning
    with_unfolding_all exact trunc_sat_simd_chosen_pure floats vector occurrence .F64 true offset laneIndex bits x y z memory
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure253 = some op at meaning
    cases meaning
    with_unfolding_all exact trunc_sat_simd_chosen_pure floats vector occurrence .F64 false offset laneIndex bits x y z memory
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure254 = some op at meaning
    cases meaning
    with_unfolding_all exact convert_integer_simd_chosen_pure floats vector occurrence laws .F64 true offset laneIndex bits x y z memory
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure255 = some op at meaning
    cases meaning
    with_unfolding_all exact convert_integer_simd_chosen_pure floats vector occurrence laws .F64 false offset laneIndex bits x y z memory


theorem pure_dispatch_chosen {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : Platform.FloatOpsCorrect floats) {choices : Exec.Spec.SourceChoices}
    (vector : choices.vector=Exec.Spec.firstVectorChoice) (occurrence : Nat)
    (opcode : U32) (op : Itasca.Wasm2.Simd.Operation)
    (meaning : Itasca.Wasm2.Simd.pureMeaning opcode.val = some op)
    (offset laneIndex : U32) (bits x y z : U128) (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats opcode offset laneIndex bits x y z memory ⦃ result =>
      ∃ value, result = (.Ok value,memory) ∧ PureChosenEffect choices occurrence op x.bv y.bv z.bv value.bv ⦄ := by
  exact pure_entries_chosen floats laws vector occurrence opcode (Itasca.Wasm2.Simd.pure_bound meaning)
    op meaning offset laneIndex bits x y z memory
end Exec.Interp.Simd
