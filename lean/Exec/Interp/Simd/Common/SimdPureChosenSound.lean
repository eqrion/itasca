import Exec.Interp.Simd.Common.SimdPureChosenRelation
import Exec.Interp.Simd.Common.SimdChosenPrimitives

/-! Selected-policy correspondence for the independent finite SIMD source table.
Neutral entries share equality transport; numeric entries keep their explicit
primitive laws, and absent source entries remain visible. -/
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- Reuse the checked implementation primitive and independently named source
meaning. Only the repeated equality transport is automated. -/
local macro "neutral_simd_case " primitive:term " => " expected:term : tactic =>
  `(tactic| (
    apply ($primitive)
    intro op meaning x y z
    change some $expected = some op at meaning
    cases meaning
    rfl))

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
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_14 floats)) => Itasca.Wasm2.Simd.pure14
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_15 floats)) => Itasca.Wasm2.Simd.pure15
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_16 floats)) => Itasca.Wasm2.Simd.pure16
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_17 floats)) => Itasca.Wasm2.Simd.pure17
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_18 floats)) => Itasca.Wasm2.Simd.pure18
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_19 floats)) => Itasca.Wasm2.Simd.pure19
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_20 floats)) => Itasca.Wasm2.Simd.pure20
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
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_35 floats)) => Itasca.Wasm2.Simd.pure35
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_36 floats)) => Itasca.Wasm2.Simd.pure36
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_37 floats)) => Itasca.Wasm2.Simd.pure37
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_38 floats)) => Itasca.Wasm2.Simd.pure38
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_39 floats)) => Itasca.Wasm2.Simd.pure39
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_40 floats)) => Itasca.Wasm2.Simd.pure40
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_41 floats)) => Itasca.Wasm2.Simd.pure41
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_42 floats)) => Itasca.Wasm2.Simd.pure42
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_43 floats)) => Itasca.Wasm2.Simd.pure43
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_44 floats)) => Itasca.Wasm2.Simd.pure44
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_45 floats)) => Itasca.Wasm2.Simd.pure45
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_46 floats)) => Itasca.Wasm2.Simd.pure46
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_47 floats)) => Itasca.Wasm2.Simd.pure47
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_48 floats)) => Itasca.Wasm2.Simd.pure48
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_49 floats)) => Itasca.Wasm2.Simd.pure49
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_50 floats)) => Itasca.Wasm2.Simd.pure50
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_51 floats)) => Itasca.Wasm2.Simd.pure51
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_52 floats)) => Itasca.Wasm2.Simd.pure52
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_53 floats)) => Itasca.Wasm2.Simd.pure53
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_54 floats)) => Itasca.Wasm2.Simd.pure54
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_55 floats)) => Itasca.Wasm2.Simd.pure55
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_56 floats)) => Itasca.Wasm2.Simd.pure56
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_57 floats)) => Itasca.Wasm2.Simd.pure57
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_58 floats)) => Itasca.Wasm2.Simd.pure58
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_59 floats)) => Itasca.Wasm2.Simd.pure59
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_60 floats)) => Itasca.Wasm2.Simd.pure60
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_61 floats)) => Itasca.Wasm2.Simd.pure61
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_62 floats)) => Itasca.Wasm2.Simd.pure62
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_63 floats)) => Itasca.Wasm2.Simd.pure63
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_64 floats)) => Itasca.Wasm2.Simd.pure64
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_65 floats)) => Itasca.Wasm2.Simd.pure65
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_66 floats)) => Itasca.Wasm2.Simd.pure66
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_67 floats)) => Itasca.Wasm2.Simd.pure67
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_68 floats)) => Itasca.Wasm2.Simd.pure68
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_69 floats)) => Itasca.Wasm2.Simd.pure69
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_70 floats)) => Itasca.Wasm2.Simd.pure70
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_71 floats)) => Itasca.Wasm2.Simd.pure71
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_72 floats)) => Itasca.Wasm2.Simd.pure72
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_73 floats)) => Itasca.Wasm2.Simd.pure73
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_74 floats)) => Itasca.Wasm2.Simd.pure74
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_75 floats)) => Itasca.Wasm2.Simd.pure75
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_76 floats)) => Itasca.Wasm2.Simd.pure76
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_77 floats)) => Itasca.Wasm2.Simd.pure77
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_78 floats)) => Itasca.Wasm2.Simd.pure78
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_79 floats)) => Itasca.Wasm2.Simd.pure79
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_80 floats)) => Itasca.Wasm2.Simd.pure80
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_81 floats)) => Itasca.Wasm2.Simd.pure81
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_82 floats)) => Itasca.Wasm2.Simd.pure82
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_83 floats)) => Itasca.Wasm2.Simd.pure83
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
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_96 floats)) => Itasca.Wasm2.Simd.pure96
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_97 floats)) => Itasca.Wasm2.Simd.pure97
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_98 floats)) => Itasca.Wasm2.Simd.pure98
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_99 floats)) => Itasca.Wasm2.Simd.pure99
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_100 floats)) => Itasca.Wasm2.Simd.pure100
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_101 floats)) => Itasca.Wasm2.Simd.pure101
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_102 floats)) => Itasca.Wasm2.Simd.pure102
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
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_107 floats)) => Itasca.Wasm2.Simd.pure107
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_108 floats)) => Itasca.Wasm2.Simd.pure108
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_109 floats)) => Itasca.Wasm2.Simd.pure109
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_110 floats)) => Itasca.Wasm2.Simd.pure110
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_111 floats)) => Itasca.Wasm2.Simd.pure111
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_112 floats)) => Itasca.Wasm2.Simd.pure112
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_113 floats)) => Itasca.Wasm2.Simd.pure113
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_114 floats)) => Itasca.Wasm2.Simd.pure114
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_115 floats)) => Itasca.Wasm2.Simd.pure115
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure116 = some op at meaning
    cases meaning
    with_unfolding_all exact float_unary_simd_chosen_pure floats vector occurrence laws .F64 .CEIL offset laneIndex bits x y z memory
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure117 = some op at meaning
    cases meaning
    with_unfolding_all exact float_unary_simd_chosen_pure floats vector occurrence laws .F64 .FLOOR offset laneIndex bits x y z memory
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_118 floats)) => Itasca.Wasm2.Simd.pure118
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_119 floats)) => Itasca.Wasm2.Simd.pure119
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_120 floats)) => Itasca.Wasm2.Simd.pure120
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_121 floats)) => Itasca.Wasm2.Simd.pure121
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure122 = some op at meaning
    cases meaning
    with_unfolding_all exact float_unary_simd_chosen_pure floats vector occurrence laws .F64 .TRUNC offset laneIndex bits x y z memory
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_123 floats)) => Itasca.Wasm2.Simd.pure123
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_124 floats)) => Itasca.Wasm2.Simd.pure124
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_125 floats)) => Itasca.Wasm2.Simd.pure125
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_126 floats)) => Itasca.Wasm2.Simd.pure126
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_127 floats)) => Itasca.Wasm2.Simd.pure127
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_128 floats)) => Itasca.Wasm2.Simd.pure128
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_129 floats)) => Itasca.Wasm2.Simd.pure129
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_130 floats)) => Itasca.Wasm2.Simd.pure130
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_131 floats)) => Itasca.Wasm2.Simd.pure131
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_132 floats)) => Itasca.Wasm2.Simd.pure132
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_133 floats)) => Itasca.Wasm2.Simd.pure133
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_134 floats)) => Itasca.Wasm2.Simd.pure134
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
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_139 floats)) => Itasca.Wasm2.Simd.pure139
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_140 floats)) => Itasca.Wasm2.Simd.pure140
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_141 floats)) => Itasca.Wasm2.Simd.pure141
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_142 floats)) => Itasca.Wasm2.Simd.pure142
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_143 floats)) => Itasca.Wasm2.Simd.pure143
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_144 floats)) => Itasca.Wasm2.Simd.pure144
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_145 floats)) => Itasca.Wasm2.Simd.pure145
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_146 floats)) => Itasca.Wasm2.Simd.pure146
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_147 floats)) => Itasca.Wasm2.Simd.pure147
  · intro op meaning offset laneIndex bits x y z memory
    change some Itasca.Wasm2.Simd.pure148 = some op at meaning
    cases meaning
    with_unfolding_all exact float_unary_simd_chosen_pure floats vector occurrence laws .F64 .NEAREST offset laneIndex bits x y z memory
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_149 floats)) => Itasca.Wasm2.Simd.pure149
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_150 floats)) => Itasca.Wasm2.Simd.pure150
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_151 floats)) => Itasca.Wasm2.Simd.pure151
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_152 floats)) => Itasca.Wasm2.Simd.pure152
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_153 floats)) => Itasca.Wasm2.Simd.pure153
  · intro op meaning
    change none = some op at meaning
    contradiction
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_155 floats)) => Itasca.Wasm2.Simd.pure155
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_156 floats)) => Itasca.Wasm2.Simd.pure156
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_157 floats)) => Itasca.Wasm2.Simd.pure157
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_158 floats)) => Itasca.Wasm2.Simd.pure158
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_159 floats)) => Itasca.Wasm2.Simd.pure159
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_160 floats)) => Itasca.Wasm2.Simd.pure160
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_161 floats)) => Itasca.Wasm2.Simd.pure161
  · intro op meaning
    change none = some op at meaning
    contradiction
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_163 floats)) => Itasca.Wasm2.Simd.pure163
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_164 floats)) => Itasca.Wasm2.Simd.pure164
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
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_171 floats)) => Itasca.Wasm2.Simd.pure171
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_172 floats)) => Itasca.Wasm2.Simd.pure172
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_173 floats)) => Itasca.Wasm2.Simd.pure173
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_174 floats)) => Itasca.Wasm2.Simd.pure174
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_177 floats)) => Itasca.Wasm2.Simd.pure177
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_181 floats)) => Itasca.Wasm2.Simd.pure181
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_182 floats)) => Itasca.Wasm2.Simd.pure182
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_183 floats)) => Itasca.Wasm2.Simd.pure183
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_184 floats)) => Itasca.Wasm2.Simd.pure184
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_185 floats)) => Itasca.Wasm2.Simd.pure185
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_186 floats)) => Itasca.Wasm2.Simd.pure186
  · intro op meaning
    change none = some op at meaning
    contradiction
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_188 floats)) => Itasca.Wasm2.Simd.pure188
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_189 floats)) => Itasca.Wasm2.Simd.pure189
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_190 floats)) => Itasca.Wasm2.Simd.pure190
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_191 floats)) => Itasca.Wasm2.Simd.pure191
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_192 floats)) => Itasca.Wasm2.Simd.pure192
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_193 floats)) => Itasca.Wasm2.Simd.pure193
  · intro op meaning
    change none = some op at meaning
    contradiction
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_195 floats)) => Itasca.Wasm2.Simd.pure195
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_196 floats)) => Itasca.Wasm2.Simd.pure196
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
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_203 floats)) => Itasca.Wasm2.Simd.pure203
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_204 floats)) => Itasca.Wasm2.Simd.pure204
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_205 floats)) => Itasca.Wasm2.Simd.pure205
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_206 floats)) => Itasca.Wasm2.Simd.pure206
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_209 floats)) => Itasca.Wasm2.Simd.pure209
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_213 floats)) => Itasca.Wasm2.Simd.pure213
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_214 floats)) => Itasca.Wasm2.Simd.pure214
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_215 floats)) => Itasca.Wasm2.Simd.pure215
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_216 floats)) => Itasca.Wasm2.Simd.pure216
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_217 floats)) => Itasca.Wasm2.Simd.pure217
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_218 floats)) => Itasca.Wasm2.Simd.pure218
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_219 floats)) => Itasca.Wasm2.Simd.pure219
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_220 floats)) => Itasca.Wasm2.Simd.pure220
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_221 floats)) => Itasca.Wasm2.Simd.pure221
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_222 floats)) => Itasca.Wasm2.Simd.pure222
  · neutral_simd_case (pure_entry_chosen_neutral floats vector occurrence _ (pure_entry_223 floats)) => Itasca.Wasm2.Simd.pure223
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
