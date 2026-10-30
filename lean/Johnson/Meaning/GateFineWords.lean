-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/GateFineWords.lean: all_ok of Johnson/Meaning/GateWords.lean anew, from finer
pieces: at every distance a from 0 to 16384 from the tables' middle, the four words of the
verifier's tables SILU and FS (its sigmoid half), made from the power e^(a/256), are the library's
stored words.

By 257 evaluations in Lean's kernel, each in a module of its own
(Johnson/Meaning/GatePiece/P000.lean to P256.lean), some seconds and below 0.8 GB of the process's
own memory a module; they build side by side.
  pieces_ok: the test holds at every piece. all_ok_fine: stepOK at every distance: the statement of
    all_ok, letter for letter.
-/
import Johnson.Meaning.GatePiece.P000
import Johnson.Meaning.GatePiece.P001
import Johnson.Meaning.GatePiece.P002
import Johnson.Meaning.GatePiece.P003
import Johnson.Meaning.GatePiece.P004
import Johnson.Meaning.GatePiece.P005
import Johnson.Meaning.GatePiece.P006
import Johnson.Meaning.GatePiece.P007
import Johnson.Meaning.GatePiece.P008
import Johnson.Meaning.GatePiece.P009
import Johnson.Meaning.GatePiece.P010
import Johnson.Meaning.GatePiece.P011
import Johnson.Meaning.GatePiece.P012
import Johnson.Meaning.GatePiece.P013
import Johnson.Meaning.GatePiece.P014
import Johnson.Meaning.GatePiece.P015
import Johnson.Meaning.GatePiece.P016
import Johnson.Meaning.GatePiece.P017
import Johnson.Meaning.GatePiece.P018
import Johnson.Meaning.GatePiece.P019
import Johnson.Meaning.GatePiece.P020
import Johnson.Meaning.GatePiece.P021
import Johnson.Meaning.GatePiece.P022
import Johnson.Meaning.GatePiece.P023
import Johnson.Meaning.GatePiece.P024
import Johnson.Meaning.GatePiece.P025
import Johnson.Meaning.GatePiece.P026
import Johnson.Meaning.GatePiece.P027
import Johnson.Meaning.GatePiece.P028
import Johnson.Meaning.GatePiece.P029
import Johnson.Meaning.GatePiece.P030
import Johnson.Meaning.GatePiece.P031
import Johnson.Meaning.GatePiece.P032
import Johnson.Meaning.GatePiece.P033
import Johnson.Meaning.GatePiece.P034
import Johnson.Meaning.GatePiece.P035
import Johnson.Meaning.GatePiece.P036
import Johnson.Meaning.GatePiece.P037
import Johnson.Meaning.GatePiece.P038
import Johnson.Meaning.GatePiece.P039
import Johnson.Meaning.GatePiece.P040
import Johnson.Meaning.GatePiece.P041
import Johnson.Meaning.GatePiece.P042
import Johnson.Meaning.GatePiece.P043
import Johnson.Meaning.GatePiece.P044
import Johnson.Meaning.GatePiece.P045
import Johnson.Meaning.GatePiece.P046
import Johnson.Meaning.GatePiece.P047
import Johnson.Meaning.GatePiece.P048
import Johnson.Meaning.GatePiece.P049
import Johnson.Meaning.GatePiece.P050
import Johnson.Meaning.GatePiece.P051
import Johnson.Meaning.GatePiece.P052
import Johnson.Meaning.GatePiece.P053
import Johnson.Meaning.GatePiece.P054
import Johnson.Meaning.GatePiece.P055
import Johnson.Meaning.GatePiece.P056
import Johnson.Meaning.GatePiece.P057
import Johnson.Meaning.GatePiece.P058
import Johnson.Meaning.GatePiece.P059
import Johnson.Meaning.GatePiece.P060
import Johnson.Meaning.GatePiece.P061
import Johnson.Meaning.GatePiece.P062
import Johnson.Meaning.GatePiece.P063
import Johnson.Meaning.GatePiece.P064
import Johnson.Meaning.GatePiece.P065
import Johnson.Meaning.GatePiece.P066
import Johnson.Meaning.GatePiece.P067
import Johnson.Meaning.GatePiece.P068
import Johnson.Meaning.GatePiece.P069
import Johnson.Meaning.GatePiece.P070
import Johnson.Meaning.GatePiece.P071
import Johnson.Meaning.GatePiece.P072
import Johnson.Meaning.GatePiece.P073
import Johnson.Meaning.GatePiece.P074
import Johnson.Meaning.GatePiece.P075
import Johnson.Meaning.GatePiece.P076
import Johnson.Meaning.GatePiece.P077
import Johnson.Meaning.GatePiece.P078
import Johnson.Meaning.GatePiece.P079
import Johnson.Meaning.GatePiece.P080
import Johnson.Meaning.GatePiece.P081
import Johnson.Meaning.GatePiece.P082
import Johnson.Meaning.GatePiece.P083
import Johnson.Meaning.GatePiece.P084
import Johnson.Meaning.GatePiece.P085
import Johnson.Meaning.GatePiece.P086
import Johnson.Meaning.GatePiece.P087
import Johnson.Meaning.GatePiece.P088
import Johnson.Meaning.GatePiece.P089
import Johnson.Meaning.GatePiece.P090
import Johnson.Meaning.GatePiece.P091
import Johnson.Meaning.GatePiece.P092
import Johnson.Meaning.GatePiece.P093
import Johnson.Meaning.GatePiece.P094
import Johnson.Meaning.GatePiece.P095
import Johnson.Meaning.GatePiece.P096
import Johnson.Meaning.GatePiece.P097
import Johnson.Meaning.GatePiece.P098
import Johnson.Meaning.GatePiece.P099
import Johnson.Meaning.GatePiece.P100
import Johnson.Meaning.GatePiece.P101
import Johnson.Meaning.GatePiece.P102
import Johnson.Meaning.GatePiece.P103
import Johnson.Meaning.GatePiece.P104
import Johnson.Meaning.GatePiece.P105
import Johnson.Meaning.GatePiece.P106
import Johnson.Meaning.GatePiece.P107
import Johnson.Meaning.GatePiece.P108
import Johnson.Meaning.GatePiece.P109
import Johnson.Meaning.GatePiece.P110
import Johnson.Meaning.GatePiece.P111
import Johnson.Meaning.GatePiece.P112
import Johnson.Meaning.GatePiece.P113
import Johnson.Meaning.GatePiece.P114
import Johnson.Meaning.GatePiece.P115
import Johnson.Meaning.GatePiece.P116
import Johnson.Meaning.GatePiece.P117
import Johnson.Meaning.GatePiece.P118
import Johnson.Meaning.GatePiece.P119
import Johnson.Meaning.GatePiece.P120
import Johnson.Meaning.GatePiece.P121
import Johnson.Meaning.GatePiece.P122
import Johnson.Meaning.GatePiece.P123
import Johnson.Meaning.GatePiece.P124
import Johnson.Meaning.GatePiece.P125
import Johnson.Meaning.GatePiece.P126
import Johnson.Meaning.GatePiece.P127
import Johnson.Meaning.GatePiece.P128
import Johnson.Meaning.GatePiece.P129
import Johnson.Meaning.GatePiece.P130
import Johnson.Meaning.GatePiece.P131
import Johnson.Meaning.GatePiece.P132
import Johnson.Meaning.GatePiece.P133
import Johnson.Meaning.GatePiece.P134
import Johnson.Meaning.GatePiece.P135
import Johnson.Meaning.GatePiece.P136
import Johnson.Meaning.GatePiece.P137
import Johnson.Meaning.GatePiece.P138
import Johnson.Meaning.GatePiece.P139
import Johnson.Meaning.GatePiece.P140
import Johnson.Meaning.GatePiece.P141
import Johnson.Meaning.GatePiece.P142
import Johnson.Meaning.GatePiece.P143
import Johnson.Meaning.GatePiece.P144
import Johnson.Meaning.GatePiece.P145
import Johnson.Meaning.GatePiece.P146
import Johnson.Meaning.GatePiece.P147
import Johnson.Meaning.GatePiece.P148
import Johnson.Meaning.GatePiece.P149
import Johnson.Meaning.GatePiece.P150
import Johnson.Meaning.GatePiece.P151
import Johnson.Meaning.GatePiece.P152
import Johnson.Meaning.GatePiece.P153
import Johnson.Meaning.GatePiece.P154
import Johnson.Meaning.GatePiece.P155
import Johnson.Meaning.GatePiece.P156
import Johnson.Meaning.GatePiece.P157
import Johnson.Meaning.GatePiece.P158
import Johnson.Meaning.GatePiece.P159
import Johnson.Meaning.GatePiece.P160
import Johnson.Meaning.GatePiece.P161
import Johnson.Meaning.GatePiece.P162
import Johnson.Meaning.GatePiece.P163
import Johnson.Meaning.GatePiece.P164
import Johnson.Meaning.GatePiece.P165
import Johnson.Meaning.GatePiece.P166
import Johnson.Meaning.GatePiece.P167
import Johnson.Meaning.GatePiece.P168
import Johnson.Meaning.GatePiece.P169
import Johnson.Meaning.GatePiece.P170
import Johnson.Meaning.GatePiece.P171
import Johnson.Meaning.GatePiece.P172
import Johnson.Meaning.GatePiece.P173
import Johnson.Meaning.GatePiece.P174
import Johnson.Meaning.GatePiece.P175
import Johnson.Meaning.GatePiece.P176
import Johnson.Meaning.GatePiece.P177
import Johnson.Meaning.GatePiece.P178
import Johnson.Meaning.GatePiece.P179
import Johnson.Meaning.GatePiece.P180
import Johnson.Meaning.GatePiece.P181
import Johnson.Meaning.GatePiece.P182
import Johnson.Meaning.GatePiece.P183
import Johnson.Meaning.GatePiece.P184
import Johnson.Meaning.GatePiece.P185
import Johnson.Meaning.GatePiece.P186
import Johnson.Meaning.GatePiece.P187
import Johnson.Meaning.GatePiece.P188
import Johnson.Meaning.GatePiece.P189
import Johnson.Meaning.GatePiece.P190
import Johnson.Meaning.GatePiece.P191
import Johnson.Meaning.GatePiece.P192
import Johnson.Meaning.GatePiece.P193
import Johnson.Meaning.GatePiece.P194
import Johnson.Meaning.GatePiece.P195
import Johnson.Meaning.GatePiece.P196
import Johnson.Meaning.GatePiece.P197
import Johnson.Meaning.GatePiece.P198
import Johnson.Meaning.GatePiece.P199
import Johnson.Meaning.GatePiece.P200
import Johnson.Meaning.GatePiece.P201
import Johnson.Meaning.GatePiece.P202
import Johnson.Meaning.GatePiece.P203
import Johnson.Meaning.GatePiece.P204
import Johnson.Meaning.GatePiece.P205
import Johnson.Meaning.GatePiece.P206
import Johnson.Meaning.GatePiece.P207
import Johnson.Meaning.GatePiece.P208
import Johnson.Meaning.GatePiece.P209
import Johnson.Meaning.GatePiece.P210
import Johnson.Meaning.GatePiece.P211
import Johnson.Meaning.GatePiece.P212
import Johnson.Meaning.GatePiece.P213
import Johnson.Meaning.GatePiece.P214
import Johnson.Meaning.GatePiece.P215
import Johnson.Meaning.GatePiece.P216
import Johnson.Meaning.GatePiece.P217
import Johnson.Meaning.GatePiece.P218
import Johnson.Meaning.GatePiece.P219
import Johnson.Meaning.GatePiece.P220
import Johnson.Meaning.GatePiece.P221
import Johnson.Meaning.GatePiece.P222
import Johnson.Meaning.GatePiece.P223
import Johnson.Meaning.GatePiece.P224
import Johnson.Meaning.GatePiece.P225
import Johnson.Meaning.GatePiece.P226
import Johnson.Meaning.GatePiece.P227
import Johnson.Meaning.GatePiece.P228
import Johnson.Meaning.GatePiece.P229
import Johnson.Meaning.GatePiece.P230
import Johnson.Meaning.GatePiece.P231
import Johnson.Meaning.GatePiece.P232
import Johnson.Meaning.GatePiece.P233
import Johnson.Meaning.GatePiece.P234
import Johnson.Meaning.GatePiece.P235
import Johnson.Meaning.GatePiece.P236
import Johnson.Meaning.GatePiece.P237
import Johnson.Meaning.GatePiece.P238
import Johnson.Meaning.GatePiece.P239
import Johnson.Meaning.GatePiece.P240
import Johnson.Meaning.GatePiece.P241
import Johnson.Meaning.GatePiece.P242
import Johnson.Meaning.GatePiece.P243
import Johnson.Meaning.GatePiece.P244
import Johnson.Meaning.GatePiece.P245
import Johnson.Meaning.GatePiece.P246
import Johnson.Meaning.GatePiece.P247
import Johnson.Meaning.GatePiece.P248
import Johnson.Meaning.GatePiece.P249
import Johnson.Meaning.GatePiece.P250
import Johnson.Meaning.GatePiece.P251
import Johnson.Meaning.GatePiece.P252
import Johnson.Meaning.GatePiece.P253
import Johnson.Meaning.GatePiece.P254
import Johnson.Meaning.GatePiece.P255
import Johnson.Meaning.GatePiece.P256

set_option autoImplicit false

namespace Meaning.Gate

open OnBytes.Model.Layer (fxOne)
open Meaning.Rope (xAt)

/-- The test holds at every piece. -/
theorem pieces_ok : ∀ k, k < 257 → pieceOK k = true
  | 0, _ => piece_0
  | 1, _ => piece_1
  | 2, _ => piece_2
  | 3, _ => piece_3
  | 4, _ => piece_4
  | 5, _ => piece_5
  | 6, _ => piece_6
  | 7, _ => piece_7
  | 8, _ => piece_8
  | 9, _ => piece_9
  | 10, _ => piece_10
  | 11, _ => piece_11
  | 12, _ => piece_12
  | 13, _ => piece_13
  | 14, _ => piece_14
  | 15, _ => piece_15
  | 16, _ => piece_16
  | 17, _ => piece_17
  | 18, _ => piece_18
  | 19, _ => piece_19
  | 20, _ => piece_20
  | 21, _ => piece_21
  | 22, _ => piece_22
  | 23, _ => piece_23
  | 24, _ => piece_24
  | 25, _ => piece_25
  | 26, _ => piece_26
  | 27, _ => piece_27
  | 28, _ => piece_28
  | 29, _ => piece_29
  | 30, _ => piece_30
  | 31, _ => piece_31
  | 32, _ => piece_32
  | 33, _ => piece_33
  | 34, _ => piece_34
  | 35, _ => piece_35
  | 36, _ => piece_36
  | 37, _ => piece_37
  | 38, _ => piece_38
  | 39, _ => piece_39
  | 40, _ => piece_40
  | 41, _ => piece_41
  | 42, _ => piece_42
  | 43, _ => piece_43
  | 44, _ => piece_44
  | 45, _ => piece_45
  | 46, _ => piece_46
  | 47, _ => piece_47
  | 48, _ => piece_48
  | 49, _ => piece_49
  | 50, _ => piece_50
  | 51, _ => piece_51
  | 52, _ => piece_52
  | 53, _ => piece_53
  | 54, _ => piece_54
  | 55, _ => piece_55
  | 56, _ => piece_56
  | 57, _ => piece_57
  | 58, _ => piece_58
  | 59, _ => piece_59
  | 60, _ => piece_60
  | 61, _ => piece_61
  | 62, _ => piece_62
  | 63, _ => piece_63
  | 64, _ => piece_64
  | 65, _ => piece_65
  | 66, _ => piece_66
  | 67, _ => piece_67
  | 68, _ => piece_68
  | 69, _ => piece_69
  | 70, _ => piece_70
  | 71, _ => piece_71
  | 72, _ => piece_72
  | 73, _ => piece_73
  | 74, _ => piece_74
  | 75, _ => piece_75
  | 76, _ => piece_76
  | 77, _ => piece_77
  | 78, _ => piece_78
  | 79, _ => piece_79
  | 80, _ => piece_80
  | 81, _ => piece_81
  | 82, _ => piece_82
  | 83, _ => piece_83
  | 84, _ => piece_84
  | 85, _ => piece_85
  | 86, _ => piece_86
  | 87, _ => piece_87
  | 88, _ => piece_88
  | 89, _ => piece_89
  | 90, _ => piece_90
  | 91, _ => piece_91
  | 92, _ => piece_92
  | 93, _ => piece_93
  | 94, _ => piece_94
  | 95, _ => piece_95
  | 96, _ => piece_96
  | 97, _ => piece_97
  | 98, _ => piece_98
  | 99, _ => piece_99
  | 100, _ => piece_100
  | 101, _ => piece_101
  | 102, _ => piece_102
  | 103, _ => piece_103
  | 104, _ => piece_104
  | 105, _ => piece_105
  | 106, _ => piece_106
  | 107, _ => piece_107
  | 108, _ => piece_108
  | 109, _ => piece_109
  | 110, _ => piece_110
  | 111, _ => piece_111
  | 112, _ => piece_112
  | 113, _ => piece_113
  | 114, _ => piece_114
  | 115, _ => piece_115
  | 116, _ => piece_116
  | 117, _ => piece_117
  | 118, _ => piece_118
  | 119, _ => piece_119
  | 120, _ => piece_120
  | 121, _ => piece_121
  | 122, _ => piece_122
  | 123, _ => piece_123
  | 124, _ => piece_124
  | 125, _ => piece_125
  | 126, _ => piece_126
  | 127, _ => piece_127
  | 128, _ => piece_128
  | 129, _ => piece_129
  | 130, _ => piece_130
  | 131, _ => piece_131
  | 132, _ => piece_132
  | 133, _ => piece_133
  | 134, _ => piece_134
  | 135, _ => piece_135
  | 136, _ => piece_136
  | 137, _ => piece_137
  | 138, _ => piece_138
  | 139, _ => piece_139
  | 140, _ => piece_140
  | 141, _ => piece_141
  | 142, _ => piece_142
  | 143, _ => piece_143
  | 144, _ => piece_144
  | 145, _ => piece_145
  | 146, _ => piece_146
  | 147, _ => piece_147
  | 148, _ => piece_148
  | 149, _ => piece_149
  | 150, _ => piece_150
  | 151, _ => piece_151
  | 152, _ => piece_152
  | 153, _ => piece_153
  | 154, _ => piece_154
  | 155, _ => piece_155
  | 156, _ => piece_156
  | 157, _ => piece_157
  | 158, _ => piece_158
  | 159, _ => piece_159
  | 160, _ => piece_160
  | 161, _ => piece_161
  | 162, _ => piece_162
  | 163, _ => piece_163
  | 164, _ => piece_164
  | 165, _ => piece_165
  | 166, _ => piece_166
  | 167, _ => piece_167
  | 168, _ => piece_168
  | 169, _ => piece_169
  | 170, _ => piece_170
  | 171, _ => piece_171
  | 172, _ => piece_172
  | 173, _ => piece_173
  | 174, _ => piece_174
  | 175, _ => piece_175
  | 176, _ => piece_176
  | 177, _ => piece_177
  | 178, _ => piece_178
  | 179, _ => piece_179
  | 180, _ => piece_180
  | 181, _ => piece_181
  | 182, _ => piece_182
  | 183, _ => piece_183
  | 184, _ => piece_184
  | 185, _ => piece_185
  | 186, _ => piece_186
  | 187, _ => piece_187
  | 188, _ => piece_188
  | 189, _ => piece_189
  | 190, _ => piece_190
  | 191, _ => piece_191
  | 192, _ => piece_192
  | 193, _ => piece_193
  | 194, _ => piece_194
  | 195, _ => piece_195
  | 196, _ => piece_196
  | 197, _ => piece_197
  | 198, _ => piece_198
  | 199, _ => piece_199
  | 200, _ => piece_200
  | 201, _ => piece_201
  | 202, _ => piece_202
  | 203, _ => piece_203
  | 204, _ => piece_204
  | 205, _ => piece_205
  | 206, _ => piece_206
  | 207, _ => piece_207
  | 208, _ => piece_208
  | 209, _ => piece_209
  | 210, _ => piece_210
  | 211, _ => piece_211
  | 212, _ => piece_212
  | 213, _ => piece_213
  | 214, _ => piece_214
  | 215, _ => piece_215
  | 216, _ => piece_216
  | 217, _ => piece_217
  | 218, _ => piece_218
  | 219, _ => piece_219
  | 220, _ => piece_220
  | 221, _ => piece_221
  | 222, _ => piece_222
  | 223, _ => piece_223
  | 224, _ => piece_224
  | 225, _ => piece_225
  | 226, _ => piece_226
  | 227, _ => piece_227
  | 228, _ => piece_228
  | 229, _ => piece_229
  | 230, _ => piece_230
  | 231, _ => piece_231
  | 232, _ => piece_232
  | 233, _ => piece_233
  | 234, _ => piece_234
  | 235, _ => piece_235
  | 236, _ => piece_236
  | 237, _ => piece_237
  | 238, _ => piece_238
  | 239, _ => piece_239
  | 240, _ => piece_240
  | 241, _ => piece_241
  | 242, _ => piece_242
  | 243, _ => piece_243
  | 244, _ => piece_244
  | 245, _ => piece_245
  | 246, _ => piece_246
  | 247, _ => piece_247
  | 248, _ => piece_248
  | 249, _ => piece_249
  | 250, _ => piece_250
  | 251, _ => piece_251
  | 252, _ => piece_252
  | 253, _ => piece_253
  | 254, _ => piece_254
  | 255, _ => piece_255
  | 256, _ => piece_256
  | n + 257, h => absurd h (by omega)

/-- The four comparisons hold at every distance. -/
theorem all_ok_fine {a : ℕ} (ha : a ≤ 16384) : stepOK a (xAt (stepOf 8) a fxOne) = true := by
  have hk : a / 64 < 257 := by omega
  have c := pieces_ok (a / 64) hk
  unfold pieceOK at c
  rw [xAtS_eq] at c
  have hj : a % 64 < (if (a / 64 == 256) = true then 1 else 64) := by
    by_cases h16 : a / 64 = 256
    · rw [if_pos (by rw [h16]; rfl)]
      omega
    · rw [if_neg (by simpa using h16)]
      exact Nat.mod_lt _ (by decide)
  have y := gateOK_spec _ _ _ _ c (a % 64) hj
  rw [← xAt_add, Nat.div_add_mod] at y
  exact y

#print axioms pieces_ok
#print axioms all_ok_fine

end Meaning.Gate
