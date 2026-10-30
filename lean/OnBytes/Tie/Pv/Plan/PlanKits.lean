-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Plan/PlanKits.lean: the parameter file and the scale file of two example
configurations, written out.

The repository's folders prover/examples/target_small_f2 (64 tokens, 8 layers) and
prover/examples/target_full_f2 (1,024 tokens, 48 layers) each hold a parameter file policy.txt, a
scale file KL.bin and a layout file layout.txt. They are not in this library. This file holds the
lines of the two parameter files and the 32-bit words of the two scale files. The layout files are
in PlanLayoutSmall.lean and PlanLayoutFull.lean. All hold public parameters and scales, no weights.

Main names: textOf, wordsFile, policyS, scalesS, policyF, scalesF.
Limits: no Lean code compares these lists with the files of the repository. The lengths are tested
in TestPlanSizesSmall.lean and
TestPlanSizesFull.lean. No theorem
is stated.
The program does not import this file.

-/
import OnBytes.Base

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Plan

/-- A text file from its lines, each ended by a line feed. -/
def textOf (l : List String) : ByteArray := (String.join (l.map (· ++ "\n"))).toUTF8

/-- A file of 32-bit words, the lowest byte first. -/
def wordsFile (l : List Nat) : ByteArray :=
  ⟨(l.flatMap fun w => [w % 256, w / 256 % 256, w / 65536 % 256, w / 16777216 % 256].map
    (·.toUInt8)).toArray⟩

/-- The small example: the lines of the parameter file. -/
def policyS : List String :=
  [
   "version H821", "sec 128", "reading 1", "rowcost 1", "slots 64", "answers 1", "record 1",
   "work field 0 0 0", "work sample 0 0 0", "work closeness 0 0 0", "work positions 20 28 32",
   "work smallness 0 0 0", "salt 40", "listed 0", "group link 1 18 17 17 13",
   "stages link 4 3 17 17 3 3 16 16 3 3 15 15 0 0 15 15", "group folded 1 17 15 13 6",
   "stages folded 4 2 14 12 0 0 14 14", "group omega 1 18 14 13 6",
   "stages omega 4 3 14 13 0 0 15 15", "group own 1 18 14 13 8", "stages own 4 3 14 13 0 0 15 15",
   "group once-folded 1 17 15 13 6", "stages once-folded 4 2 14 12 0 0 14 14",
   "group once-omega 1 18 14 13 6", "stages once-omega 4 3 14 13 0 0 15 15",
   "group once-own 1 18 14 13 8", "stages once-own 4 3 14 13 0 0 15 15",
   "group once-ranges 1 22 18 16 10", "stages once-ranges 4 3 19 17 3 3 17 17 0 0 20 20",
   "ranges-part 14", "table 8 23 524288 65535 0 11", "prof 20", "lt 6", "L 8", "ll 2", "d 512",
   "H 4", "G 2", "dh 128", "f 1024", "fe 512", "NE 4", "V 512", "eps1_lo 1", "eps1_hi 0",
   "eps2_lo 1", "eps2_hi 0", "cs 12", "theta0_lo 10000", "theta0_hi 0", "hq 2", "hv 1", "ho 1",
   "hgD 1", "huD 1", "hdD 1", "hr 1", "ut 1", "la 8", "nmin 20", "D 2048", "tau 128", "lmaf 13",
   "NAf 3", "lmad 12", "NAd 1", "lmar 12", "lmb 13", "lmq 13", "lmx 13", "wb_qk 13", "wb_v 13",
   "wb_o 13", "wb_g 13", "wb_u 13", "wb_gs 13", "wb_us 13", "wb_gr 13", "wb_ur 13", "wb_dn 13",
   "wb_dnr 13", "wb_r 13", "iota_0 0", "iota_1 0", "iota_2 0", "iota_3 1", "iota_4 0", "iota_5 0",
   "iota_6 0", "iota_7 0", "seed_lo 31", "seed_hi 0", "lB 4", "S 12", "rx 8", "kFM 15", "kFD 16",
   "lmS 11", "NAs 1", "lmh 12", "lmo 13", "lmbA 13", "iotaA_0 52", "MF 44", "KF 30", "epsF_lo 1",
   "epsF_hi 0", "toksrc 1", "lmhf 14", "NHf 1", "lmhd 12", "lmhr 12", "lmbH 13", "wb_emb 21",
   "wb_head 13", "iotaH_0 0", "iotaH_1 0", "iotaH_2 0", "iotaH_3 0", "iotaH_4 0", "iotaH_5 0",
   "C 256", "theta 256", "cap 0", "s 16", "sh 8", "sT 4", "F 24", "lidb 24", "rcl 1", "gcl 1",
   "xl 5", "tsilu0 2048398297", "tsilu1 192427613", "tsilu2 2862900154", "tsilu3 2853881485",
   "tsilu4 2797826050", "tsilu5 1420723544", "tsilu6 3686369553", "tsilu7 2593882461",
   "tsig0 1965976300", "tsig1 2359599336", "tsig2 2246761285", "tsig3 2426172242",
   "tsig4 3869868832", "tsig5 310049175", "tsig6 339407438", "tsig7 2601410768",
   "trope0 2232934348", "trope1 2156588140", "trope2 3599599331", "trope3 498649753",
   "trope4 3675316650", "trope5 2999201840", "trope6 1537898906", "trope7 2900737701",
   "texp0 3648852807", "texp1 2402568834", "texp2 4186852988", "texp3 523559909",
   "texp4 1873895626", "texp5 3042864545", "texp6 1726265496", "texp7 165292856",
   "call R16a R16 G U", "call R16b R16 N1 N1H N2 N2H O D V", "call R16c R16 QK QKH XR LR LT DD",
   "call R8 R8 GH UH OH DH VH ROW LH SEL L3 G0", "call FC FC CN1 CN2 CQK CV CLR",
   "call FS FS MR CG", "call FL FL F", "call R16d R16 UT", "callA KR KR RM RD",
   "callA KFD KFD FM FD", "callA R16 R16 WL IX", "callA WH WH WH", "callH R16a R16 NF NFH HD0",
   "callH R16b R16 HD1", "callH R8 R8 ROW HD2", "callH FEa FE HE0", "callH FEb FE HE1",
   "callH FC FC CNF"]

/-- The small example: the words of the scale file. -/
def scalesS : List Nat :=
  [
   29, 29, 17, 7, 9, 13, 9, 44, 30, 44, 30, 12, 1, 29, 29, 17, 7, 9, 13, 9, 44, 30, 44, 30, 12, 1,
   29, 29, 17, 7, 9, 13, 9, 44, 30, 44, 30, 12, 1, 29, 29, 17, 7, 9, 13, 9, 44, 30, 44, 30, 12, 0,
   29, 29, 17, 7, 9, 13, 9, 44, 30, 44, 30, 12, 1, 29, 29, 17, 7, 9, 13, 9, 44, 30, 44, 30, 12, 1,
   29, 29, 17, 7, 9, 13, 9, 44, 30, 44, 30, 12, 1, 29, 29, 17, 7, 9, 13, 9, 44, 30, 44, 30, 12, 0,
   11, 8, 14, 11, 8, 14, 11, 8, 14, 11, 8, 14]

/-- The full-size example: the lines of the parameter file. -/
def policyF : List String :=
  [
   "version H821", "sec 128", "reading 1", "rowcost 1", "slots 64", "answers 1", "record 1",
   "work field 0 0 0", "work sample 0 0 0", "work closeness 0 0 0", "work positions 20 28 32",
   "work smallness 0 0 0", "salt 40", "listed 0", "group link 1 23 22 17 13",
   "stages link 4 3 22 17 3 3 19 16 3 3 16 15 4 4 13 13 0 0 15 15", "group folded 1 24 22 13 6",
   "stages folded 5 2 21 12 4 2 17 12 4 2 13 12 0 0 14 14", "group omega 1 22 18 13 6",
   "stages omega 4 3 18 14 4 3 14 13 0 0 15 15", "group own 1 22 18 13 8",
   "stages own 4 3 18 15 3 3 15 14 3 3 13 13 0 0 15 15", "group once-folded 1 24 22 13 6",
   "stages once-folded 5 2 21 12 4 2 17 12 4 2 13 12 0 0 14 14", "group once-omega 1 22 18 13 6",
   "stages once-omega 4 3 18 14 4 3 14 13 0 0 15 15", "group once-own 1 22 18 13 8",
   "stages once-own 4 3 18 15 3 3 15 14 3 3 13 13 0 0 15 15", "group once-ranges 1 22 18 16 12",
   "stages once-ranges 4 3 19 17 3 3 17 17 0 0 20 20", "ranges-part 18",
   "table 11 32 402653184 44040191 0 18", "prof 20", "lt 10", "L 48", "ll 2", "d 5120", "H 40",
   "G 8", "dh 128", "f 16384", "fe 8192", "NE 128", "V 202048", "eps1_lo 53687", "eps1_hi 0",
   "eps2_lo 53687", "eps2_hi 0", "cs 12", "theta0_lo 500000", "theta0_hi 0", "hq 2", "hv 1",
   "ho 1", "hgD 1", "huD 1", "hdD 1", "hr 1", "ut 1", "la 16", "nmin 20", "D 2048", "tau 128",
   "lmaf 16", "NAf 3", "lmad 15", "NAd 1", "lmar 13", "lmb 16", "lmq 16", "lmx 16", "wb_qk 13",
   "wb_v 13", "wb_o 13", "wb_g 13", "wb_u 13", "wb_gs 13", "wb_us 13", "wb_gr 13", "wb_ur 13",
   "wb_dn 13", "wb_dnr 13", "wb_r 13", "iota_0 1", "iota_1 1", "iota_2 1", "iota_3 2", "iota_4 1",
   "iota_5 1", "iota_6 0", "iota_7 0", "seed_lo 1", "seed_hi 0", "lB 6", "S 12", "rx 8", "kFM 15",
   "kFD 16", "lmS 16", "NAs 1", "lmh 13", "lmo 16", "lmbA 14", "iotaA_0 57", "MF 44", "KF 30",
   "epsF_lo 53687", "epsF_hi 0", "toksrc 1", "lmhf 16", "NHf 4", "lmhd 14", "lmhr 13", "lmbH 15",
   "wb_emb 21", "wb_head 13", "iotaH_0 1", "iotaH_1 1", "iotaH_2 1", "iotaH_3 0", "iotaH_4 0",
   "iotaH_5 0", "C 256", "theta 256", "cap 0", "s 15", "sh 8", "sT 4", "F 24", "lidb 28",
   "nminH 27", "rcl 1", "gcl 1", "xl 5", "tsilu0 2048398297", "tsilu1 192427613",
   "tsilu2 2862900154", "tsilu3 2853881485", "tsilu4 2797826050", "tsilu5 1420723544",
   "tsilu6 3686369553", "tsilu7 2593882461", "tsig0 1965976300", "tsig1 2359599336",
   "tsig2 2246761285", "tsig3 2426172242", "tsig4 3869868832", "tsig5 310049175",
   "tsig6 339407438", "tsig7 2601410768", "trope0 786409086", "trope1 1563166184",
   "trope2 1100635208", "trope3 2272768750", "trope4 1260813977", "trope5 3744463197",
   "trope6 3300849996", "trope7 4050797957", "texp0 3648852807", "texp1 2402568834",
   "texp2 4186852988", "texp3 523559909", "texp4 1873895626", "texp5 3042864545",
   "texp6 1726265496", "texp7 165292856", "call R16a R16 G U", "call R16b R16 N1 N1H N2 N2H O D V",
   "call R16c R16 QK QKH XR LR LT DD", "call R8 R8 GH UH OH DH VH ROW LH SEL L3 G0",
   "call FC FC CN1 CN2 CQK CV CLR", "call FS FS MR CG", "call FL FL F", "call R16d R16 UT",
   "callA KR KR RM RD", "callA KFD KFD FM FD", "callA R16 R16 WL IX", "callA WH WH WH",
   "callH R16a R16 NF NFH HD0", "callH R16b R16 HD1", "callH R8 R8 ROW HD2", "callH FEa FE HE0",
   "callH FEb FE HE1", "callH FC FC CNF"]

/-- The full-size example: the words of the scale file. -/
def scalesF : List Nat :=
  [
   29, 29, 17, 17, 16, 20, 19, 44, 30, 44, 30, 8, 1, 29, 29, 17, 17, 16, 20, 19, 44, 30, 44, 30, 8,
   1, 29, 29, 17, 17, 16, 20, 19, 44, 30, 44, 30, 8, 1, 29, 29, 17, 17, 16, 20, 19, 44, 30, 44, 30,
   8, 0, 29, 29, 17, 17, 16, 20, 19, 44, 30, 44, 30, 8, 1, 29, 29, 17, 17, 16, 20, 19, 44, 30, 44,
   30, 8, 1, 29, 29, 17, 17, 16, 20, 19, 44, 30, 44, 30, 8, 1, 29, 29, 17, 17, 16, 20, 19, 44, 30,
   44, 30, 8, 0, 29, 29, 17, 17, 16, 20, 19, 44, 30, 44, 30, 8, 1, 29, 29, 17, 17, 16, 20, 19, 44,
   30, 44, 30, 8, 1, 29, 29, 17, 17, 16, 20, 19, 44, 30, 44, 30, 8, 1, 29, 29, 17, 17, 16, 20, 19,
   44, 30, 44, 30, 8, 0, 29, 29, 17, 17, 16, 20, 19, 44, 30, 44, 30, 8, 1, 29, 29, 17, 17, 16, 20,
   19, 44, 30, 44, 30, 8, 1, 29, 29, 17, 17, 16, 20, 19, 44, 30, 44, 30, 8, 1, 29, 29, 17, 17, 16,
   20, 19, 44, 30, 44, 30, 8, 0, 29, 29, 17, 17, 16, 20, 19, 44, 30, 44, 30, 8, 1, 29, 29, 17, 17,
   16, 20, 19, 44, 30, 44, 30, 8, 1, 29, 29, 17, 17, 16, 20, 19, 44, 30, 44, 30, 8, 1, 29, 29, 17,
   17, 16, 20, 19, 44, 30, 44, 30, 8, 0, 29, 29, 17, 17, 16, 20, 19, 44, 30, 44, 30, 8, 1, 29, 29,
   17, 17, 16, 20, 19, 44, 30, 44, 30, 8, 1, 29, 29, 17, 17, 16, 20, 19, 44, 30, 44, 30, 8, 1, 29,
   29, 17, 17, 16, 20, 19, 44, 30, 44, 30, 8, 0, 29, 29, 17, 17, 16, 20, 19, 44, 30, 44, 30, 8, 1,
   29, 29, 17, 17, 16, 20, 19, 44, 30, 44, 30, 8, 1, 29, 29, 17, 17, 16, 20, 19, 44, 30, 44, 30, 8,
   1, 29, 29, 17, 17, 16, 20, 19, 44, 30, 44, 30, 8, 0, 29, 29, 17, 17, 16, 20, 19, 44, 30, 44, 30,
   8, 1, 29, 29, 17, 17, 16, 20, 19, 44, 30, 44, 30, 8, 1, 29, 29, 17, 17, 16, 20, 19, 44, 30, 44,
   30, 8, 1, 29, 29, 17, 17, 16, 20, 19, 44, 30, 44, 30, 8, 0, 29, 29, 17, 17, 16, 20, 19, 44, 30,
   44, 30, 8, 1, 29, 29, 17, 17, 16, 20, 19, 44, 30, 44, 30, 8, 1, 29, 29, 17, 17, 16, 20, 19, 44,
   30, 44, 30, 8, 1, 29, 29, 17, 17, 16, 20, 19, 44, 30, 44, 30, 8, 0, 29, 29, 17, 17, 16, 20, 19,
   44, 30, 44, 30, 8, 1, 29, 29, 17, 17, 16, 20, 19, 44, 30, 44, 30, 8, 1, 29, 29, 17, 17, 16, 20,
   19, 44, 30, 44, 30, 8, 1, 29, 29, 17, 17, 16, 20, 19, 44, 30, 44, 30, 8, 0, 29, 29, 17, 17, 16,
   20, 19, 44, 30, 44, 30, 8, 1, 29, 29, 17, 17, 16, 20, 19, 44, 30, 44, 30, 8, 1, 29, 29, 17, 17,
   16, 20, 19, 44, 30, 44, 30, 8, 1, 29, 29, 17, 17, 16, 20, 19, 44, 30, 44, 30, 8, 0, 29, 29, 17,
   17, 16, 20, 19, 44, 30, 44, 30, 8, 1, 29, 29, 17, 17, 16, 20, 19, 44, 30, 44, 30, 8, 1, 29, 29,
   17, 17, 16, 20, 19, 44, 30, 44, 30, 8, 1, 29, 29, 17, 17, 16, 20, 19, 44, 30, 44, 30, 8, 0, 17,
   16, 20, 17, 16, 20, 17, 16, 20, 17, 16, 20, 17, 16, 20, 17, 16, 20, 17, 16, 20, 17, 16, 20, 17,
   16, 20, 17, 16, 20, 17, 16, 20, 17, 16, 20, 17, 16, 20, 17, 16, 20, 17, 16, 20, 17, 16, 20, 17,
   16, 20, 17, 16, 20, 17, 16, 20, 17, 16, 20, 17, 16, 20, 17, 16, 20, 17, 16, 20, 17, 16, 20]

end OnBytes.Tie.Pv.Plan
