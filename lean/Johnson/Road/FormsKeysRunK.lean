-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/FormsKeysRunK.lean: the runs of Johnson/Road/FormsKeysRun8.lean and
Johnson/Road/FormsKeysRunT.lean at the numbers of two examples of the prover's, typed into this
file, through the verifier's own reader of the configuration files.

Everything but three theorems is a run. A line "#guard" is evaluated when this file is compiled, by
Lean's interpreter, and the compilation fails if the value is not true. It is no theorem, and it
says nothing of other numbers.

The files. prover/examples/target_small_f2 and prover/examples/target_full_f2 each hold a parameter
file policy.txt and a scale file KL.bin. The lists here were written from these files: the lines of
the two texts (linesKS, linesKF) and the 32-bit words (scalesKS, scalesKF). EVERY RUN HERE IS AT
THESE TYPED BYTES. No Lean code compares them with the files on the disk: the runs are at the
examples only if sha256sum of the four files begins 3c7ff5cb, f8829d72 (small), ce9e126b, 1c319116
(full-size), as that of the typed bytes does. Whether the tree that you hold has these four files
with these sums is tested by nothing here: sha256sum tells. Another small example, stored elsewhere
in that tree, may have other bytes. They hold public parameters and scales, no weights.

What is run at both examples, on the two files' bytes:
 1. publicOf (OnBytes/Model/VerifyPublic.lean) returns, with no layout file: so every step of the
    verifier's public part has returned, among them all that the head of
    Johnson/Road/FormsKeysRun.lean lists as not run: the scan of the parameter file and the tests
    before and behind the layout, planesHeld, tableHeld on the three tables, whose digests are lines
    of the file, hPar, the head's and attention's layouts, Pub.of, and the plans with their
    comparisons. What "no layout file" leaves out: publicOf reads that file in hPar alone, which
    hashes it and whose result publicOf drops; without the file zeros stand for its digest. So what
    publicOf returns is the same with the file; not run is only that the digest of the examples'
    own layout.txt is computed without a refusal,
 2. the shape that the verifier reads from the file is the shape written here by hand (hKS, hKF),
    field by field; these two have the switches (a theorem: switchesK),
 3. the file's eight lines of calls name the families of the library's calls, in its order,
 4. the columns that the layout's segments list are the library's pos (at the full-size example on a
    sample of the entries: see below); the logarithms of the numbers of columns, the verifier's and
    the library's; and call by call whether the least number of columns that the file asks for is at
    most the library's number,
 5. the library's test LawfulW on the words of each layer, read as wordsAt reads them,
 6. the layers without the rotary step are the same for the verifier and the library (rotaryK),
 7. the padding keys, as numbers and as words of the base field, and all rows of all eight tables,
    against the library's tables at its reference functions tbRef,
 8. the sizes of the matrices against the library's (sizesK),
 9. in every group of layers the record of the smallness test in the verifier's own plan has the
    list of matrices of tailsOf, NM is its length, and the reads are as long as the plan says: this
    gives the hypotheses htm and hNM of laid1_of_run (Johnson/Road/FormsKeysTab.lean)
    and of the theorems that stand on it; and the plan's array of reads has a
    number of columns that is not 0 and is the length of the reads. That array and number are
    compared with nothing in the smallness test's own claims.
At the small example besides, in both groups, in an environment with the plan's own array of reads
and its number of columns, and with made-up points that are tied as the lookup ties them (lookR8):
 10. CallD.padding and the marks of weighedOf against the library's isPad, on all columns,
 11. the tests on the calls' points; line for every segment on every layer where it exists;
    weighedOf and joinPart for every call; pointsOf and funsOf,
 12. the order of the entries of every family of tables (g1T), and their rows, columns and parts
    against the library's featAt and afPart (g2T), with the plan's own record.
At the full-size example besides: the words of the scale file are the library's reference scales in
every layer (refScalesK: thin evidence on the reading of the file, as its docstring says); the
verifier's rotary table, all 131,072 words, is the library's C and S of layer 0 plus 4096 (ropeK);
the sizes of point 8 are compared at the library's reference sizes Dim.ref themselves; and in the
first and the last group, in an environment with the plan's own array of reads and number of
columns, weighedOf returns and agrees with CallD.padding, the tests on the points pass, and pointsOf
and funsOf return.
Why layer 0 is enough for the rotary table: the library's C and S depend on the layer only through
the question whether it has the rotary step, and point 6 compares that for every layer. A control:
in layer 3, which has none, most words differ. The small example has another base of the angles, so
its rotary table is not compared.
Two more comparisons with the library, at no example's file:
 13. the reading of a scale file: wordsAt against the library's own reading KLFile.words, on a
    made-up file of 696 words that all differ (dictK),
 14. the eight fields of the library's record Dim.OK, one by one (okT).

What comes out.
 - No number differs but one: at the small example the file asks for at least 2^12
   columns, and the library's calls 0, 5, 6 and 7 have 2^11, 2^11, 2^10 and 2^10. So the hypothesis
   hfl of joinPart_keyVec (Johnson/Road/FormsKeysKV.lean) fails for these four
   calls there. At the full-size example it holds for all eight.
 - LawfulW fails in all 8 layers of the small example and holds in all 48 of the full-size one. The
   library's test is written at the reference sizes.
 - Dim.OK holds at the reference sizes. At the small example's sizes dimT two of its fields fail:
   a layer's keys of call 3 do not fit one tree, and the number of trees is no power of two. There
   dimT also takes the library's one number r from the rows of the matrix of counts, 2^13, where the
   library's tables want r = 16.

Theorems: switchesK; sizedKS (Sized and Sized2 of the small example's shape at the sizes dimT);
sizedKF (Sized and Sized2 of the full-size example's shape at Dim.ref).

What is cut at the full-size example. The columns of point 4 are compared at every 61st entry of
each family and at the last. Points 10 and 12, line and joinPart are not run there.

What is made up: every element of the field that stands for a challenge or a point. No proof is made
or checked, no weight is read, and no prover has run.

What is not claimed. Nothing is said of other parameter files. That a shape passes the verifier's
public part says nothing on soundness. Of the file's first 32 lines the functions run here read the
lines sec and work positions and the last number of the line table. The lines record, group and
stages and the other numbers of table pass the reader's tests of form and are read no further:
whether the verifier admits them (Params.sized, Params.configure in OnBytes/Model/VerifyChains.lean)
is not run. The program does not import this file.

Where the guards stand. So that no module costs over a minute of Lean's time, two long guards are
not in this file. The run at the full-size example's two files (publicOf returns; points 5 to 9; "At
the full-size example besides") is the guard of Johnson/Road/FormsKeysRunKFull.lean. The run of
points 5 to 12 at the small example costs some 160 s and is in no file of this library: whoever
wants it evaluates runK (textK linesKS) (wordsK scalesKS). What this head says of these points at
the small example (among them: LawfulW fails in all 8 layers there) is held by no guard of this
library. Points 2 to 4 at both examples (with them: polLayout returns), the files' lengths and
words, 13 and 14 are guards of this file. That publicOf returns at the small example (point 1) is
held by the guards of Johnson/Road/HeadRunK.lean.

-/
import Johnson.Road.FormsKeysRun8
import Johnson.Road.FormsKeysRunT
import OnBytes.Model.VerifyPublic
import Inst.Model.ProgTests

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open OnBytes.Model (Seg CallD PolScan fileWords HTailF2)
open OnBytes.Model.Verify (polLayout publicOf layerShape Public)
open OnBytes.Model.Layer (Env Lay Shape Scales Reads layout scalesOf scalesHeld noWrap readsOf
  tableAsks layTables pointsOf funsOf tailsOf)
open Inst.Model (tbRef)
open Inst.Model (rotaryOff KLFile)
open Inst.Model.FFSeg (Dim Fam fams call ord len LawfulW nFeatMx afCols nCol lRow mZ)

/-! ## The files -/

/-- A text file from its lines, each ended by a line feed. -/
def textK (l : List String) : ByteArray := (String.join (l.map (· ++ "\n"))).toUTF8

/-- A file of 32-bit words, the lowest byte first. -/
def wordsK (l : List ℕ) : ByteArray :=
  ⟨(l.flatMap fun w => [w % 256, w / 256 % 256, w / 65536 % 256, w / 16777216 % 256].map
    (·.toUInt8)).toArray⟩

/-- The lines of the parameter file of the small example. -/
def linesKS : List String :=
  [
   "version H821", "sec 128", "reading 1", "rowcost 1", "slots 64", "answers 1", "record 1",
   "work field 0 0 0", "work sample 0 0 0", "work closeness 0 0 0", "work positions 20 28 32",
   "work smallness 0 0 0", "salt 40", "listed 0", "group link 1 18 17 17 13",
   "stages link 4 3 17 17 3 3 16 16 3 3 15 15 0 0 15 15", "group folded 1 17 15 13 6",
   "stages folded 4 2 14 12 0 0 14 14", "group omega 1 18 14 13 6",
   "stages omega 4 3 14 13 0 0 15 15", "group own 1 18 14 13 8",
   "stages own 4 3 14 13 0 0 15 15", "group once-folded 1 17 15 13 6",
   "stages once-folded 4 2 14 12 0 0 14 14",
   "group once-omega 1 18 14 13 6", "stages once-omega 4 3 14 13 0 0 15 15",
   "group once-own 1 18 14 13 8", "stages once-own 4 3 14 13 0 0 15 15",
   "group once-ranges 1 22 18 16 10",
   "stages once-ranges 4 3 19 17 3 3 17 17 0 0 20 20", "ranges-part 14",
   "table 8 23 524288 65535 0 11", "prof 20", "lt 6", "L 8", "ll 2", "d 512", "H 4", "G 2",
   "dh 128", "f 1024", "fe 512", "NE 4", "V 512", "eps1_lo 1", "eps1_hi 0", "eps2_lo 1",
   "eps2_hi 0", "cs 12", "theta0_lo 10000", "theta0_hi 0", "hq 2", "hv 1", "ho 1", "hgD 1",
   "huD 1", "hdD 1", "hr 1", "ut 1", "la 8", "nmin 20", "D 2048", "tau 128", "lmaf 13", "NAf 3",
   "lmad 12", "NAd 1", "lmar 12", "lmb 13", "lmq 13", "lmx 13", "wb_qk 13", "wb_v 13", "wb_o 13",
   "wb_g 13", "wb_u 13", "wb_gs 13", "wb_us 13", "wb_gr 13", "wb_ur 13", "wb_dn 13", "wb_dnr 13",
   "wb_r 13", "iota_0 0", "iota_1 0", "iota_2 0", "iota_3 1", "iota_4 0", "iota_5 0", "iota_6 0",
   "iota_7 0", "seed_lo 31", "seed_hi 0", "lB 4", "S 12", "rx 8", "kFM 15", "kFD 16", "lmS 11",
   "NAs 1", "lmh 12", "lmo 13", "lmbA 13", "iotaA_0 52", "MF 44", "KF 30", "epsF_lo 1",
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

/-- The words of the scale file of the small example. -/
def scalesKS : List ℕ :=
  [
   29, 29, 17, 7, 9, 13, 9, 44, 30, 44, 30, 12, 1, 29, 29, 17, 7, 9, 13, 9, 44, 30, 44, 30, 12, 1,
   29, 29, 17, 7, 9, 13, 9, 44, 30, 44, 30, 12, 1, 29, 29, 17, 7, 9, 13, 9, 44, 30, 44, 30, 12, 0,
   29, 29, 17, 7, 9, 13, 9, 44, 30, 44, 30, 12, 1, 29, 29, 17, 7, 9, 13, 9, 44, 30, 44, 30, 12, 1,
   29, 29, 17, 7, 9, 13, 9, 44, 30, 44, 30, 12, 1, 29, 29, 17, 7, 9, 13, 9, 44, 30, 44, 30, 12, 0,
   11, 8, 14, 11, 8, 14, 11, 8, 14, 11, 8, 14]

/-- The shape that the small example's parameter file describes, written by hand from its lines. -/
def hKS : Shape :=
  { prof := 4, lt := 6, L := 8, ll := 2, d := 512, H := 4, Gk := 2, dh := 128, f := 1024, fe := 512,
    NE := 4, eps1 := 1, eps2 := 1, epsF := 1, cs := 12, theta0 := 10000, hq := 2, hv := 1, ho := 1,
    hgD := 1, huD := 1, hdD := 1, hr := 1, ut := 1, la := 8, nmin := 20, D := 2048, tau := 128,
    lmaf := 13, NAf := 3, lmad := 12, NAd := 1, lmar := 12, lmb := 13, lmq := 13, lmx := 13,
    wb := Array.replicate 12 13, iota := #[0, 0, 0, 1, 0, 0, 0, 0], seed := 31, gcl := true,
    rcl := true, xl := 5, lidb := 24 }

/-- The lines of the parameter file of the full-size example. -/
def linesKF : List String :=
  [
   "version H821", "sec 128", "reading 1", "rowcost 1", "slots 64", "answers 1", "record 1",
   "work field 0 0 0", "work sample 0 0 0", "work closeness 0 0 0", "work positions 20 28 32",
   "work smallness 0 0 0", "salt 40", "listed 0", "group link 1 23 22 17 13",
   "stages link 4 3 22 17 3 3 19 16 3 3 16 15 4 4 13 13 0 0 15 15", "group folded 1 24 22 13 6",
   "stages folded 5 2 21 12 4 2 17 12 4 2 13 12 0 0 14 14", "group omega 1 22 18 13 6",
   "stages omega 4 3 18 14 4 3 14 13 0 0 15 15", "group own 1 22 18 13 8",
   "stages own 4 3 18 15 3 3 15 14 3 3 13 13 0 0 15 15", "group once-folded 1 24 22 13 6",
   "stages once-folded 5 2 21 12 4 2 17 12 4 2 13 12 0 0 14 14",
   "group once-omega 1 22 18 13 6", "stages once-omega 4 3 18 14 4 3 14 13 0 0 15 15",
   "group once-own 1 22 18 13 8", "stages once-own 4 3 18 15 3 3 15 14 3 3 13 13 0 0 15 15",
   "group once-ranges 1 22 18 16 12",
   "stages once-ranges 4 3 19 17 3 3 17 17 0 0 20 20", "ranges-part 18",
   "table 11 32 402653184 44040191 0 18", "prof 20", "lt 10", "L 48", "ll 2", "d 5120",
   "H 40", "G 8", "dh 128", "f 16384", "fe 8192", "NE 128", "V 202048", "eps1_lo 53687",
   "eps1_hi 0", "eps2_lo 53687", "eps2_hi 0", "cs 12", "theta0_lo 500000", "theta0_hi 0", "hq 2",
   "hv 1", "ho 1", "hgD 1", "huD 1", "hdD 1", "hr 1", "ut 1", "la 16", "nmin 20", "D 2048",
   "tau 128", "lmaf 16", "NAf 3", "lmad 15", "NAd 1", "lmar 13", "lmb 16", "lmq 16", "lmx 16",
   "wb_qk 13", "wb_v 13", "wb_o 13", "wb_g 13", "wb_u 13", "wb_gs 13", "wb_us 13", "wb_gr 13",
   "wb_ur 13", "wb_dn 13", "wb_dnr 13", "wb_r 13", "iota_0 1", "iota_1 1", "iota_2 1", "iota_3 2",
   "iota_4 1", "iota_5 1", "iota_6 0", "iota_7 0", "seed_lo 1", "seed_hi 0", "lB 6", "S 12",
   "rx 8", "kFM 15", "kFD 16", "lmS 16", "NAs 1", "lmh 13", "lmo 16", "lmbA 14", "iotaA_0 57",
   "MF 44", "KF 30", "epsF_lo 53687", "epsF_hi 0", "toksrc 1", "lmhf 16", "NHf 4", "lmhd 14",
   "lmhr 13", "lmbH 15", "wb_emb 21", "wb_head 13", "iotaH_0 1", "iotaH_1 1", "iotaH_2 1",
   "iotaH_3 0", "iotaH_4 0", "iotaH_5 0", "C 256", "theta 256", "cap 0", "s 15", "sh 8", "sT 4",
   "F 24", "lidb 28", "nminH 27", "rcl 1", "gcl 1", "xl 5", "tsilu0 2048398297",
   "tsilu1 192427613", "tsilu2 2862900154", "tsilu3 2853881485", "tsilu4 2797826050",
   "tsilu5 1420723544", "tsilu6 3686369553", "tsilu7 2593882461", "tsig0 1965976300",
   "tsig1 2359599336", "tsig2 2246761285", "tsig3 2426172242", "tsig4 3869868832",
   "tsig5 310049175", "tsig6 339407438", "tsig7 2601410768", "trope0 786409086",
   "trope1 1563166184", "trope2 1100635208", "trope3 2272768750", "trope4 1260813977",
   "trope5 3744463197", "trope6 3300849996", "trope7 4050797957", "texp0 3648852807",
   "texp1 2402568834", "texp2 4186852988", "texp3 523559909", "texp4 1873895626",
   "texp5 3042864545", "texp6 1726265496", "texp7 165292856", "call R16a R16 G U",
   "call R16b R16 N1 N1H N2 N2H O D V", "call R16c R16 QK QKH XR LR LT DD",
   "call R8 R8 GH UH OH DH VH ROW LH SEL L3 G0", "call FC FC CN1 CN2 CQK CV CLR",
   "call FS FS MR CG", "call FL FL F", "call R16d R16 UT", "callA KR KR RM RD",
   "callA KFD KFD FM FD", "callA R16 R16 WL IX", "callA WH WH WH", "callH R16a R16 NF NFH HD0",
   "callH R16b R16 HD1", "callH R8 R8 ROW HD2", "callH FEa FE HE0", "callH FEb FE HE1",
   "callH FC FC CNF"]

/-- The words of the scale file of the full-size example. -/
def scalesKF : List ℕ :=
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

/-- The shape that the full-size example's parameter file describes, written by hand from its
lines. -/
def hKF : Shape :=
  { prof := 4, lt := 10, L := 48, ll := 2, d := 5120, H := 40, Gk := 8, dh := 128, f := 16384,
    fe := 8192, NE := 128, eps1 := 53687, eps2 := 53687, epsF := 53687, cs := 12, theta0 := 500000,
    hq := 2, hv := 1, ho := 1, hgD := 1, huD := 1, hdD := 1, hr := 1, ut := 1, la := 16, nmin := 20,
    D := 2048, tau := 128, lmaf := 16, NAf := 3, lmad := 15, NAd := 1, lmar := 13, lmb := 16,
    lmq := 16, lmx := 16, wb := Array.replicate 12 13, iota := #[1, 1, 1, 2, 1, 1, 0, 0], seed := 1,
    gcl := true, rcl := true, xl := 5, lidb := 28 }

/-- All fields of a shape, for a comparison. -/
def fieldsK (h : Shape) : List ℕ × Array ℕ × Array ℕ × Bool × Bool :=
  ([h.prof, h.lt, h.L, h.ll, h.d, h.H, h.Gk, h.dh, h.f, h.fe, h.NE, h.eps1, h.eps2, h.epsF, h.cs,
    h.theta0, h.hq, h.hv, h.ho, h.hgD, h.huD, h.hdD, h.hr, h.ut, h.la, h.nmin, h.D, h.tau, h.lmaf,
    h.NAf, h.lmad, h.NAd, h.lmar, h.lmb, h.lmq, h.lmx, h.seed, h.xl, h.lidb, h.eg, h.smax],
   h.wb, h.iota, h.gcl, h.rcl)

/-! ## What is evaluated -/

/-- As columnsR8, but of the entries of a family only every step-th, from the first on, and the
last. -/
def columnsK (step : ℕ) (D : Dim) (calls : Array CallD) : Bool :=
  famsR.all fun s =>
    let g := calls[(call s).val]!.segs[ord s]!
    g.name == segName s && g.n == len D s && g.pos.size == len D s &&
      ((List.range (len D s / step + 1)).map (· * step) ++ [len D s - 1]).all fun x =>
        decide (len D s ≤ x) || g.pos[x]! == Inst.Model.FFSeg.pos D s x

/-- The verifier's scan of a parameter file and the layout of a layer sub-proof, compared with a
shape written by hand and with the library's calls: whether the shape is h; namesR8, columnsK,
logsR8 and floorR8 at the library's sizes dimOf h. Refuses where the verifier refuses. -/
def scanK (pol : ByteArray) (h : Shape) (step : ℕ) :
    Except String (Bool × Bool × Bool × List (ℕ × ℕ) × List Bool) := do
  let (P, y) ← polLayout pol
  let D := dimOf h
  pure (fieldsK (layerShape P) == fieldsK h, namesR8 y.calls, columnsK step D y.calls,
    logsR8 D y.calls, floorR8 h D)

/-- For each layer of the model: whether the library's test on the words of one layer passes on the
layer's words of the scale file, read as wordsAt reads them. -/
def lawfulK (h : Shape) (sc : Scales) : List Bool :=
  (List.range h.L).map fun L => decide (LawfulW (wordsAt h sc L))

/-- The scales of one layer as a list of 18 numbers: the ten shifts, three numbers for each of the
two normalisations, the rows of the exponential's table, and the shift sh. -/
def scaleListK (s : Inst.Model.LayerScale) : List ℤ :=
  [s.kq, s.kk, s.kv, s.ko, s.kg, s.ku, s.kd, s.kr, s.kg', s.ku', s.n1.M, s.n1.K, s.n1.eps, s.n2.M,
   s.n2.K, s.n2.eps, s.expRows, s.sh]

/-- Whether in every layer of the model the words of the scale file, read as wordsAt reads them, are
the scales of the library's reference parameters. This says little on how wordsAt reads a file. Of
the 18 numbers one is written into wordsAt in every layer and three more in the even layers, and two
come from the parameter file. The full-size example's file has one record for all layers, in which
values repeat, so a reading that swapped two equal words or took another layer's record would pass
too. dictK is the test of the reading. -/
def refScalesK (h : Shape) (sc : Scales) : Bool :=
  (List.range h.L).all fun L => scaleListK (wordsAt h sc L) == scaleListK Inst.Model.ppref.scale

/-- The reading of a scale file: wordsAt against the library's own reading of the file (KLFile.words
in Inst/Model/ProgTests.lean), on a made-up file for the full-size example's shape whose 696 words
all differ: word number i is 1000 + i. True if the 18 numbers agree in all 48 layers. For records
that are cut from the file by the verifier's Scales.kl and Scales.klM this is a theorem, for every
file (wordsAt_eq, Johnson/Road/FormsKeysWords.lean). Here the records are
written by hand from the library's description of the flat file, so the run covers that cutting too.
-/
def dictK : Bool :=
  match scalesOf hKF ((Array.range 696).map (· + 1000)) with
  | .error _ => false
  | .ok sc =>
    let f : KLFile :=
      { lay := fun L i => 1000 + 13 * L.val + i.val,
        moe := fun e j => 1000 + 624 + 3 * e.val + j.val,
        eps1 := hKF.eps1, eps2 := hKF.eps2, MF := 0, KF := 0, epsF := 0, C := 0, theta := 0,
        cap := 0 }
    (List.finRange 48).all fun L =>
      scaleListK (wordsAt hKF sc L.val) == scaleListK (f.words L).scale

/-- Whether the layers without the rotary step are the same: for the verifier those whose record in
the scale file ends in the word 0, for the library the layers L with L mod 4 = 3. -/
def rotaryK (h : Shape) (sc : Scales) : Bool :=
  (List.range h.L).all fun L => (sc.klRp L == 0) == decide (rotaryOff L)

/-- A rotary table for T positions and 64 pairs of channels beside the library's reference functions
C and S in layer L: the table's length, and the numbers of pairs (position i, pair of channels j) at
which the word number 64 i + j is not C L i j + 4096, and the word number 64 T + 64 i + j is not
S L i j + 4096. -/
def ropeK (a : Array ℕ) (T L : ℕ) : ℕ × ℕ × ℕ :=
  (a.size,
   ((List.range (T * 64)).filter fun x =>
      (a.getD x 0 : ℤ) != tbRef.C L (x / 64) (x % 64) + 4096).length,
   ((List.range (T * 64)).filter fun x =>
      (a.getD (T * 64 + x) 0 : ℤ) != tbRef.S L (x / 64) (x % 64) + 4096).length)

/-- The sizes, the verifier's against the library's, as g3T of Johnson/Road/FormsKeysRunT.lean
compares them, on a given layout. -/
def sizesK (y : Lay) (D : Dim) : List Bool :=
  [y.feat.toList == [nFeatMx D .af, nFeatMx D .ad, nFeatMx D .ar, nFeatMx D .qa],
   y.h.xl * y.h.d == nFeatMx D .xin, y.h.xl * y.h.d == nFeatMx D .xout,
   y.kcol.getD 0 0 == afCols D,
   (List.range 4).all fun m => partsM y m * colsM y m == nCol D (mxOf m),
   y.kxb == nCol D .xin && y.kxb == nCol D .xout,
   (List.range 6).all fun m => rowsM y m == 2 ^ lRow D (mxOf m),
   rowsT y == mZ D]

/-- What is evaluated in one group of layers, on all that the verifier computes from the
configuration files (X). First, on the group's own plan: whether the smallness test's list of
matrices is that of tailsOf, whether it has the same rows and columns, whether NM is its length,
whether the reads have the length that the plan says, and whether the number of columns of the
plan's array of reads is not 0 and is that length. Then, in an environment with the plan's own
array of reads and number of columns, taken as the check takes them (hearOwn in
OnBytes/Model/Layer.lean), and the points of lookR8: marksR8; testsR8; the two
numbers of linesR; joinsR; the numbers of points and of tables. Then g1T and g2T of
Johnson/Road/FormsKeysRunT.lean with the plan's own record of the smallness test. -/
def groupK (X : Public) (pad : Array (Array Bool)) (D2 : Dim) (g : ℕ) : Except String
    ((Bool × Bool × Bool × Bool × Bool) × (Bool × Bool × (ℕ × ℕ) × Bool × ℕ × ℕ) × Bool × Bool) :=
    do
  let y := X.layers.y
  let rd := X.layers.rd
  let ms := ((tailsOf y).getD g {}).mats
  match X.G[g]?, layTables (matsR y g) (tableAsks y rd g) 0 with
  | some hp, some r =>
    match hp.tl.ix.U.getD 2 none with
    | none => throw "no array of reads"
    | some iU3 =>
      let K3 := ((hp.Fp.trees[iU3]?).map (·.K)).getD 0
      let H := heardR8 y rd g
      let v : Env := { y, sc := X.layers.sc, g, iU3, K3, tab := r.1, zk := H.fo.zk }
      let pts := pointsOf y H { r := elemsR 3100 rd.muH } (some { r := elemsR 3200 rd.muH2 })
      let funs := pts.bind fun p => funsOf y H.fo p r.2.1
      let fs := (r.1.zip r.2.1).map fun x => (x.1, x.2.1, x.2.2)
      pure ((hp.tl.mats == ms, (hp.tl.mats.map fun M => (M.m, M.k)) == matsR y g,
          hp.tl.NM == hp.tl.mats.size, r.2.2 == hp.nU.getD 2 0,
          K3 != 0 && K3 == hp.nU.getD 2 0),
        (marksR8 pad v, testsR8 v H, linesR v, joinsR v, (pts.map (·.length)).getD 0,
          (funs.map (·.size)).getD 0),
        g1T y hp.tl (matsR y g) fs, g2T D2 (fun _ => true) y hp.tl (matsR y g) fs)
  | _, _ => throw "no plan or no tables"

/-- The whole run at an example's own files. pol, KL: the parameter file and the scale file. First:
paddingR8 at the library's sizes dimOf; lawfulK; rotaryK; padKeysR8, padWordsR8 and tablesR8 at the
library's reference tables; sizesK at the sizes dimT. Then groupK for each group. Refuses where the
verifier refuses. -/
def runK (pol KL : ByteArray) : Except String
    ((Bool × List Bool × Bool × List (ℤ × ℤ) × Bool × List (Bool × ℕ) × List Bool) ×
      List ((Bool × Bool × Bool × Bool × Bool) × (Bool × Bool × (ℕ × ℕ) × Bool × ℕ × ℕ) ×
        Bool × Bool)) := do
  let X ← publicOf pol KL none
  let y := X.layers.y
  let pad := libPadR8 (dimOf y.h) y.Lam y.calls
  let r ← (List.range y.NGr).mapM (groupK X pad (dimT y.h))
  pure ((paddingR8 pad y.Lam y.calls, lawfulK y.h X.layers.sc, rotaryK y.h X.layers.sc,
    padKeysR8 y tbRef,
    padWordsR8 y tbRef, tablesR8 y tbRef, sizesK y (dimT y.h)), r)

/-- The array of reads and the number of its columns in the plan of group g, taken as the check
takes them (hearOwn in OnBytes/Model/Layer.lean); none if there is no such plan or array. -/
def readsK (X : Public) (g : ℕ) : Option (ℕ × ℕ) :=
  (X.G[g]?).bind fun hp => (hp.tl.ix.U.getD 2 none).map fun iU3 =>
    (iU3, ((hp.Fp.trees[iU3]?).map (·.K)).getD 0)

/-- In one group, in an environment with the plan's own array of reads and number of columns, at the
points of lookR8: whether weighedOf returns marks for every call and marks a column exactly if the
verifier's own rule CallD.padding does not call it padding; testsR8; the numbers of points and of
tables that pointsOf and funsOf return (0 if none). -/
def pointsK (X : Public) (g : ℕ) : Bool × Bool × ℕ × ℕ :=
  let y := X.layers.y
  let rd := X.layers.rd
  match layTables (matsR y g) (tableAsks y rd g) 0, readsK X g with
  | some r, some (iU3, K3) =>
    let H := heardR8 y rd g
    let v : Env := { y, sc := X.layers.sc, g, iU3, K3, tab := r.1, zk := H.fo.zk }
    let pts := pointsOf y H { r := elemsR 3100 rd.muH } (some { r := elemsR 3200 rd.muH2 })
    let funs := pts.bind fun p => funsOf y H.fo p r.2.1
    (y.calls.all fun cd =>
        match v.weighedOf cd with
        | none => false
        | some w =>
          w == (Array.range (y.Lam * cd.J)).map fun i => !cd.padding (i / cd.J) (i % cd.J),
      testsR8 v H, (pts.map (·.length)).getD 0, (funs.map (·.size)).getD 0)
  | _, _ => (false, false, 0, 0)

/-- The lighter run at the full-size example's files, on all that the verifier computes from them:
lawfulK; refScalesK; rotaryK; ropeK of the verifier's rotary table in the layers 0 and 3; padKeysR8,
padWordsR8 and tablesR8 at the library's reference tables; sizesK at the library's reference sizes;
for each group whether the plan's own list of matrices is that of tailsOf, NM its length, the reads
as long as the plan says, and the number of columns of the plan's array of reads not 0 and that
length; pointsK in the first and in the last group. Refuses where the verifier refuses. -/
def runKF (pol KL : ByteArray) : Except String
    (List Bool × Bool × Bool × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) × List (ℤ × ℤ) × Bool × List (Bool × ℕ) ×
      List Bool × List (Bool × Bool × Bool × Bool) × List (Bool × Bool × ℕ × ℕ)) := do
  let X ← publicOf pol KL none
  let y := X.layers.y
  let rd := X.layers.rd
  let gs := (List.range y.NGr).map fun g =>
    match X.G[g]?, layTables (matsR y g) (tableAsks y rd g) 0 with
    | some hp, some r => (hp.tl.mats == ((tailsOf y).getD g {}).mats,
        hp.tl.NM == hp.tl.mats.size, r.2.2 == hp.nU.getD 2 0,
        match readsK X g with
        | some (_, K3) => K3 != 0 && K3 == hp.nU.getD 2 0
        | none => false)
    | _, _ => (false, false, false, false)
  pure (lawfulK y.h X.layers.sc, refScalesK y.h X.layers.sc, rotaryK y.h X.layers.sc,
    ropeK X.layers.rope y.T 0, ropeK X.layers.rope y.T 3,
    padKeysR8 y tbRef, padWordsR8 y tbRef, tablesR8 y tbRef, sizesK y Dim.ref, gs,
    [0, y.NGr - 1].map (pointsK X))

/-- The two shapes have the switches and digit forms for which the library has keys. -/
theorem switchesK : Switches hKS ∧ Switches hKF :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- The sizes dimT agree with the small example's shape: the nine numbers of Sized and the seven
equations of Sized2. -/
theorem sizedKS : Sized hKS (dimT hKS) ∧ Sized2 hKS (dimT hKS) :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- The library's reference sizes agree with the full-size example's shape: the nine numbers of
Sized and the seven equations of Sized2. -/
theorem sizedKF : Sized hKF Dim.ref ∧ Sized2 hKF Dim.ref :=
  ⟨sized_ref rfl rfl rfl rfl rfl rfl rfl rfl rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- The padding keys of the eight calls, each twice. -/
def keysK : List (ℤ × ℤ) :=
  ([0, 0, 0, 0, 2 ^ 15 + 2 ^ 39, 2 ^ 15 + 2 ^ 28 + 2 ^ 40, 2 ^ 15 + 2 ^ 40, 0] : List ℤ).map
    fun k => (k, k)

/-! ## The run: the small example -/

/- the files' lengths, and the words read back -/
#guard ((textK linesKS).size, (wordsK scalesKS).size,
  fileWords (wordsK scalesKS) == scalesKS.toArray) == (2479, 464, true)

/- 2 to 4 -/
#guard (match scanK (textK linesKS) hKS 1 with
  | .ok r => r == (true, true, true,
      [(12, 11), (12, 12), (12, 12), (13, 13), (12, 12), (12, 11), (12, 10), (12, 10)],
      [false, true, true, true, true, false, false, false])
  | .error _ => false)

/-! ## The run: the full-size example -/

/- the files' lengths, and the words read back -/
#guard ((textK linesKF).size, (wordsK scalesKF).size,
  fileWords (wordsK scalesKF) == scalesKF.toArray) == (2629, 2784, true)

/- 2 to 4, the columns at every 61st entry -/
#guard (match scanK (textK linesKF) hKF 61 with
  | .ok r => r == (true, true, true,
      [(15, 15), (15, 15), (15, 15), (16, 16), (15, 15), (15, 15), (14, 14), (14, 14)],
      List.replicate 8 true)
  | .error _ => false)

/-! ## The run: two more comparisons with the library -/

/- the reading of a scale file -/
#guard dictK

/- the eight fields of the library's Dim.OK, one by one (okT of Johnson/Road/FormsKeysRunT.lean): at
the small example's sizes dimT two fail; at the reference sizes all hold -/
#guard okT (dimT hKS) == [true, true, true, true, true, false, true, false]
#guard okT Dim.ref == List.replicate 8 true

#print axioms switchesK
#print axioms sizedKS
#print axioms sizedKF

end OnBytes.Road
