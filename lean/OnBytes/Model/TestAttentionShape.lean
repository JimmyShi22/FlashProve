-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestAttentionShape.lean: tests of the shape of the attention sub-proof.

The tests run when this file is compiled. The program does not import this file. Each section below
begins with its own account.
 1. The table of exponentials.
 2. The numbers that depend on the shift.
 3. The group of the lookup calls.
 4. Sizes and rounds at the small configuration.
 5. Pieces, rows of the calls' tables, the cover.
 6. The functions on points.
 7. The refusals of shape.
 8. The conditions at their bounds.

Not tested here: the first half of the condition af-no-wrap-N2 (wrapTests), which cannot fail before
its second half. The file holds no theorem. No guard on the refusals of shape reaches what no
configuration reaches (section 7 lists it: two sizes, the lower limit on kFD, the conditions N1, N2,
N5, N6 and N9). The known answers under 3 are copied by hand; nothing compares the copy with
verifier/tests/forest_weights.txt. No file of the repository is read.
-/
import OnBytes.Model.AttentionShape
import OnBytes.Hash.SecondHashFunction
import OnBytes.Params.SubRounds

namespace OnBytes.Attention.Test

/-! ## The table of exponentials

The table of exponentials of OnBytes/Model/AttentionExp.lean at two settings: its length, its
first entries and the sum of its entries. The expected numbers are what the loop of AFork::shape
(verifier/src/vf_attention_shape.h) gives in floating point. At S = 12 and rx = 8 also its digest,
against eight words that are spelled out here. They were taken from the lines texp0 to texp7 of a
parameter file with these two numbers that the C++ verifier did not refuse. The C++ verifier
compares the digest of the table that it computes in floating point with these lines of the
parameter file.
-/

#guard ((expTable 12 8).getD #[]).size == 2307
#guard ((expTable 12 8).getD #[]).toList.take 5 == [4096, 4080, 4064, 4048, 4032]
#guard ((expTable 12 8).getD #[]).foldl (· + ·) 0 == 1050555
-- 72 is the number under which verifier/src/cp_verify.cpp makes this digest (table-digest-exp)
#guard Fmt.hex (secondHashFunction 72 (Fmt.cat (((expTable 12 8).getD #[]).toList.map word32))) ==
  Fmt.hex (Fmt.cat ([3648852807, 2402568834, 4186852988, 523559909, 1873895626, 3042864545,
    1726265496, 165292856].map word32))
#guard ((expTable 12 5).getD #[]).size == 289
#guard ((expTable 12 5).getD #[]).toList.take 4 == [4096, 3970, 3848, 3729]
#guard ((expTable 12 5).getD #[]).foldl (· + ·) 0 == 133122

/-! ## The numbers that depend on the shift

The numbers that depend on the shift, for the shift 8 at dh = 128, S = 12 and rx = 8. The
expected numbers were worked out by hand from the formulas of AFork::shd in
verifier/src/vf_attention_shape.h.
-/

#guard shdOf 2307 (128 * 2047 * 2047) 8 == (⟨590592, 65280, 32865, 1073284096⟩ : ShD)

/-! ## The group of the lookup calls

The known answers for the group of the sub-proof's lookup calls: the lines APUB and AREFUSE of
verifier/tests/forest_weights.txt, each with its name. The C++ test
verifier/tests/hc_forest_attention_test.cpp runs the C++ verifier's code on the same lines and
fills the configuration in the same way. The function answer prints what shapeHid derives in
the format of such a line. The lines are copied here by hand. Nothing compares the copy with the
file.
-/

/-- A configuration from the numbers of a line of known answers. The arguments follow the line's
fields lt, lB, lgk, ldh, HA, nmin, kFD and sh; the six numbers after sh are its field other. The
numbers on which the answers do not depend are set as the C++ test sets them. -/
def cfgOf (lt lB lgk ldh HA nmin kFD : Nat) (sh : Array Nat) (rx lmS la lmb lmh lmo : Nat)
    (lines : List Line) : Cfg :=
  { lt := lt, lB := lB, lgk := lgk, ldh := ldh, ll := ceilLog2 sh.size, S := 12, rx := rx,
    kFD := kFD, lmS := lmS, la := la, lmb := lmb, nmin := nmin,
    H := HA * 2 ^ lgk, sh := sh, wcH := 2 ^ lmh / 2 ^ lt, wcO := 2 ^ lmo / 2 ^ lt,
    wcQ := 2 ^ lmo / 2 ^ lt, NAs := 1, Ty := 1000, lines := lines }

/-- Numbers with commas between them. -/
def commas (l : List Nat) : String := ",".intercalate (l.map toString)

/-- What shapeHid derives, in the format of a line of known answers; or the name of the refusal. -/
def answer (lid : Nat) (cf : Cfg) : String :=
  match shapeHid lid cf with
  | .error name => name
  | .ok (A, h) =>
    let calls := A.calls.toList
    "calls=" ++ ",".intercalate (calls.map (·.call.name)) ++
    " tot=" ++ commas (calls.map (·.tot)) ++
    " n=" ++ commas (calls.map (·.call.n)) ++
    " k=" ++ commas (calls.map (·.call.k)) ++
    " dT=" ++ toString h.dT ++ " kT=" ++ toString h.kT ++ " NT=" ++ toString h.NT ++
    " first=" ++ commas h.first.toList ++
    " columns=" ++ toString A.kbA ++
    " pub=" ++ commas h.pub.toList

/-- The usual call list: one line for each kind of table. -/
def list0 : List Line :=
  [⟨"KR", .kr, [.rm, .rd]⟩,
   ⟨"KFD", .kfd, [.fm, .fd]⟩,
   ⟨"R16", .r16, [.wl, .ix]⟩,
   ⟨"WH", .wh, [.wh]⟩]

/-- A list with IX in a call of its own, in another order, and with FD before FM. -/
def list1 : List Line :=
  [⟨"X", .r16, [.ix]⟩,
   ⟨"KR", .kr, [.rm, .rd]⟩,
   ⟨"WH", .wh, [.wh]⟩,
   ⟨"KFD", .kfd, [.fd, .fm]⟩,
   ⟨"R16", .r16, [.wl]⟩]

/-- The usual list with IX in a call of its own, after WL's. -/
def list2 : List Line :=
  [⟨"KR", .kr, [.rm, .rd]⟩,
   ⟨"KFD", .kfd, [.fm, .fd]⟩,
   ⟨"R16", .r16, [.wl]⟩,
   ⟨"X", .r16, [.ix]⟩,
   ⟨"WH", .wh, [.wh]⟩]

-- profile4
#guard answer 22 (cfgOf 4 2 1 4 2 13 13 #[8, 8]
  5 7 6 11 7 8 list0) ==
  "calls=KR,KFD,R16,WH tot=1536,1536,4224,2048 n=13,13,13,13 k=16,13,16,16 dT=13 kT=16 NT=4 " ++
  "first=0,1,2,3 columns=4096 pub=6656,6656,3968,6144"

-- profile4-12
#guard answer 22 (cfgOf 4 2 1 4 2 12 13 #[8, 8]
  5 7 6 11 7 8 list0) ==
  "calls=KR,KFD,R16,WH tot=1536,1536,4224,2048 n=12,12,13,12 k=16,13,16,16 dT=12 kT=16 NT=5 " ++
  "first=2,3,0,4 columns=4096 pub=0,3968,2560,2560,2048"

-- profile4-11
#guard answer 22 (cfgOf 4 2 1 4 2 11 13 #[8, 8]
  5 7 6 11 7 8 list0) ==
  "calls=KR,KFD,R16,WH tot=1536,1536,4224,2048 n=11,11,13,11 k=16,13,16,16 dT=11 kT=16 NT=7 " ++
  "first=4,5,0,6 columns=4096 pub=0,0,1920,2048,512,512,0"

-- small_both
#guard answer 24 (cfgOf 6 4 1 7 2 20 16 #[8, 8, 8, 8]
  8 11 8 13 12 13 list0) ==
  "calls=KR,KFD,R16,WH tot=49152,49152,263168,131072 n=20,20,20,20 k=16,16,16,16 dT=20 " ++
  "kT=16 NT=4 first=0,1,2,3 columns=1024 pub=999424,999424,785408,917504"

-- full_prompt
#guard answer 28 (cfgOf 10 6 3 7 5 20 16 #[8, 8, 8, 8]
  8 16 16 14 13 16 list0) ==
  "calls=KR,KFD,R16,WH tot=94371840,94371840,42106880,20971520 n=27,27,26,25 k=16,16,16,16 " ++
  "dT=25 kT=16 NT=11 first=0,4,8,10 columns=512 " ++
  "pub=0,0,6291456,33554432,0,0,6291456,33554432,0,25001984,12582912"

-- two-shifts
#guard answer 28 (cfgOf 10 6 3 7 5 20 16 #[9, 8, 9, 9]
  8 16 16 14 13 16 list0) ==
  "calls=KR8,KR9,KFD8,KFD9,R16,WH tot=23592960,70778880,23592960,70778880,42106880,20971520 " ++
  "n=25,27,25,27,26,25 k=16,16,16,16,16,16 dT=25 kT=16 NT=13 first=10,0,11,4,8,12 " ++
  "columns=768 " ++
  "pub=0,0,29884416,33554432,0,0,29884416,33554432,0,25001984,9961472,9961472,12582912"

-- lidb-binds
#guard answer 24 (cfgOf 10 6 3 7 5 20 16 #[8, 8, 8, 8]
  8 16 16 14 13 16 list0) ==
  "calls=KR,KFD,R16,WH tot=94371840,94371840,42106880,20971520 n=27,27,26,25 k=16,16,16,16 " ++
  "dT=24 kT=16 NT=22 first=0,8,16,20 columns=512 " ++
  "pub=0,0,0,0,0,6291456,16777216,16777216,0,0,0,0,0,6291456,16777216,16777216,0,0,8224768," ++
  "16777216,0,12582912"

-- IX-by-itself
#guard answer 28 (cfgOf 10 6 3 7 5 24 16 #[8, 8, 8, 8]
  8 16 16 14 13 16 list1) ==
  "calls=X,KR,WH,KFD,R16 tot=163840,94371840,20971520,94371840,41943040 n=24,27,25,27,26 " ++
  "k=16,16,16,16,16 dT=24 kT=16 NT=23 first=22,0,20,8,16 columns=640 " ++
  "pub=0,0,0,0,0,6291456,16777216,16777216,0,0,0,0,0,6291456,16777216,16777216,0,0,8388608," ++
  "16777216,0,12582912,16613376"

-- 353-trees
#guard answer 28 (cfgOf 10 6 3 7 5 20 16 #[8, 8, 8, 8]
  8 16 16 14 13 16 list2) ==
  "forest-trees"

-- a-tree-shorter-than-a-row-of-a-head
#guard answer 22 (cfgOf 4 2 0 7 1 10 16 #[8, 8]
  5 6 6 13 7 8 list0) ==
  "forest-depth-A"

-- lmbA-4
#guard answer 22 (cfgOf 4 2 1 4 2 13 13 #[8, 8]
  5 7 6 4 7 8 list0) ==
  "forest-planes"

-- lmbA-22
#guard answer 22 (cfgOf 4 2 1 4 2 13 13 #[8, 8]
  5 7 6 22 7 8 list0) ==
  "forest-planes"

-- sixteen-calls
#guard answer 28 (cfgOf 10 6 3 7 5 20 16 #[4, 5, 6, 7, 8, 9, 10, 10]
  8 16 16 14 13 16 list0) ==
  "af-policy-call-list"

/-- True if every call's number iota is n - dT. The C++ test asks this at every line APUB; the guard
below asks it at the line two-shifts only. -/
def iotaHolds (lid : Nat) (cf : Cfg) : Bool :=
  match shapeHid lid cf with
  | .error _ => false
  | .ok (A, h) => A.calls.all fun c => c.call.iota + h.dT == c.call.n

#guard iotaHolds 28 (cfgOf 10 6 3 7 5 20 16 #[9, 8, 9, 9] 8 16 16 14 13 16 list0)

/-! ## Sizes and rounds at the small configuration

Some sizes, and the rounds of the sub-proof's own part, at a small configuration, spelled out here
(small: 64 tokens, eight layers in two groups of four, four query heads, two heads of keys and
values). The rounds are planned by OnBytes/Params/SubRounds.lean from numbers of the shape. The
expected numbers were worked out from the C++ source. None of them depends on Ty. The C++ verifier
prints such numbers in a planning call (verifier/README.md, "Planning calls"): cp_verify -plan
request policy.txt KL.bin 128 -layout layout.txt -prompt REQUEST -reply REPLY -arrays -fields, on a
parameter file, a file of scales and a layout file with these numbers and a request and a reply for
them; that call was not run for this file, and nothing here compares its output with these numbers.
The option -arrays prints the columns of each array and the elements of the vector of tables, the
option -fields the length of every message. No file of the repository is read; the examples under
prover/examples may have other numbers.
-/

/-- The small configuration. It is typed here; nothing here reads a file. Where the verifier fills
a configuration, the shifts are word 11, counted from 0, of each layer's 13 words of 32 bits in the
file of scales KL.bin (klSh in verifier/src/cp_verify.cpp), Ty is 2^18, and the other numbers come
from lines of the parameter file. Here cfgOf sets Ty to 1000. -/
def small : Cfg := cfgOf 6 4 1 7 2 20 16 #[12, 12, 12, 12] 8 11 8 13 12 13 list0

/-- Some sizes of a shape: the columns of the matrices `as`, ah, ao, qa and bA, and the elements of
all tables. -/
def sizes (lid : Nat) (cf : Cfg) : List Nat :=
  match shapeHid lid cf with
  | .error _ => []
  | .ok (A, _) =>
    [A.kAs, A.fillH / cf.wcH, A.fillO / cf.wcO, A.fillQ / cf.wcQ, A.kbA, A.tableElems]

#guard sizes 24 small == [120, 4, 32, 96, 1024, 34152]
-- the same at full size (lt 10, lB 6, G 8, H 40, dh 128, ll 2), worked out by hand from
-- AFork::shape and AFork::tableWords; here the features of ah fill its columns exactly
#guard sizes 28 (cfgOf 10 6 3 7 5 20 16 #[8, 8, 8, 8] 8 16 16 14 13 16 list0) ==
  [7200, 360, 640, 1536, 512, 60640]
-- seven parts: 245,760 cells, 7 * 2,048 to a column of all parts: the cells do not fill the parts,
-- so the columns are rounded up to 18 for each part. The C++ verifier gave the same number in a run
-- with added lines that only print, at the small configuration with NAs 7; that build is not part
-- of the repository.
#guard ((shape { small with NAs := 7 }).toOption.map (·.kAs)) == some 126
-- more columns than a part has rows
#guard ((shape (cfgOf 4 2 1 4 2 13 13 #[8, 8] 5 1 6 11 7 8 list0)).toOption.map (·.kAs)) ==
  some 3840

/-- The numbers on which the rounds depend, from a shape. rows is left 0. The verifier does not call
this function: it fills its own record in the function plan of OnBytes/Model/AttentionPlan.lean,
which the guard on ownRuns does not touch. -/
def ownOf (A : Shape) : Params.AttentionRounds :=
  let found (k : Table) (l : List Seg) : List (ACall × Seg) :=
    (A.calls.toList.filter (·.kind == k)).flatMap fun c => (l.filter c.holds).map fun s => (c, s)
  { lt := A.cf.lt, lgk := A.cf.lgk, pairs := A.NP, Lam := A.Lam,
    planeMessages := (found .kr [.rm, .rd]).length,
    score := (found .kfd [.fm, .fd]).map fun x => (A.nvKF x.2, x.1.npOf x.2),
    e := A.nvE, valueM := A.nvVM, valueD := A.nvVD, attained := A.nvF, bits := A.nvH, rows := 0 }

/-- Replaces each run of equal neighbours by one of them and the run's length. -/
def runs : List (String × Nat × Nat) → List ((String × Nat × Nat) × Nat)
  | [] => []
  | a :: t =>
    match runs t with
    | (b, n) :: r => if a == b then (b, n + 1) :: r else (a, 1) :: (b, n) :: r
    | [] => [(a, 1)]

/-- The rounds of the sub-proof's own part as runs of (name, elements sent, elements drawn). An
element has 24 bytes. -/
def ownRuns (lid : Nat) (cf : Cfg) : List ((String × Nat × Nat) × Nat) :=
  match shapeHid lid cf with
  | .error _ => []
  | .ok (A, _) =>
    match Params.finish {} .request (Params.planAttentionOwn (ownOf A)) with
    | .error _ => []
    | .ok p => runs (p.rounds.map fun r => (r.entry.name, r.entry.msg / 24, r.entry.drawE))

#guard ownRuns 24 small ==
  [(("PSC epsilon", 14, 1), 1), (("PSC round", 3, 1), 11), (("PSC Y", 2, 1), 1),
   (("PSC values", 16, 0), 1), (("PSC epsilon", 8, 1), 1), (("PSC round", 3, 1), 10),
   (("PSC Y", 2, 1), 1), (("PSC values", 16, 0), 1), (("PSC epsilon", 14, 1), 1),
   (("PSC round", 3, 1), 7), (("PSC Y", 2, 1), 1), (("PSC values", 16, 0), 1),
   (("BAT-sigma", 0, 1), 1), (("PSC epsilon", 3, 1), 1), (("PSC round", 3, 1), 8),
   (("PSC Y", 2, 1), 1), (("PSC values", 16, 0), 1), (("PSC epsilon", 1, 1), 1),
   (("PSC round", 3, 1), 7), (("PSC Y", 2, 1), 1), (("PSC values", 16, 0), 1),
   (("ZERO", 0, 18), 1), (("BAT-sigma", 8, 1), 1), (("PSC epsilon", 1, 1), 1),
   (("PSC round", 3, 1), 14), (("PSC Y", 2, 1), 1), (("PSC values", 16, 0), 1),
   (("BAT-sigma", 0, 1), 1), (("PSC epsilon", 1, 1), 1), (("PSC round", 2, 1), 6),
   (("PSC round", 8, 1), 1), (("PSC round", 7, 1), 6), (("PSC Y", 7, 1), 1),
   (("PSC values", 52, 0), 1), (("BAT-sigma", 0, 1), 1), (("PSC epsilon", 1, 1), 1),
   (("PSC round", 3, 1), 11), (("PSC Y", 2, 1), 1), (("PSC values", 16, 0), 1)]

/-- The numbers of batched rows in the entries of the own part's batching rounds. -/
def ownBatchRows (lid : Nat) (cf : Cfg) : List Nat :=
  match shapeHid lid cf with
  | .error _ => []
  | .ok (A, _) =>
    match Params.finish {} .request (Params.planAttentionOwn (ownOf A)) with
    | .error _ => []
    | .ok p => (p.rounds.filter fun r => r.entry.name == "BAT-sigma").map (·.entry.rows)

-- two sums, then the eight pairs three times (plan_attention_own in prover/attn/plan_rounds.h)
#guard ownBatchRows 24 small == [2, 8, 8, 8]

/-! ## Pieces, rows of the calls' tables, the cover

The pieces of the calls at two lists, some rows of the calls' tables, and the cover of the tiles
below the diagonal for 16 tiles on a side.
-/

/-- The calls of a configuration; none if it is refused. -/
def callsOf (cf : Cfg) : List ACall := ((shape cf).toOption.getD {}).calls.toList

/-- True if the pieces follow one another from key 0 on, none larger than the one before it, each
at a multiple of its size, and end at tot. -/
def piecesFit (c : ACall) : Bool :=
  let l := c.pcs.toList
  let last := l.foldl (fun (st : Bool × Nat × Nat) p =>
    (st.1 && p.off == st.2.1 && p.b ≤ st.2.2 && p.off % 2 ^ p.b == 0, p.off + 2 ^ p.b, p.b))
    (true, 0, 64)
  last.1 && last.2.1 == c.tot

/-- The configuration of the line full_prompt of the known answers. -/
def full : Cfg := cfgOf 10 6 3 7 5 20 16 #[8, 8, 8, 8] 8 16 16 14 13 16 list0

/-- The configuration of the line two-shifts of the known answers. -/
def twoShifts : Cfg := cfgOf 10 6 3 7 5 20 16 #[9, 8, 9, 9] 8 16 16 14 13 16 list0

#guard (callsOf full).length == 4 && (callsOf full).all piecesFit
#guard (callsOf twoShifts).length == 6 && (callsOf twoShifts).all piecesFit
-- 20 pieces of 2^22 keys, then 20 of 2^19; within a kind the pieces go by lam, then by a
#guard ((callsOf full).take 1).map (fun c => c.pcs.toList.map fun p => (p.seg, p.b, p.lam, p.a)) ==
  [((List.range 20).map fun i => (Seg.rm, 22, i / 5, i % 5)) ++
   ((List.range 20).map fun i => (Seg.rd, 19, i / 5, i % 5))]
-- a line that lists FD before FM: the larger pieces of FM still come first
#guard ((callsOf (cfgOf 10 6 3 7 5 24 16 #[8, 8, 8, 8] 8 16 16 14 13 16 list1)).filter
  (·.kind == .kfd)).map (fun c => (c.segs, (c.pcs.toList.take 1).map (·.seg))) ==
  [([.fd, .fm], [.fm])]
-- the call for the shift 8 holds only layer 1, the call for the shift 9 the other three
#guard ((callsOf twoShifts).take 2).map (fun c => (c.sh, (c.pcs.toList.map (·.lam)).eraseDups)) ==
  [(8, [1]), (9, [0, 2, 3])]
-- the padding keys point to row 0, whose value is 0; in KFD to row u0, with C - 2^sh + 2^32
#guard (callsOf full).map (fun c => (c.call.t0, (c.call.tauAt c.call.t0).toNat)) ==
  [(0, 0), (2307, 590592 - 256 + 2 ^ 32), (0, 0), (0, 0)]
#guard rowKR 8 255 == 255 && rowKR 8 256 == 2 ^ 20 + 2 ^ 40 && rowWH 65535 == 255 + 255 * 2 ^ 20
#guard rowWH 256 == 2 ^ 20
-- The expected rows below were worked out by hand from AFork::shape (vf_attention_shape.h).
-- Row 256 of the tables of kind KR for the shifts 8 and 9: the flag is set from row 2^sh on.
#guard ((callsOf twoShifts).take 2).map (fun c => (c.call.tauAt 256).toNat) ==
  [2 ^ 20 + 2 ^ 40, 2 ^ 20]
-- a table that is written out has 2^k rows
#guard (callsOf full).all fun c => (c.call.tau.map (·.size)).getD (2 ^ c.call.k) == 2 ^ c.call.k
-- KFD at the shift 8 (u0 = 2307, nHD = 32865, rho = 65280): row 1, the second row for large gaps,
-- the first and the last of the rows that only fill the table up
#guard (((callsOf full).drop 1).take 1).map
    (fun c => [1, 2308, 35172, 65535].map fun t => (c.call.tauAt t).toNat) ==
  [[256 + 4080 * 2 ^ 33, 590336 + 65280 + 2 ^ 32, 590336 + 32640 + 2 ^ 32,
    590336 + 65280 * 30363 + 32640 + 2 ^ 32]]
#guard ((callsOf full).drop 3).map (fun c => (c.call.tauAt 65535).toNat) == [255 + 255 * 2 ^ 20]
-- of each call: k (the table has 2^k rows), the flag fn, kappa (a count has 2^kappa bits), the row
-- of the padding keys, and the shift, which is 0 where the table does not depend on it
#guard (callsOf small).map (fun c => (c.call.k, c.call.fn, c.call.kappa, c.call.t0, c.sh)) ==
  [(16, 2, 5, 0, 12), (16, 1, 5, 2307, 12), (16, 0, 5, 0, 0), (16, 2, 5, 0, 0)]
-- where the tensors begin in ah, ao and qa
#guard ((shape small).toOption.map fun A =>
    [A.oMr, A.oZr, A.oIb, A.oRh, A.oRhp, A.oQ, A.oK, A.oV, A.oO]) ==
  some [0, 64, 128, 0, 2048, 0, 4096, 6144, 8192]
-- where q, k, v and o are in qa: first feature, limbs, layers, features in a layer
#guard ((shape small).toOption.map fun A => [A.atQ, A.atK, A.atV, A.atO]) ==
  some ([⟨0, 2, 4, 512⟩, ⟨4096, 2, 4, 256⟩, ⟨6144, 2, 4, 256⟩, ⟨8192, 2, 4, 512⟩] :
    List Model.TenAt)

/-- The tiles at all tile slots that hold one, for nT tiles on a side. -/
def tiles (nT : Nat) : List (Nat × Nat) :=
  (List.range (nT / 2)).flatMap fun P =>
    (List.range (nT - 1)).map fun sg => Shape.cover { nT := nT } P sg

-- for 16 tiles on a side: every tile below the diagonal is at exactly one tile slot
#guard (tiles 16).length == 120 && (tiles 16).eraseDups.length == 120 &&
  (tiles 16).all fun x => x.2 < x.1 && x.1 < 16

/-! ## The functions on points

The functions on points (eqAt, eqPts, leOf, idOf, onesOf): on all points of three coordinates that
are bits they are the predicates and numbers that they extend. Off the bits: at one point eqAt
agrees with eqTab, and idOf and onesOf are the sums that a multilinear extension is; at one pair of
points so are leOf and eqPts.
-/

/-- The point whose coordinates are the n bits of x, the top bit first. -/
def bitsOf (n x : Nat) : Array E :=
  (Array.range n).map fun v => if (x >>> (n - 1 - v)) % 2 == 1 then oneE else zeroE

/-- 1 if b is true, else 0. -/
def flag (b : Bool) : E := if b then oneE else zeroE

#guard (List.range 8).all fun x => (List.range 8).all fun y =>
  eqAt (bitsOf 3 x) y == flag (x == y) && eqPts (bitsOf 3 x) (bitsOf 3 y) == flag (x == y) &&
  leOf (bitsOf 3 x) (bitsOf 3 y) == flag (x ≤ y)
#guard (List.range 8).all fun x =>
  idOf (bitsOf 3 x) == Model.ofNat x && onesOf (bitsOf 3 x) == flag (x == 7)

/-- A point that is not made of bits. -/
def somePoint : Array E := #[E.mk3 2 0 0, E.mk3 3 1 0, E.mk3 5 0 7]

#guard (List.range 8).all fun c => (Model.eqTab somePoint).getD c zeroE == eqAt somePoint c

/-- A second point that is not made of bits. -/
def otherPoint : Array E := #[E.mk3 11 0 3, E.mk3 0 13 0, E.mk3 17 19 1]

-- Off the bits each function is the multilinear extension: the sum over the indices of its value
-- there times the equality weights.
#guard leOf somePoint otherPoint == (List.range 8).foldl (fun s a =>
  (List.range 8).foldl (fun s b =>
    if a ≤ b then addE s (mulE (eqAt somePoint a) (eqAt otherPoint b)) else s) s) zeroE
#guard eqPts somePoint otherPoint == (List.range 8).foldl (fun s a =>
  addE s (mulE (eqAt somePoint a) (eqAt otherPoint a))) zeroE
#guard idOf somePoint == (List.range 8).foldl (fun s a =>
  addE s (mulE (Model.ofNat a) (eqAt somePoint a))) zeroE
#guard onesOf somePoint == eqAt somePoint 7

/-! ## The refusals of shape

Refusals of shape: a configuration that is admitted, with one field changed at a time, in some
guards several. No guard of this part reaches what no configuration reaches: a table of
exponentials of more than 2^20 + 1 entries, a call of fewer than 2^10 keys, the lower limit on
kFD (a table of fewer than 2^8 rows is refused for its rows, under the same name), and the
conditions N1, N2, N5, N6 and N9 (N3 fails before the first four, and the left side of N9 is
always 2^17).
-/

-- The expected names of this section and the next were worked out by hand from the conditions in
-- AFork::shape (vf_attention_shape.h). None of them comes from a run of the C++ verifier.

/-- A configuration that shape admits: the line profile4 of the known answers. -/
def base : Cfg := cfgOf 4 2 1 4 2 13 13 #[8, 8] 5 7 6 11 7 8 list0

/-- The name under which shape refuses a configuration; empty if it is admitted. -/
def refusal (cf : Cfg) : String :=
  match shape cf with
  | .error name => name
  | .ok _ => ""

#guard refusal base == ""
#guard refusal { base with lB := 3 } == "af-shape-tiles"
#guard refusal { base with lt := 17 } == "af-shape-tiles"
#guard refusal { base with lt := 1, lB := 0 } == "af-shape-tiles"
-- lt = 2 passes this test and fails a later one
#guard refusal { base with lt := 2, lB := 0 } == "af-shape-lmS"
#guard refusal { base with H := 3 } == "af-shape-heads"
#guard refusal { base with H := 0 } == "af-shape-heads"
#guard refusal { base with sh := #[8] } == "af-shape-sh"
#guard refusal { base with la := 3 } == "af-shape-la"
#guard refusal { base with la := 9 } == "af-shape-la"
-- The three clauses of the first test on la. At la 3 and la 9 the second test on la would pass. At
-- la 17 it is not reached: without the clause la > 16 the answer would be af-policy-kF, as at
-- la 16.
#guard refusal { base with la := 8, wcO := 16, wcQ := 16 } == ""
#guard refusal { base with la := 9, wcO := 32, wcQ := 32 } == "af-shape-la"
#guard refusal { base with la := 16, ldh := 12 } == "af-policy-kF"
#guard refusal { base with la := 17, ldh := 13 } == "af-shape-la"
#guard refusal { base with S := 0 } == "af-policy-softmax"
#guard refusal { base with S := 15 } == "af-policy-softmax"
#guard refusal { base with rx := 0 } == "af-policy-softmax"
#guard refusal { base with rx := 13 } == "af-policy-softmax"
-- lt + S + 1 is 24, then 25
#guard refusal { full with S := 13 } == ""
#guard refusal { full with S := 14 } == "af-policy-softmax"
#guard refusal { base with lmS := 0 } == "af-shape-lmS"
#guard refusal { base with lmS := 1 } == ""
#guard refusal { base with lmS := 8 } == "af-shape-lmS"
#guard refusal { base with kFD := 7 } == "af-policy-kF"
#guard refusal { base with kFD := 17 } == "af-policy-kF"
-- 2^17 rows would suit the table here, so it is the test on kFD itself that refuses
#guard refusal { base with kFD := 17, ldh := 8, sh := #[4, 4] } == "af-policy-kF"
-- the table of kind KFD has too few rows, or too many that only fill it up
#guard refusal { base with kFD := 12 } == "af-policy-kF"
#guard refusal { base with kFD := 14 } == "af-policy-kF"
#guard refusal { base with sh := #[3, 8] } == "af-policy-sh"
#guard refusal { base with sh := #[13, 8] } == "af-policy-sh"
#guard refusal { base with Ty := 2 ^ 20 } == "af-no-wrap-N3"
#guard refusal { base with lines := [] } == "af-policy-call-list"
#guard refusal { base with lines := list0 ++ [⟨"X", .wh, [.wh]⟩] } == "af-policy-call-list"
#guard refusal { base with lines := list0 ++ [⟨"X", .wh, []⟩] } == "af-policy-call-list"
-- each kind of segment once, but WH in a line of kind KR
#guard refusal { base with lines := [⟨"KR", .kr, [.rm, .rd, .wh]⟩] ++ (list0.drop 1).take 2 } ==
  "af-policy-call-list"
-- five shifts: twelve calls from the usual list, thirteen with IX in a call of its own
#guard refusal (cfgOf 10 6 3 7 5 20 16 #[4, 5, 6, 7, 8, 8, 8, 8] 8 16 16 14 13 16 list0) == ""
#guard refusal (cfgOf 10 6 3 7 5 20 16 #[4, 5, 6, 7, 8, 8, 8, 8] 8 16 16 14 13 16 list2) ==
  "af-policy-call-list"
#guard refusal { base with nmin := 9 } == "af-policy-nmin"
-- the four clauses of the second test on la, one at a time: a width 0 is a multiple of 2^ls
#guard refusal { base with wcO := 0 } == "af-shape-la"
#guard refusal { base with wcQ := 0 } == "af-shape-la"
#guard refusal { base with wcO := 18 } == "af-shape-la"
#guard refusal { base with wcQ := 18 } == "af-shape-la"
#guard refusal { base with nmin := 45 } == "af-shape-call"
-- two more names that a configuration can reach
#guard refusal { base with S := 14, rx := 12, sh := #[12, 12], kFD := 16, ldh := 6 } ==
  "af-policy-C"
#guard refusal { base with S := 1, rx := 1, sh := #[4, 4], kFD := 16, ldh := 8 } == "af-no-wrap-N4"

/-! ## The conditions at their bounds

The conditions of shTests and wrapTests, called directly, each at its bound and one step beyond
it. The first half of af-no-wrap-N2 is not tried: it cannot fail before the second half.
-/

/-- The name of a refusal; empty if there is none. -/
def nameOf (x : Except String Unit) : String :=
  match x with
  | .error name => name
  | .ok _ => ""

/-- The numbers that shTests reads of a configuration. -/
def forSh (kFD Ty S : Nat) : Cfg := { kFD := kFD, Ty := Ty, S := S }

/-- The numbers that wrapTests reads of a configuration. -/
def forWrap (lt Ty S : Nat) : Cfg := { lt := lt, Ty := Ty, S := S }

-- Each condition is called with numbers at its bound and one step beyond it, and no number is 0, so
-- that a constant that is wrong by more than the few units between the numbers and the bound fails
-- a test. The numbers were worked out from the conditions in
-- AFork::shape (vf_attention_shape.h). No configuration that shape admits need have them. Where a
-- later condition fails at the bound of an earlier one, the later one's name is expected.
#guard nameOf (shTests (forSh 16 1000 12) 34536 507763620 3) == "af-policy-sh"
#guard nameOf (shTests (forSh 16 1000 12) 34536 507763620 4) == ""
#guard nameOf (shTests (forSh 16 1000 12) 4080 476144640 12) == ""
#guard nameOf (shTests (forSh 16 1000 12) 4080 476144640 13) == "af-policy-sh"
#guard nameOf (shTests (forSh 16 1000 12) 34537 507763620 4) == "af-policy-kF"
#guard nameOf (shTests (forSh 16 1000 12) 3536 507763620 4) == ""
#guard nameOf (shTests (forSh 16 1000 12) 3535 507763620 4) == "af-policy-kF"
#guard nameOf (shTests (forSh 16 1000 12) 34536 507763619 4) == ""
#guard nameOf (shTests (forSh 16 1000 12) 34537 507763619 4) == ""
#guard nameOf (shTests (forSh 16 1000 12) 4081 476144640 12) == "af-policy-C"
#guard nameOf (shTests (forSh 23 1044495 6) 1 69435271845 4) == "af-no-wrap-N4"
#guard nameOf (shTests (forSh 23 1044495 6) 1 69435271846 4) == "af-no-wrap-N3"
-- the left side of N3 is 2^61 - 2 two lines above, and 2^61 here
#guard nameOf (shTests (forSh 23 1044495 6) 2 69435271840 4) == "af-no-wrap-N3"
#guard nameOf (shTests (forSh 16 1000 12) 1 715795109 4) == ""
#guard nameOf (shTests (forSh 16 1000 12) 1 715795110 4) == "af-no-wrap-N4"
-- the left side of N4 is 2^32
#guard nameOf (shTests (forSh 16 1000 12) 2 715795104 4) == "af-no-wrap-N4"
#guard nameOf (wrapTests (forWrap 16 1000 1) 1 1152921487763837975) == ""
#guard nameOf (wrapTests (forWrap 16 1000 1) 1 1152921487763837976) == "af-no-wrap-N1"
#guard nameOf (wrapTests (forWrap 16 1048191 1) 1 1) == ""
#guard nameOf (wrapTests (forWrap 16 1048192 1) 1 1) == "af-no-wrap-N2"
#guard nameOf (wrapTests (forWrap 16 1000 1) 576460743881918987 1) == "af-no-wrap-N6"
#guard nameOf (wrapTests (forWrap 16 1000 1) 576460743881918988 1) == "af-no-wrap-N5"
#guard nameOf (wrapTests (forWrap 16 319355 1) 3511737601 1) == ""
#guard nameOf (wrapTests (forWrap 16 319355 1) 3511737602 1) == "af-no-wrap-N6"
-- the left side of N6 is 17 below 2^60 two lines above, and 61 above it here; no numbers that N2
-- admits bring it nearer on either side
#guard nameOf (wrapTests (forWrap 16 80647 1) 13905143810 1) == "af-no-wrap-N6"
#guard nameOf (wrapTests (forWrap 3 1 1) 70368744177663 1) == ""
#guard nameOf (wrapTests (forWrap 3 1 1) 70368744177664 1) == "af-no-wrap-N9"

-- some of the names that the guards above expect, looked up in shapeNames
#guard ["af-shape-tiles", "af-policy-call-list", "forest-depth-A", "af-shape-call", "af-policy-C",
  "af-no-wrap-N1", "af-no-wrap-N9"].all shapeNames.contains

end OnBytes.Attention.Test
