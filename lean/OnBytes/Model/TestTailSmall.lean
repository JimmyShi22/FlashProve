-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestTailSmall.lean: the smallness test's public numbers at a small configuration.

A small configuration, spelled out here, has five sub-proofs: two for groups of layers (G0, G1), two
for attention (A0, A1) and one for the output head (H). No file of the repository is read, and the
numbers need not be those of any example folder of the repository. For each sub-proof this file
holds the inputs of its smallness test (the fields of Given from tau to aTX, the field U of ix, and
reads), and the numbers that the C++ verifier computes from them when it makes its plan. No proof is
read for them. Inputs and expected numbers alike were printed by a copy of the C++ verifier to which
only print statements were added, and a program wrote them into this file. None was taken from the
output of the Lean functions. That copy is not in the repository, so a reader cannot print them
again. HTailF2.shape, addTrees and t2Plan must give the same numbers.

The terms are explained in OnBytes/Model/Tail.lean (the docstring of HTailF2 says where). Names such
as R10z, R8d, PXo, PXf0 and af0 are the C++ programs'.

The file is not imported by the program.
-/
import OnBytes.Model.Tail

namespace OnBytes.Model.TestTailSmall

open OnBytes OnBytes.Model

/-- The inputs to the smallness test of one sub-proof, and the numbers that the C++ verifier
computes from them. -/
structure Given where
  /-- the number of random combinations -/
  tau : Nat
  /-- log2 of the most keys in one tree of a lookup -/
  lidb : Nat
  /-- the matrices -/
  mats : Array TMat
  /-- for each matrix: its number i among the arrays PX_i, which another sub-proof reads; none for a
  matrix that has no such array -/
  txOf : Array (Option Nat)
  /-- the arrays of earlier sub-proofs -/
  ft : Array T2Foreign
  /-- the lengths of the sub-proof's vectors U1 to U3 -/
  nU : Array Nat
  /-- for each array that another sub-proof reads: 1 + the number of its readers -/
  aTX : Array Nat
  /-- expected: HTailF2.mz -/
  mz : Nat
  /-- expected: HTailF2.off -/
  off : Array Nat
  /-- expected: HTailF2.gtTree -/
  gtTree : Array Nat
  /-- expected: HTailF2.kTX -/
  kTX : Array Nat
  /-- expected: HTailF2.ix. Its field U is also an input: from it Given.made tells shape which of U1
  to U4 the sub-proof has. So of U the comparison tests only the numbering -/
  ix : T2Map
  /-- expected: HTailF2.pkMat -/
  pkMat : Array Nat
  /-- expected: HTailF2.pxMat -/
  pxMat : Array Nat
  /-- expected, for both lookup calls: name, n, iota, k -/
  calls : Array (String × Nat × Nat × Nat)
  /-- expected, for the pieces of both calls: tree, row, r0, Rp, c0, Cp, CP, off, a, b -/
  pieces : Array (Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat)
  /-- expected, of the lookup: dT, kT, NT, rK, NC, cK -/
  forest : Nat × Nat × Nat × Nat × Nat × Nat
  /-- expected: Forest.Shape.iota -/
  iota : Array Nat
  /-- expected: Forest.Shape.first -/
  first : Array Nat
  /-- expected: Forest.Shape.callOf -/
  callOf : Array Nat
  /-- expected: Forest.Shape.pub -/
  pub : Array Nat
  /-- expected, of the lookup: v, d, emptyKeys, padding, elems, lins -/
  counts : Nat × Nat × Nat × Nat × Nat × Nat
  /-- expected: HTailF2.bzColumns -/
  bzColumns : Nat
  /-- expected: HTailF2.stepF -/
  stepF : Nat
  /-- expected, for each array of the list: name, whether it holds symbols, R, K, the number of
  virtual rows, owner -/
  trees : Array (String × Bool × Nat × Nat × Nat × Bool)
  /-- expected, for each array of the list: ec, a, foreign, and of a symbol array m, k, mS, aX -/
  nt : Array (Nat × Nat × Bool × Option (Nat × Nat × Nat × Nat))
  /-- the number of reads in the sub-proof's plan -/
  reads : Nat
  /-- expected: HTailF2.lins reads -/
  lins : Nat
  /-- expected: HTailF2.equationsF reads -/
  equations : Nat

/-- The state of the smallness test, the sub-proof's state with the arrays, and the closed list, as
the Lean functions make them. -/
def Given.made (x : Given) : Except String (HTailF2 × Fork × Tail2) := do
  let seed : HTailF2 := { tau := x.tau, lidb := x.lidb }
  let tl ← seed.shape x.mats x.txOf x.ft (x.ix.U.map (·.isSome)) x.tau
  -- hb = 100 is arbitrary: no expected number depends on it. hbLine = tau is the largest value that
  -- addTrees accepts.
  let (tl, F, T) ← tl.addTrees {} {} x.nU x.aTX 100 x.tau
  pure (tl, F, ← t2Plan F T)

/-- The labels of the groups of numbers in which the Lean functions differ from what is expected; a
label names the first field of its group. A failed #guard below does not print the list: evaluate
givenG0.faults to see it. -/
def Given.faults (x : Given) : List String :=
  match x.made with
  | .error e => [e]
  | .ok (tl, F, T) =>
    let h := tl.f9
    let tests : List (String × Bool) := [
      ("mz", tl.mz == x.mz && tl.NM == x.mats.size),
      ("off", tl.off == x.off),
      ("gtTree", tl.gtTree == x.gtTree),
      ("kTX", tl.kTX == x.kTX),
      ("ix", tl.ix == x.ix),
      ("pkMat", tl.pkMat == x.pkMat && tl.pxMat == x.pxMat),
      ("calls", #[tl.z1, tl.z2].map (fun z => (z.call.name, z.call.n, z.call.iota, z.call.k))
        == x.calls),
      ("pieces", (tl.z1.pieces ++ tl.z2.pieces).map
        (fun p => (p.tree, p.row, p.r0, p.Rp, p.c0, p.Cp, p.CP, p.off, p.a, p.b)) == x.pieces),
      ("forest", (h.dT, h.kT, h.NT, h.rK, h.NC, h.cK) == x.forest),
      ("iota", h.iota == x.iota && h.first == x.first && h.callOf == x.callOf),
      ("pub", h.pub == x.pub),
      ("counts", (h.v, h.d, h.emptyKeys, h.padding, tl.smallElems, Forest.lins h) == x.counts),
      ("bzColumns", tl.bzColumns == x.bzColumns && tl.stepF == x.stepF),
      ("trees", F.trees.map
        (fun X => (X.name, X.kind == .symbols, X.R, X.K, X.rows.size, X.owner)) == x.trees),
      ("nt", T.nt.map
        (fun n => (n.ec, n.a, n.foreign, n.p.map fun s => (s.m, s.k, s.mS, s.aX))) == x.nt),
      ("lins", tl.lins x.reads == x.lins),
      ("equations", tl.equationsF x.reads == x.equations)]
    (tests.filter fun t => !t.2).map (·.1)

/-- The sub-proof G0. -/
def givenG0 : Given where
  tau := 128
  lidb := 24
  mats := #[{ name := "af0", m := 8192, k := 247, kind := 0, foreign := none, aId := 256 },
    { name := "af1", m := 8192, k := 247, kind := 0, foreign := none, aId := 257 },
    { name := "af2", m := 8192, k := 247, kind := 0, foreign := none, aId := 258 },
    { name := "ad0", m := 4096, k := 160, kind := 0, foreign := none, aId := 259 },
    { name := "ar", m := 4096, k := 14, kind := 0, foreign := none, aId := 260 },
    { name := "b", m := 8192, k := 2048, kind := 0, foreign := none, aId := 261 },
    { name := "qa", m := 8192, k := 96, kind := 0, foreign := none, aId := 262 },
    { name := "xbO", m := 8192, k := 20, kind := 0, foreign := none, aId := 263 },
    { name := "xbI", m := 8192, k := 20, kind := 0, foreign := none, aId := 264 }]
  txOf := #[none, none, none, none, none, none, some 0, some 1, none]
  ft := #[]
  nU := #[0, 0, 167328]
  aTX := #[2, 2]
  mz := 65536
  off := #[0, 8192, 16384, 24576, 28672, 32768, 40960, 49152, 57344]
  gtTree := #[1, 2, 3, 4, 5, 6, 8, 9, 7]
  kTX := #[96, 20]
  ix :=
    { U := #[none, none, some 0, none], ZZ := 10, BZ := 11, TX := #[8, 9], FT := #[],
      PK := #[1, 2, 3, 4, 5, 6, 7], count := 12 }
  pkMat := #[0, 1, 2, 3, 4, 5, 8]
  pxMat := #[6, 7]
  calls := #[("R10z", 23, 0, 10), ("R8d", 23, 0, 8)]
  pieces := #[(10, 0, 0, 128, 0, 65536, 65536, 0, 7, 23),
    (10, 1, 0, 128, 65536, 65536, 65536, 0, 7, 23)]
  forest := (23, 10, 2, 1, 2, 1)
  iota := #[0, 0]
  first := #[0, 1]
  callOf := #[0, 1]
  pub := #[0, 0]
  counts := (24, 11, 0, 0, 1198, 67)
  bzColumns := 2048
  stepF := 128
  trees := #[("U3", false, 1, 167328, 1, true), ("PK0", true, 2731, 247, 1, true),
    ("PK1", true, 2731, 247, 1, true), ("PK2", true, 2731, 247, 1, true),
    ("PK3", true, 1366, 160, 1, true), ("PK4", true, 1366, 14, 1, true),
    ("PK5", true, 2731, 2048, 1, true), ("PK6", true, 2731, 20, 1, true),
    ("PX0", true, 2731, 96, 1, true), ("PX1", true, 2731, 20, 1, true),
    ("ZZ", false, 128, 131072, 4, true), ("BZ", false, 32, 2048, 3, true)]
  nt := #[(3, 1, false, none), (1, 1, false, some (8192, 247, 2731, 12)),
    (1, 1, false, some (8192, 247, 2731, 12)), (1, 1, false, some (8192, 247, 2731, 12)),
    (1, 1, false, some (4096, 160, 1366, 11)), (1, 1, false, some (4096, 14, 1366, 11)),
    (1, 1, false, some (8192, 2048, 2731, 12)), (1, 1, false, some (8192, 20, 2731, 12)),
    (1, 2, false, some (8192, 96, 2731, 12)), (1, 2, false, some (8192, 20, 2731, 12)),
    (1, 1, false, none), (1, 1, false, none)]
  reads := 1187
  lins := 1267
  equations := 4346240

/-- The sub-proof A0. -/
def givenA0 : Given where
  tau := 128
  lidb := 24
  mats := #[{ name := "as0", m := 2048, k := 120, kind := 0, foreign := none, aId := 1024 },
    { name := "ah", m := 4096, k := 4, kind := 0, foreign := none, aId := 1025 },
    { name := "ao", m := 8192, k := 32, kind := 0, foreign := none, aId := 1026 },
    { name := "bA", m := 8192, k := 1024, kind := 0, foreign := none, aId := 1027 },
    { name := "qa", m := 8192, k := 96, kind := 1, foreign := some 0, aId := 262 }]
  txOf := #[none, none, none, none, none]
  ft := #[{ name := "PXo", K := 96, a := 2, m := 8192 }]
  nU := #[0, 0, 34152]
  aTX := #[]
  mz := 30720
  off := #[0, 2048, 6144, 14336, 22528]
  gtTree := #[1, 2, 3, 4, 7]
  kTX := #[]
  ix :=
    { U := #[none, none, some 0, none], ZZ := 5, BZ := 6, TX := #[], FT := #[7],
      PK := #[1, 2, 3, 4], count := 8 }
  pkMat := #[0, 1, 2, 3]
  pxMat := #[]
  calls := #[("R10z", 22, 0, 10), ("R8d", 22, 0, 8)]
  pieces := #[(5, 0, 0, 128, 0, 30720, 32768, 0, 7, 22),
    (5, 1, 0, 128, 30720, 30720, 32768, 0, 7, 22)]
  forest := (22, 10, 2, 1, 2, 1)
  iota := #[0, 0]
  first := #[0, 1]
  callOf := #[0, 1]
  pub := #[262144, 262144]
  counts := (23, 11, 0, 524288, 1147, 66)
  bzColumns := 2048
  stepF := 128
  trees := #[("U3", false, 1, 34152, 1, true), ("PK0", true, 683, 120, 1, true),
    ("PK1", true, 1366, 4, 1, true), ("PK2", true, 2731, 32, 1, true),
    ("PK3", true, 2731, 1024, 1, true), ("ZZ", false, 128, 61440, 4, true),
    ("BZ", false, 32, 2048, 3, true), ("PXo", true, 2731, 96, 1, false)]
  nt := #[(3, 1, false, none), (1, 1, false, some (2048, 120, 683, 10)),
    (1, 1, false, some (4096, 4, 1366, 11)), (1, 1, false, some (8192, 32, 2731, 12)),
    (1, 1, false, some (8192, 1024, 2731, 12)), (1, 1, false, none), (1, 1, false, none),
    (1, 2, true, some (8192, 96, 2731, 12))]
  reads := 838
  lins := 913
  equations := 2073344

/-- The sub-proof G1. -/
def givenG1 : Given where
  tau := 128
  lidb := 24
  mats := #[{ name := "af0", m := 8192, k := 247, kind := 0, foreign := none, aId := 512 },
    { name := "af1", m := 8192, k := 247, kind := 0, foreign := none, aId := 513 },
    { name := "af2", m := 8192, k := 247, kind := 0, foreign := none, aId := 514 },
    { name := "ad0", m := 4096, k := 160, kind := 0, foreign := none, aId := 515 },
    { name := "ar", m := 4096, k := 14, kind := 0, foreign := none, aId := 516 },
    { name := "b", m := 8192, k := 2048, kind := 0, foreign := none, aId := 517 },
    { name := "qa", m := 8192, k := 96, kind := 0, foreign := none, aId := 518 },
    { name := "xbO", m := 8192, k := 20, kind := 0, foreign := none, aId := 519 },
    { name := "xbI", m := 8192, k := 20, kind := 1, foreign := some 0, aId := 263 }]
  txOf := #[none, none, none, none, none, none, some 0, some 1, none]
  ft := #[{ name := "PXf0", K := 20, a := 2, m := 8192 }]
  nU := #[0, 0, 166688]
  aTX := #[2, 2]
  mz := 65536
  off := #[0, 8192, 16384, 24576, 28672, 32768, 40960, 49152, 57344]
  gtTree := #[1, 2, 3, 4, 5, 6, 7, 8, 11]
  kTX := #[96, 20]
  ix :=
    { U := #[none, none, some 0, none], ZZ := 9, BZ := 10, TX := #[7, 8], FT := #[11],
      PK := #[1, 2, 3, 4, 5, 6], count := 12 }
  pkMat := #[0, 1, 2, 3, 4, 5]
  pxMat := #[6, 7]
  calls := #[("R10z", 23, 0, 10), ("R8d", 23, 0, 8)]
  pieces := #[(9, 0, 0, 128, 0, 65536, 65536, 0, 7, 23),
    (9, 1, 0, 128, 65536, 65536, 65536, 0, 7, 23)]
  forest := (23, 10, 2, 1, 2, 1)
  iota := #[0, 0]
  first := #[0, 1]
  callOf := #[0, 1]
  pub := #[0, 0]
  counts := (24, 11, 0, 0, 1198, 67)
  bzColumns := 2048
  stepF := 128
  trees := #[("U3", false, 1, 166688, 1, true), ("PK0", true, 2731, 247, 1, true),
    ("PK1", true, 2731, 247, 1, true), ("PK2", true, 2731, 247, 1, true),
    ("PK3", true, 1366, 160, 1, true), ("PK4", true, 1366, 14, 1, true),
    ("PK5", true, 2731, 2048, 1, true), ("PX0", true, 2731, 96, 1, true),
    ("PX1", true, 2731, 20, 1, true), ("ZZ", false, 128, 131072, 4, true),
    ("BZ", false, 32, 2048, 3, true), ("PXf0", true, 2731, 20, 1, false)]
  nt := #[(3, 1, false, none), (1, 1, false, some (8192, 247, 2731, 12)),
    (1, 1, false, some (8192, 247, 2731, 12)), (1, 1, false, some (8192, 247, 2731, 12)),
    (1, 1, false, some (4096, 160, 1366, 11)), (1, 1, false, some (4096, 14, 1366, 11)),
    (1, 1, false, some (8192, 2048, 2731, 12)), (1, 2, false, some (8192, 96, 2731, 12)),
    (1, 2, false, some (8192, 20, 2731, 12)), (1, 1, false, none), (1, 1, false, none),
    (1, 2, true, some (8192, 20, 2731, 12))]
  reads := 1155
  lins := 1235
  equations := 4342144

/-- The sub-proof A1. -/
def givenA1 : Given where
  tau := 128
  lidb := 24
  mats := #[{ name := "as0", m := 2048, k := 120, kind := 0, foreign := none, aId := 1280 },
    { name := "ah", m := 4096, k := 4, kind := 0, foreign := none, aId := 1281 },
    { name := "ao", m := 8192, k := 32, kind := 0, foreign := none, aId := 1282 },
    { name := "bA", m := 8192, k := 1024, kind := 0, foreign := none, aId := 1283 },
    { name := "qa", m := 8192, k := 96, kind := 1, foreign := some 0, aId := 518 }]
  txOf := #[none, none, none, none, none]
  ft := #[{ name := "PXo", K := 96, a := 2, m := 8192 }]
  nU := #[0, 0, 34152]
  aTX := #[]
  mz := 30720
  off := #[0, 2048, 6144, 14336, 22528]
  gtTree := #[1, 2, 3, 4, 7]
  kTX := #[]
  ix :=
    { U := #[none, none, some 0, none], ZZ := 5, BZ := 6, TX := #[], FT := #[7],
      PK := #[1, 2, 3, 4], count := 8 }
  pkMat := #[0, 1, 2, 3]
  pxMat := #[]
  calls := #[("R10z", 22, 0, 10), ("R8d", 22, 0, 8)]
  pieces := #[(5, 0, 0, 128, 0, 30720, 32768, 0, 7, 22),
    (5, 1, 0, 128, 30720, 30720, 32768, 0, 7, 22)]
  forest := (22, 10, 2, 1, 2, 1)
  iota := #[0, 0]
  first := #[0, 1]
  callOf := #[0, 1]
  pub := #[262144, 262144]
  counts := (23, 11, 0, 524288, 1147, 66)
  bzColumns := 2048
  stepF := 128
  trees := #[("U3", false, 1, 34152, 1, true), ("PK0", true, 683, 120, 1, true),
    ("PK1", true, 1366, 4, 1, true), ("PK2", true, 2731, 32, 1, true),
    ("PK3", true, 2731, 1024, 1, true), ("ZZ", false, 128, 61440, 4, true),
    ("BZ", false, 32, 2048, 3, true), ("PXo", true, 2731, 96, 1, false)]
  nt := #[(3, 1, false, none), (1, 1, false, some (2048, 120, 683, 10)),
    (1, 1, false, some (4096, 4, 1366, 11)), (1, 1, false, some (8192, 32, 2731, 12)),
    (1, 1, false, some (8192, 1024, 2731, 12)), (1, 1, false, none), (1, 1, false, none),
    (1, 2, true, some (8192, 96, 2731, 12))]
  reads := 838
  lins := 913
  equations := 2073344

/-- The sub-proof H. -/
def givenH : Given where
  tau := 128
  lidb := 24
  mats := #[{ name := "hf0", m := 16384, k := 20, kind := 0, foreign := none, aId := 768 },
    { name := "hd", m := 4096, k := 16, kind := 0, foreign := none, aId := 769 },
    { name := "hr", m := 4096, k := 2, kind := 0, foreign := none, aId := 770 },
    { name := "bH", m := 8192, k := 1536, kind := 0, foreign := none, aId := 771 },
    { name := "xbL", m := 8192, k := 20, kind := 1, foreign := some 0, aId := 519 }]
  txOf := #[none, none, none, none, none]
  ft := #[{ name := "PXf0", K := 20, a := 2, m := 8192 }]
  nU := #[0, 0, 11264]
  aTX := #[]
  mz := 40960
  off := #[0, 16384, 20480, 24576, 32768]
  gtTree := #[1, 2, 3, 4, 7]
  kTX := #[]
  ix :=
    { U := #[none, none, some 0, none], ZZ := 5, BZ := 6, TX := #[], FT := #[7],
      PK := #[1, 2, 3, 4], count := 8 }
  pkMat := #[0, 1, 2, 3]
  pxMat := #[]
  calls := #[("R10z", 23, 0, 10), ("R8d", 23, 0, 8)]
  pieces := #[(5, 0, 0, 128, 0, 40960, 65536, 0, 7, 23),
    (5, 1, 0, 128, 40960, 40960, 65536, 0, 7, 23)]
  forest := (23, 10, 2, 1, 2, 1)
  iota := #[0, 0]
  first := #[0, 1]
  callOf := #[0, 1]
  pub := #[3145728, 3145728]
  counts := (24, 11, 0, 6291456, 1198, 67)
  bzColumns := 2048
  stepF := 128
  trees := #[("U3", false, 1, 11264, 1, true), ("PK0", true, 5462, 20, 1, true),
    ("PK1", true, 1366, 16, 1, true), ("PK2", true, 1366, 2, 1, true),
    ("PK3", true, 2731, 1536, 1, true), ("ZZ", false, 128, 81920, 4, true),
    ("BZ", false, 32, 2048, 3, true), ("PXf0", true, 2731, 20, 1, false)]
  nt := #[(3, 1, false, none), (1, 1, false, some (16384, 20, 5462, 13)),
    (1, 1, false, some (4096, 16, 1366, 11)), (1, 1, false, some (4096, 2, 1366, 11)),
    (1, 1, false, some (8192, 1536, 2731, 12)), (1, 1, false, none), (1, 1, false, none),
    (1, 2, true, some (8192, 20, 2731, 12))]
  reads := 707
  lins := 783
  equations := 2711936

#guard givenG0.faults == []
#guard givenA0.faults == []
#guard givenG1.faults == []
#guard givenA1.faults == []
#guard givenH.faults == []

end OnBytes.Model.TestTailSmall
