-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestHeadPlan.lean: tests of the plan of the output head's sub-proof.

The numbers are those of a small configuration, spelled out in OnBytes/Model/TestHeadLayout.lean
and here. The expected values are what the C++ verifier computes for it in a planning call. No
test here runs that verifier. The tests run `matsH`, the tail's shape, the four counts and
`addTrees`. They do not run `planH2`, the tests that it makes itself, `t2Plan` or `ownerHeld`. The
program does not import this file.
-/
import OnBytes.Model.HeadPlan
import OnBytes.Model.TestHeadLayout

namespace OnBytes.Model.Head

/-- The matrix of the residual stream at the small example configuration. -/
def smallBorder : Border := { mxb := 8192, kxb := 20, off := 0, nl := 5, cnt := 1, J := 512 }

/-- The matrices of the head's smallness test. There are two groups of layers, so the head is
sub-proof number 3. The stream is matrix 7 of sub-proof number 2. -/
def smallMats : Except String (Array TMat) :=
  smallLayout.map fun L => matsH smallShape L smallBorder 3 519

#guard (smallMats.toOption.map fun m => m.toList.map fun M => (M.name, M.m, M.k, M.kind, M.aId)) ==
  some [("hf0", 16384, 20, 0, 768), ("hd", 4096, 16, 0, 769), ("hr", 4096, 2, 0, 770),
    ("bH", 8192, 1536, 0, 771), ("xbL", 8192, 20, 1, 519)]

/-- The record of the head's smallness test (the tail), built as planH2 builds it: tau 128, of the
vectors U1 to U3 only U3, and the stream as the one array of another sub-proof. -/
def smallTail : Except String HTailF2 := do
  let mats ← smallMats
  ({ tau := 128, lidb := 24 } : HTailF2).shape mats (Array.replicate mats.size none)
    #[{ name := "PXf0", K := 20, a := 2, m := 8192, wp := 0 }] #[false, false, true, false] 128

#guard smallTail.isOk
#guard (smallTail.toOption.map fun tl => [tl.NM, tl.mz, tl.smallElems, tl.lins 707,
    tl.equationsF 707]) == some [5, 40960, 1198, 783, 2711936]
#guard (smallLayout.toOption.map fun L => [Forest.elems L.fs, Forest.lins L.fs]) == some [1531, 74]
#guard (smallLayout.toOption.map fun L =>
    [readsLength smallShape L smallBorder, readsH smallShape L smallBorder]) == some [11264, 707]
#guard ((do
    let L ← smallLayout
    let tl ← smallTail
    pure [slotsH smallShape L tl 11, claimsH smallShape L tl 707]).toOption) == some [2879, 897]

/-- The list of the head's arrays, at 128 bits with no bits of work; 11264 is readsLength. -/
def smallTrees : Except String (HTailF2 × Fork × Tail2) := do
  (← smallTail).addTrees {} {} #[0, 0, 11264] #[] 128 128

#guard (smallTrees.toOption.map fun x => x.2.1.trees.toList.map fun X =>
    (X.name, X.R, X.K, X.rows.size)) ==
  some [("U3", 1, 11264, 1), ("PK0", 5462, 20, 1), ("PK1", 1366, 16, 1), ("PK2", 1366, 2, 1),
    ("PK3", 2731, 1536, 1), ("ZZ", 128, 81920, 4), ("BZ", 32, 2048, 3), ("PXf0", 2731, 20, 1)]
#guard (smallTrees.toOption.map fun x => x.2.2.nt.toList.map fun n => (n.ec, n.a, n.foreign)) ==
  some [(3, 1, false), (1, 1, false), (1, 1, false), (1, 1, false), (1, 1, false), (1, 1, false),
    (1, 1, false), (1, 2, true)]
#guard (smallTrees.toOption.map fun x =>
    (x.1.ix.U, x.1.ix.ZZ, x.1.ix.BZ, x.1.ix.PK, x.1.ix.TX, x.1.ix.FT, x.1.pkMat)) ==
  some (#[none, none, some 0, none], 5, 6, #[1, 2, 3, 4], #[], #[7], #[0, 1, 2, 3])

/-! ## Other settings

The expected values are what the C++ verifier computes in planning calls on that configuration's
parameter file with the named lines changed. -/

/-- The plan's counts for the numbers h and the stream's matrix b: the scalars sent, the claims, the
length of the vector of reads, the reads, the smallness test's claims, and the rows that the last
round batches. -/
def countsAt (h : Shape) (b : Border) : Except String (List Nat) := do
  let L ← layout h someTable
  let mats := matsH h L b 3 519
  let tl ← ({ tau := 128, lidb := 24 } : HTailF2).shape mats (Array.replicate mats.size none)
    #[{ name := "PXf0", K := b.kxb, a := 2, m := b.mxb, wp := 0 }] #[false, false, true, false] 128
  let r := readsH h L b
  pure [slotsH h L tl 11, claimsH h L tl r, readsLength h L b, r, tl.lins r,
    claimsH h L tl r + tl.equationsF r]

#guard (countsAt smallShape smallBorder).toOption == some [2879, 897, 11264, 707, 783, 2712833]
-- The matrix hf in two parts.
#guard (countsAt { smallShape with NHf := 2, lmhf := 13 } smallBorder).toOption ==
  some [2879, 898, 11264, 707, 784, 2712834]
-- Five calls: all four segments of the kind R16 in one.
#guard (countsAt { smallShape with polCallsH := [["R16", "R16", "NF", "NFH", "HD0", "HD1"],
      ["R8", "R8", "ROW", "HD2"], ["FEa", "FE", "HE0"], ["FEb", "FE", "HE1"], ["FC", "FC", "CNF"]] }
    smallBorder).toOption == some [2879, 897, 10496, 707, 783, 2712833]
-- Four limbs.
#guard (countsAt { smallShape with XL := 4 } { smallBorder with kxb := 16, nl := 4 }).toOption ==
  some [2872, 891, 11008, 707, 783, 2712827]
-- A lower floor on a call's keys (nmin, with the head's iota to fit; in that planning call the
-- lines iota of the layers and of attention were changed too): the first call of the lookup takes
-- two trees.
#guard (countsAt { smallShape with nmin := 16, iotaH := [1, 0, 0, 0, 0, 0] }
    smallBorder).toOption == some [2695, 893, 11264, 707, 783, 2712829]

end OnBytes.Model.Head
