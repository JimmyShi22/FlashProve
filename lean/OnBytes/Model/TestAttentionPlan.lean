-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestAttentionPlan.lean: tests of OnBytes/Model/AttentionPlan.lean.

The tests run when this file is compiled. The program does not import this file.

What is tested: the counts of the plan at a small configuration, spelled out here (smallCfg: 64
tokens, a group of four layers, four query heads, two heads of keys and values).
No file of the repository is read; the examples under prover/examples may have other numbers.

Where the expected numbers come from.
 1. By hand from AttentionSubProof::plan (verifier/src/vf_attention_check.h): the counts over the
    calls, the numbers of calls and of pairs, the matrices, and the parts of the two totals. 3,076
    slots are 1,427 of the lookup, 502 of the own part and 1,147 of the smallness test. 1,191 claims
    are 278 of the sub-proof's own and 913 of the smallness test, 838 of them reads.
 2. Printed by the C++ verifier, on a parameter file and a file of scales with these numbers, for a
    model of two such groups. It is not claimed that a file of the repository has them. The two
    totals are in the line that begins
    "read: sub-proof A_0: 1191 claims listed (tested at the chain's end), 3076 slots"
    (verifier/src/vf_segments.inc), which it prints when it checks a proof. That proof was made by a
    build of the repository's cp_commit and cp_prove for tests, on synthetic weights, and is not in
    the repository. The rows and columns of the eight arrays are printed by the call
    cp_verify -plan request with the option -arrays, which also needs a request file and a reply
    file. PXo is the array M6 of the layer sub-proof there.
 3. Printed by no program of the repository: the 2,073,344 equations of the smallness test, which
    with the 1,191 claims are the 2,074,535 rows of the last batching round. The number was recorded
    from a run of the C++ verifier with added lines that only print (its routine equationsF). That
    build is not part of the repository, so a reader cannot repeat it. The same run printed the
    matrices, and the seven arrays that the link commits to, as they are expected here.
-/
import OnBytes.Model.AttentionPlan

namespace OnBytes.Attention

/-- The small configuration. -/
def smallCfg : Cfg :=
  { lt := 6, lB := 4, lgk := 1, ldh := 7, ll := 2, S := 12, rx := 8, kFD := 16, lmS := 11, la := 8,
    lmb := 13, nmin := 20, H := 4, sh := #[12, 12, 12, 12], wcH := 64, wcO := 128, wcQ := 128,
    NAs := 1, Ty := 2 ^ 18,
    lines := [⟨"KR", .kr, [.rm, .rd]⟩, ⟨"KFD", .kfd, [.fm, .fd]⟩, ⟨"R16", .r16, [.wl, .ix]⟩,
      ⟨"WH", .wh, [.wh]⟩] }

/-- The counts over the calls, the scalars, the claims, the reads and the length of U3. -/
def smallCounts : Option (Counts × Nat × Nat × Nat × Nat) :=
  (shapeHid 24 smallCfg).toOption.map fun x =>
    let c := Counts.of x.1
    (c, ownScalars x.1 x.2 c, ownClaims x.1 x.2 c, tableReads x.1 c, x.1.tableElems)

-- two plane messages of 3; two score segments: 7 + 52 and 7 + 49 scalars, 8 pieces each
#guard (smallCounts.map fun x => (x.1.msg, x.1.sumNp, x.1.nKRp, x.1.nKFp, x.1.score)) ==
  some (6 + 59 + 56, 16, 2, 2, #[(11, 8), (10, 8)])
-- scalars, claims, reads, the length of U3
#guard (smallCounts.map (·.2)) == some (1427 + 502, 278, 838, 34152)

-- the matrices: name, rows, columns, kind, number; the number of qa is arbitrary
#guard ((shapeHid 24 smallCfg).toOption.map fun x =>
    (matrices x.1 { gid := 4, midQ := 518 }).map fun M => (M.name, M.m, M.k, M.kind, M.aId)) ==
  some #[("as0", 2048, 120, 0, 1024), ("ah", 4096, 4, 0, 1025), ("ao", 8192, 32, 0, 1026),
    ("bA", 8192, 1024, 0, 1027), ("qa", 8192, 96, 1, 518)]

/-- The plan of the small configuration's first attention sub-proof. The target hb and the number of
qa are arbitrary. -/
def smallPlan : Except String Plan :=
  plan { tau := 128, lidb := 24, hb := 64 } { hb := 64, gid := 4, ktO := 96, aO := 2, midQ := 518 }
    smallCfg

-- slots, scalars, claims, calls, pairs, the length of U3, the rows of the last batching round
#guard (smallPlan.toOption.map fun P => (P.ns, P.nMsg, P.nLin, P.NC, P.NP, P.nW, P.own.rows)) ==
  some (3076, 3076, 1191, 4, 8, 34152, 2074535)
-- the arrays in list order: name, rows, columns
#guard (smallPlan.toOption.map fun P => P.seam.Fp.trees.map fun X => (X.name, X.R, X.K)) ==
  some #[("U3", 1, 34152), ("PK0", 683, 120), ("PK1", 1366, 4), ("PK2", 2731, 32),
    ("PK3", 2731, 1024), ("ZZ", 128, 61440), ("BZ", 32, 2048), ("PXo", 2731, 96)]
-- U3 is the first array; the list is closed
#guard (smallPlan.toOption.map fun P => (P.iU3, P.seam.Tp.planned)) == some (0, true)

/-- The name under which something is refused. Returns none if it is made. -/
def refusal {α : Type} (r : Except String α) : Option String :=
  match r with
  | .error e => some e
  | .ok _ => none

-- qa must fill its owner's array, from its first column on
#guard refusal (plan { tau := 128, lidb := 24, hb := 64 } { hb := 64, ktO := 95, aO := 2 } smallCfg)
  == some "internal-a-TX-place"
#guard refusal (plan { tau := 128, lidb := 24, hb := 64 }
  { hb := 64, ktO := 96, aO := 2, col0Q := 1 } smallCfg) == some "internal-a-TX-place"
-- The first three tests of the plan, in their order. In the first guard all three conditions fail,
-- and in the second the last two.
#guard refusal (plan {} {} { smallCfg with Ty := 1 }) == some "hid-hb"
#guard refusal (plan {} { hb := 1 } { smallCfg with Ty := 1 }) == some "hid-a-owner-uses"
#guard refusal (plan {} { hb := 1, aO := 2 } { smallCfg with Ty := 1 }) == some "internal-a-Ty"
-- a matrix of a kind that an attention sub-proof does not have
#guard refusal (Seam.shape { tau := 128, lidb := 24 } #[{ kind := 2 }] 128 0 0 1) ==
  some "hid-a-weight-matrix"
-- the list of matrices has at most 256 members: 252 parts of `as` pass this test, 253 do not
#guard refusal (plan { tau := 128, lidb := 24, hb := 64 } { hb := 64, ktO := 96, aO := 2 }
  { smallCfg with NAs := 253 }) == some "hid-a-fold-list"
#guard refusal (plan { tau := 128, lidb := 24, hb := 64 } { hb := 64, ktO := 96, aO := 2 }
  { smallCfg with NAs := 252 }) != some "hid-a-fold-list"
-- The record of the shared matrix takes i.hb (108 here), not settings.hb. settings.hb is only
-- compared with tau: 128 passes, 129 is refused.
#guard ((plan { tau := 128, lidb := 24, hb := 128 } { hb := 108, ktO := 96, aO := 2 }
  smallCfg).toOption.map fun P => P.seam.tl.plFor.map (·.hb)) == some #[108]
#guard refusal (plan { tau := 128, lidb := 24, hb := 129 } { hb := 64, ktO := 96, aO := 2 }
  smallCfg) == some "policy-tau-hb"
-- the shape in that record has the caller's count of the array's users
#guard (smallPlan.toOption.map fun P => P.seam.tl.plFor.map fun x => x.sh.map (·.a)) ==
  some #[some 2]
-- The six names of planNames that the guards above reach are in that list. Its other three names
-- (internal-a-tree-list, internal-a-claim-count, hid-a-slots) are reached by no guard here.
#guard ["internal-a-TX-place", "hid-hb", "hid-a-owner-uses", "internal-a-Ty", "hid-a-weight-matrix",
  "hid-a-fold-list"].all planNames.contains

end OnBytes.Attention
