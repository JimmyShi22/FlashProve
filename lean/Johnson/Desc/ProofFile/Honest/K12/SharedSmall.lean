-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/SharedSmall.lean: the public data of a small made-up shared chain
with its two proximity tests, for tests and for a play in small: the codes, the shape, the two
tests' parameters, the chain's blocks, and the list of its sendings with the labels of
Johnson/G/Sends.lean. Definitions, `#guard` lines and one theorem that Lean's kernel checks by
evaluation.

The example is that of Johnson/Desc/K14/Honest/Toy.lean with two changes. The table of codes has six
more codes, for the two tests' later stages; the first codes keep their numbers. The shape's two
lists of stages, which are placeholders of one stage there, hold the three stages of each test.

  `codes2`, `shape3`, `P3`   the codes, the shape, the shared rounds' parameters
  `nums`, `p`, `numsO`, `pO`   the parameters of the test on G_u and of the test on G_omega
  `chain`        the chain's blocks: the eight sub-protocols, then the two tests at their seats
                 (`Seat.onGu`, `Seat.onGomega`, Johnson/Desc/K12/Seat.lean)
  `listed`       the chain's sendings under their labels, by `Johnson.G.linSharedSends` at `shape3`
  `entries`, `sends`, `chainSends`   the chain's declared entries; each sending with its entry "SEND
                 seed" and the entry after it. The pairing repeats the one inside
                 `Johnson.G.sendsOf`, which reads three files of bytes and cannot be called here;
                 nothing compares the two

What is checked. `sendingsFit` (Johnson/Desc/ProofFile/Honest/K14/SendingsShapes.lean), the check on
the shapes of the two sendings, accepts `P3` (`sendingsFit_P3`), and rejects it with one of two
changes; it asks neither `masksAhead` nor `sharedSplitNeeded`. `linOk` accepts the codes and the
shape. All ten blocks accept their parameters (`planOk`), and the two tests' stages pass `StagesOk`.
The list has six sendings with the written labels and numbers of messages; the chain has as many
entries "SEND seed"; at each, `treesOf` gives the entry's number of roots. The stages in the shape
are those in the two tests' parameters, by code numbers, k and h, and the codes at these numbers are
the stages' codes. The parameters' numbers of rows, who sends the first fresh table, and the roots
before each test are what `H2U.placesLater` (Johnson/Desc/K12/Plan/PlaceOfPlan.lean) computes them
by.

Limits. The fresh table that the test on G_omega sends itself goes in its entry "FOLD epsilon" and
is not in the list, as in Johnson/G/Sends.lean. Written by hand in `p` and `pO`: the first openings,
the first group's and the first tree's number, the two positions at every stage, the work 0, one
answer, `early` = true, the chain's number 2 and the pieces 9 and 10, and the stages' code numbers
(`idx`; a test compares these with the shape); and the one sample in `listed`. `P3` keeps Toy.lean's
placeholder `beforePoint`, which names a message of the first chain. It imports Mathlib through
RunMany.lean. The chain has no front block and no closing block. Nothing is played here. Nothing on
completeness, soundness or hiding.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.K14.Honest.Toy
import Johnson.Desc.K12.Seat
import Johnson.Desc.K12.AtPlan
import Johnson.Desc.ProofFile.Honest.K12.RunMany
import Johnson.G.Sends
import Johnson.Desc.ProofFile.Honest.K14.SendingsShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light.SharedSmall
open OnBytes (Codes)
open OnBytes.Params (LinShape IoppStage)
open Desc.K14 (P14 St blocks)
open Desc.K14.Honest.Toy (codes P shape)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open Johnson.G (Listed linSharedSends)

/-- Toy.lean's codes, and six more for the two tests' later stages. -/
def codes2 : Codes :=
  { base := codes.base ++ #[⟨6, 8, 2⟩, ⟨7, 8, 2⟩, ⟨5, 2, 2⟩, ⟨7, 2, 2⟩]
    mask := codes.mask ++ #[⟨5, 8, 2⟩, ⟨6, 32, 2⟩] }

/-- Toy.lean's shape with the two tests' three stages: code, mask code, k, h. -/
def shape3 : LinShape :=
  { shape with testU := [⟨0, 0, 1, 0⟩, ⟨2, 1, 1, 1⟩, ⟨3, 2, 0, 0⟩]
               testOmega := [⟨1, 0, 1, 0⟩, ⟨4, 1, 1, 1⟩, ⟨5, 2, 0, 0⟩] }
def P3 : P14 := { P with codes := codes2, S := shape3 }

def nums : H2U.TestNums :=
  { rows := 8, work := 0
    stages := [⟨⟨6, 16, 2⟩, ⟨4, 4, 2⟩, 1, 0, 2⟩, ⟨⟨6, 8, 2⟩, ⟨5, 8, 2⟩, 1, 1, 2⟩,
      ⟨⟨7, 8, 2⟩, ⟨6, 32, 2⟩, 0, 0, 2⟩]
    ownMask := false, first := [(⟨6, 9, false, 0⟩, .own 0), (⟨4, 3, false, 2⟩, .own 2)], free := 3
    firstTree := 0 }
def p : P12 := H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ ⟨2, 0, nums, [(0, 0), (2, 1), (3, 2)], 2, 1, true⟩

def numsO : H2U.TestNums :=
  { rows := 3, work := 0
    stages := [⟨⟨5, 4, 2⟩, ⟨4, 4, 2⟩, 1, 0, 2⟩, ⟨⟨5, 2, 2⟩, ⟨5, 8, 2⟩, 1, 1, 2⟩,
      ⟨⟨7, 2, 2⟩, ⟨6, 32, 2⟩, 0, 0, 2⟩]
    ownMask := true, first := [(⟨5, 3, false, 1⟩, .own 1), (⟨4, 3, false, 2⟩, .own 2)], free := 5
    firstTree := 0 }
def pO : P12 := H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ ⟨2, 0, numsO, [(1, 0), (4, 1), (5, 2)], 4, 1, true⟩

/-- The chain's blocks. -/
def chain : List (Block St Unit) :=
  (blocks P3).getD [] ++
    [VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts p),
      VerifiableInference.Desc.K12.Seat.onGomega (proximityTestKind guardedProximityTestParts pO)]

/-- The chain's sendings under their labels. -/
def listed : List Listed := (linSharedSends shape3 1).toOption.getD []

/-- The chain's declared entries, in order. -/
def entries : List Fmt.Entry := chain.flatMap fun b => b.rounds.map (·.entry)

/-- Each sending with its entry "SEND seed" (numbered from 1) and the entry after it. -/
def sends : List Johnson.G.Sending :=
  ((entries.zipIdx.filter fun r => r.1.name == "SEND seed").zip listed).filterMap fun x =>
    (entries[x.1.2 + 1]?).map fun b =>
      ({ entry := x.1.2 + 1, label := x.2.label, sent := x.2.sent, seed := x.1.1, behind := b } :
        Johnson.G.Sending)

/-- The codes and the sendings in the form in which `Johnson.G.sendsOf` gives a chain's. The name
"proof" and the number 1 are chosen here: under them `sendsOf` lists a proof file's shared chain. -/
def chainSends : Johnson.G.ChainSends := ⟨"proof", 1, codes2, sends⟩

def stagesOf (q : P12) : List (ℕ × ℕ × ℕ × ℕ) :=
  (q.idx.zip q.nums.stages).map fun x => (x.1.1, x.1.2, x.2.k, x.2.h)
def asTuples (l : List IoppStage) : List (ℕ × ℕ × ℕ × ℕ) :=
  l.map fun s => (s.code, s.maskCode, s.k, s.h)
def codesFit (q : P12) : Bool :=
  (q.idx.zip q.nums.stages).all fun x =>
    sameCode (codes2.base.getD x.1.1 default) x.2.C &&
      sameCode (codes2.mask.getD x.1.2 default) x.2.Z

/-- The check on the two sendings' shapes accepts `P3`. -/
theorem sendingsFit_P3 : ProofFile.Honest.K14.sendingsFit P3 = true := by decide +kernel

-- it accepts a shape whose first fresh table does not go out with o_u, and one in which o_omega has
-- o_u's code, so that o_sp is not sent: it asks neither masksAhead nor sharedSplitNeeded; it
-- rejects a shape without o_sp's row, and one that names a code which the table of codes lacks
#guard ProofFile.Honest.K14.sendingsFit { P3 with S := { shape3 with masksAhead := false } }
def oneCode : LinShape := { shape3 with omega := { shape3.omega with code := 0 } }
#guard !oneCode.sharedSplitNeeded && ProofFile.Honest.K14.sendingsFit { P3 with S := oneCode }
#guard !ProofFile.Honest.K14.sendingsFit
  { P3 with S := { shape3 with sharedSplit := { shape3.sharedSplit with maskRows := 0 } } }
#guard !ProofFile.Honest.K14.sendingsFit
  { P3 with S := { shape3 with omega := { shape3.omega with code := 99 } } }
-- the library's check on codes and shape
#guard OnBytes.linOk codes2 shape3 && shape3.sharedSplitNeeded && shape3.masksAhead &&
  codes2.lengthsOk
-- all ten blocks accept their parameters; the stages pass StagesOk
#guard chain.all (·.planOk)
#guard (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk && (proximityTestKind guardedProximityTestParts pO : Block T12 Unit).planOk
#guard StagesOk p.nums.stages && StagesOk pO.nums.stages
-- six sendings, their labels, and how many messages each has
#guard listed.map (fun s => (s.label, s.sent.length)) ==
  [("the folded row", 2), ("Omega", 2),
    ("the folded row's test, the code switch of stage 1", 2),
    ("the folded row's test, the code switch of stage 2", 2),
    ("Omega's test, the code switch of stage 1", 2),
    ("Omega's test, the code switch of stage 2", 2)]
-- ten blocks; as many entries "SEND seed" as sendings; at each the trees are the entry's roots
#guard chain.length == 10 && sends.length == 6
#guard (entries.filter fun e => e.name == "SEND seed").length == 6
#guard sends.all fun s => OnBytes.Params.treesOf codes2 s.sent.toArray == some s.seed.roots
-- the stages in the shape are those in the tests' parameters; the codes are the stages' codes
#guard stagesOf p == asTuples shape3.testU && stagesOf pO == asTuples shape3.testOmega
#guard codesFit p && codesFit pO
-- the other numbers, by the formulas of H2U.placesLater at one sample
#guard p.nums.rows == shape3.fold.index.answers + shape3.fold.columns + 1 + 2 * 1 &&
  pO.nums.rows == 1 + 2 * 1
#guard p.nums.ownMask == !shape3.masksAhead && pO.nums.ownMask
-- the roots before each test, counted off the chain's entries
#guard p.nums.free ==
  (((chain.take 8).flatMap fun b => b.rounds.map (·.entry.roots)).foldl (· + ·) 0)
#guard pO.nums.free ==
  (((chain.take 9).flatMap fun b => b.rounds.map (·.entry.roots)).foldl (· + ·) 0)

end ProofFile.Honest.K12.Light.SharedSmall

#print axioms ProofFile.Honest.K12.Light.SharedSmall.sendingsFit_P3
#print axioms ProofFile.Honest.K12.Light.SharedSmall.codes2
#print axioms ProofFile.Honest.K12.Light.SharedSmall.shape3
#print axioms ProofFile.Honest.K12.Light.SharedSmall.P3
#print axioms ProofFile.Honest.K12.Light.SharedSmall.nums
#print axioms ProofFile.Honest.K12.Light.SharedSmall.p
#print axioms ProofFile.Honest.K12.Light.SharedSmall.numsO
#print axioms ProofFile.Honest.K12.Light.SharedSmall.pO
#print axioms ProofFile.Honest.K12.Light.SharedSmall.chain
#print axioms ProofFile.Honest.K12.Light.SharedSmall.listed
#print axioms ProofFile.Honest.K12.Light.SharedSmall.entries
#print axioms ProofFile.Honest.K12.Light.SharedSmall.sends
#print axioms ProofFile.Honest.K12.Light.SharedSmall.chainSends
#print axioms ProofFile.Honest.K12.Light.SharedSmall.stagesOf
#print axioms ProofFile.Honest.K12.Light.SharedSmall.asTuples
#print axioms ProofFile.Honest.K12.Light.SharedSmall.codesFit
#print axioms ProofFile.Honest.K12.Light.SharedSmall.oneCode
