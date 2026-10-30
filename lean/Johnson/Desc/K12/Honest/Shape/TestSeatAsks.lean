-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/Shape/TestSeatAsks.lean: a proximity test at its place in the key file's
first chain (`rangesTest`, Johnson/Desc/Key/Ranges.lean). The file defines one test with code on the
plan and on the shape of the structure before the test (`guardK12`). With three marks on that
structure, the library's own test on the block's view (`Block.Fits`) and the test on values with
code (`valsK12`), the guard gives (`seat_returns`): the place's tests before the test
(`asksOnRecord`) return, the test's block accepts, and the place's test after the test (`testEnded`)
is true. "Returns" and "accepts" mean: the value is `.ok` and not a refusal. Definitions and
theorems. All is stated at the test's own structure t: the chain's state is not named here. General
in the place p, in t, in the number ft, in the rounds and in the columns. TestFinishSix.lean and
TestSeatAsksToy.lean in this folder build on this file.

In the list: p is the place (`P12`, Johnson/Desc/K12/Frame.lean): the numbers of a place at which a
proximity test is, among them its stages (`p.nums.stages`). The plan is what is computed from p
only. `curOf p` and `nxtOf p` (TestAtKeyRanges.lean) are the first two stages; `idxOf p` and
`nextOf p` (same file) have the numbers of their codes; each is a default where p has none.
`laidOf p` (Johnson/Desc/K12/Law/ReadsK.lean) lists the place's declared rounds, each with its
oracle messages; `laidS p` is that list without its first element. The block is `proximityTestKind guardedProximityTestParts p`
(Frame.lean; Johnson/Desc/K12/JoinGuarded.lean): a `Block` (Johnson/Desc/Block.lean) over the structure t
(`T12`, Johnson/Desc/K12/Join.lean). t has the statement `st`, the book of trees `book`, the count
of roots `roots`, the number `g` of the group under test, `pass` (what passes from one part of the
test to the next) and `mask` (the number of the message that holds the present stage's mask, if it
has come). The shape c (`CoreSh`, Johnson/Desc/Ground/Shape/Core.lean) is what `coreSh` reads of
`st`, `book` and `roots`. `TestSh` (Johnson/Desc/K12/Honest/Shape/Test.lean) and `ThinSh`
(TestCore.lean) are two shapes of t: each has c, the group's number, a shape of `pass`, and `mask`;
`testSh` and `thinSh` read them off t. The rows that the test takes in are `runRows t.st G`
(OnBytes/Slice/BlkBegin.lean), G being group number `t.g`. The three marks are `stTidyB t.st`
(Johnson/Desc/Ground/Shape/Marks.lean), "every row that the test takes in is a `PlainRow`"
(OnBytes/Slice/BlkPlain.lean: it has no written-out factor) and `claimsB t` (TestDoor.lean). rs are
rounds (`Fmt.RoundView`), cols are columns (`OpenedColumn`, Johnson/Desc/Step.lean), ft is the number of the chain's
first own tree. `Block.Fits` and `Block.shown` (Johnson/Top/H0/StepLaws/StepLaws.lean) are the two
tests of `Block.step`, and the groups of columns that it shows the decision. `noDigest` (Block.lean)
leaves a round's digest out.

  `seat_returns`: nothing is passed in front; the guard; the three marks on the structure in front;
    `Block.Fits`; `valsK12` (TestValsB.lean) at the rounds and groups that the decision is shown:
    then `asksOnRecord` returns, the block's decision returns, and `testEnded` holds of what it
    returns. In Lean, under the seven hypotheses below: `asksOnRecord p t` (Ranges.lean: what the
    place asks before the test) is `.ok ()`; and there is a t' such that the block's `decide` at t,
    `rs.map noDigest` and `Block.shown ft rs cols` is `.ok t'`, and `testEnded t'` (Ranges.lean:
    "the test has run to its end") is true. `leaveRanges` (Johnson/Desc/Key/Chain1.lean), the
    place's way out in the key file's first chain, asks `testEnded`
  `guardK12`: all that is asked of the shape and the plan: the block's test on the plan; `doorB`
    (TestDoor.lean); the mask is named and `seat1B` (TestSeat.lean) holds at its tree; `batCut`;
    `planFromOk` from the first stage on; `openA0B` (TestFits.lean); `seatLayB`; `endedB`
    (Johnson/Desc/ProofFile/Honest/K12/Ended.lean). A definition: a Bool, these eight clauses joined
    by `&&`. In Lean they are, in this order: `planOk` of the block; `doorB` at the `TestSh` made of
    c, g, `.nothing` and mask; mask is some id, and `seat1B` passes at id and at the index in the
    book's list of trees that `c.book.place` has for id (0 if it has none); `batCut`
    (Johnson/Prover/Link/FormBat.lean) at the first declared round; `planFromOk`
    (Johnson/Prover/Link/StepPlanOk.lean) from stage number 0 on, at `laidS p` and at the codes in
    c; `openA0B` at `curOf p` and `laidS p`; `seatLayB` at `curOf p`; `endedB` at the `ThinSh` made
    of c, g, `.nothing` and mask. The stages and the numbers of codes in these clauses are
    `curOf p`, `nxtOf p`, `idxOf p` and `nextOf p` of TestAtKeyRanges.lean
  `guard_says`: where `guardK12` passes, each of its eight clauses holds; the third is stated as
    "there is an id such that mask is some id and `seat1B` passes at id"
  `asks_of_guard`: at `t.pass = .nothing`, under the guard, the three marks and `Block.Fits`: rs is
    a first round rB and a list R, and `OneAsks` (TestReturnsOneIff.lean) holds at p, t, rB, R and
    the groups `Block.shown ft rs cols`. `OneAsks` is the structure of all hypotheses of
    `k12_returns_one` (TestReturnsOne.lean) but the one on the values of the test's own rounds and
    columns. The proof uses the guard's first six clauses only
  `seatLayB cur c g`: a definition: a Bool. Group number g is in the shape c, and `layoutIsStage`
    (Ranges.lean) passes at cur and at the group's layout as it is read off the shape (`layoutS`,
    Johnson/Desc/Ground/Shape/Ground.lean): the layout's four numbers are the stage's
  `testSh_front`, `thinSh_front`: where `t.pass = .nothing`, `testSh t` and `thinSh t` are made of
    the shape of `t.st`, `t.book` and `t.roots`, of `t.g`, of `.nothing` and of `t.mask`: the
    arguments at which the guard calls `doorB` and `endedB`

By what. `asks_of_guard` takes the guard apart by `guard_says` and calls `planFrom_of_ok`
(StepPlanOk.lean), `k12_letters` (Johnson/Prover/Link/LinkJoinB.lean), `view_of_fits`
(TestFits.lean) and `testSh_front`. `seat_returns` has the block's accept from `k12_accept_iff_B`
(TestValsB.lean) at what `asks_of_guard` gives, and `testEnded` from `ended_of_accept` (Ended.lean),
`thinSh_front` and the eighth clause. For `asksOnRecord` it unfolds `doorB` and calls
`testFront_of`, `batOwes_of` and `frontOwes_of` (TestDoor.lean): they give the group, that the
statement is in order (`InOrder`), and three of the place's tests (`pubOk`, `gpOk`, `labelsOk`).
`combineAt_of_order` (Johnson/Prover/Link/DoorV.lean) gives the place's test "every row that the
batching takes lies on the group's tables" (`Means.combineAt`) from a statement in order.
`layoutIsStage` comes from the seventh clause by `grp_get` (Core.lean), `layoutS_eq` (Ground.lean)
and `layoutOf_own` (Johnson/Prover/Link/FormBatLaws.lean). That `t.mask` is some id comes from the
third clause. `layout_eq` (Johnson/Desc/Means/Layout.lean) gives the group's layout.

Hypotheses of `seat_returns`. hpass: `t.pass = .nothing`. hg: `guardK12` passes at p, at the shape
of `t.st`, `t.book` and `t.roots`, at `t.g` and at `t.mask`. ht: `stTidyB t.st` passes. hp: if group
number `t.g` is there, every row that the test takes in is a `PlainRow`. hv: `claimsB t` passes. hF:
`Block.Fits ft rs cols` holds of the block. hvals: `valsK12 p t` passes at `rs.map noDigest` and at
the groups `Block.shown ft rs cols`. `asks_of_guard` has the first six.

Limits.
- All limits of TestReturnsOne.lean, TestValsB.lean and TestFits.lean stand: one tree at the first
  stage; the mask has come; no written-out factor; `valsK12` runs the test's own parts and is, under
  these premises, equivalent to the block's yes.
- `guardK12` fails where its argument mask is `none`.
- Three of the hypotheses are marks that the shape does not hold; one of them (`claimsB`) is a test
  on values. `stTidyB` reads values at one spot (Marks.lean says which).
- What the place asks of the chain's own state (`enterRanges`, Chain1.lean) is not treated here.
- What the place asks of the plan (`asksOnPlan`, Ranges.lean) is not stated here.
- p is a free parameter. The guard is evaluated at no place here, and nothing here ties p to the key
  file's own place (`rangesParams`, Ranges.lean).
- The structure t' that the block returns is only said to exist, with `testEnded t'`.
- One statement is proved twice. `asks_of_six` (TestFinishSix.lean) has the conclusion of
  `asks_of_guard` under the guard's first six clauses and the same other hypotheses. The two proofs
  are the same text but for the lemma that takes the guard apart; neither is derived from the other.
- No values that meet the seven hypotheses of `seat_returns` together are given in this file.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.Shape.TestFits
import Johnson.Desc.K12.Honest.Shape.TestValsB
import Johnson.Desc.K12.Honest.Shape.TestAtKeyRanges
import Johnson.Desc.ProofFile.Honest.K12.Ended
import Johnson.Desc.Key.Ranges
import Johnson.Prover.Link.LinkJoinB
import Johnson.Prover.Link.DoorV

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Sh
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.Ground (has)
open VerifiableInference.Desc.Key (asksOnRecord layoutIsStage behindBatching testEnded)
open Johnson.Prover.Link
open H2K.JointK (laidS)
open ProofFile.Honest.K12 (endedB ended_of_accept)

/-- Group number g is in the shape c, and the four numbers of its layout, read off the shape
(`layoutS`), are those of the stage cur (`layoutIsStage`). False where the group is not there. -/
def seatLayB (cur : Fmt.M1.Stage) (c : CoreSh) (g : ℕ) : Bool :=
  has c.st.groups[g]? fun G => layoutIsStage cur (layoutS c.st G)

/-- One Bool of eight clauses on the plan and on the shape of the structure before the test: the
hypothesis hg of `seat_returns`. c: the shape of statement, book and count of roots. g: the group
under test. mask: the first fold's mask. `⟨c, g, .nothing, mask⟩` is a `TestSh` as the argument of
`doorB` and a `ThinSh` as the argument of `endedB`. -/
def guardK12 (p : P12) (c : CoreSh) (g : ℕ) (mask : Option ℕ) : Bool :=
  (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk &&
  doorB p (curOf p) (nxtOf p) (((H2K.JointK.laidOf p).take 1).map (·.1)) (idxOf p)
    ((nextOf p).code, (nextOf p).maskCode) ⟨c, g, .nothing, mask⟩ &&
  (mask.any fun id =>
    seat1B (curOf p) (laidS p) c g id (((c.book.place[id]?).map (·.1)).getD 0)) &&
  batCut (((H2K.JointK.laidOf p).take 1).map (·.1)) &&
  planFromOk p (nxtOf p :: p.nums.stages.drop 2) 0 (curOf p) (laidS p) c.st.codes &&
  openA0B (curOf p) (laidS p) && seatLayB (curOf p) c g && endedB p ⟨c, g, .nothing, mask⟩

/-- Where the guard passes, each of its eight clauses holds. -/
theorem guard_says {p : P12} {c : CoreSh} {g : ℕ} {mask : Option ℕ}
    (h : guardK12 p c g mask = true) :
    (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true ∧
    doorB p (curOf p) (nxtOf p) (((H2K.JointK.laidOf p).take 1).map (·.1)) (idxOf p)
      ((nextOf p).code, (nextOf p).maskCode) ⟨c, g, .nothing, mask⟩ = true ∧
    (∃ id, mask = some id ∧
      seat1B (curOf p) (laidS p) c g id (((c.book.place[id]?).map (·.1)).getD 0) = true) ∧
    batCut (((H2K.JointK.laidOf p).take 1).map (·.1)) = true ∧
    planFromOk p (nxtOf p :: p.nums.stages.drop 2) 0 (curOf p) (laidS p) c.st.codes = true ∧
    openA0B (curOf p) (laidS p) = true ∧ seatLayB (curOf p) c g = true ∧
    endedB p ⟨c, g, .nothing, mask⟩ = true := by
  unfold guardK12 at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨g1, g2⟩, g3⟩, g4⟩, g5⟩, g6⟩, g7⟩, g8⟩ := h
  refine ⟨g1, g2, ?_, g4, g5, g6, g7, g8⟩
  cases mask with
  | none => cases g3
  | some id => exact ⟨id, rfl, g3⟩

theorem testSh_front {t : T12} (hp : t.pass = .nothing) :
    testSh t = ⟨coreSh ⟨t.st, t.book, t.roots⟩, t.g, .nothing, t.mask⟩ := by
  unfold testSh
  rw [hp]
  rfl

theorem thinSh_front {t : T12} (hp : t.pass = .nothing) :
    thinSh t = ⟨coreSh ⟨t.st, t.book, t.roots⟩, t.g, .nothing, t.mask⟩ := by
  unfold thinSh
  rw [hp]
  rfl

/-- `OneAsks` (TestReturnsOneIff.lean) from the guard, the three marks and the library's test on the
view (`Block.Fits`). The proof uses the guard's first six clauses only. -/
theorem asks_of_guard {p : P12} {t : T12} (hpass : t.pass = .nothing)
    (hg : guardK12 p (coreSh ⟨t.st, t.book, t.roots⟩) t.g t.mask = true)
    (ht : stTidyB t.st = true)
    (hp : ∀ G, t.st.groups[t.g]? = some G → ∀ r ∈ (runRows t.st G).toList, PlainRow r)
    (hv : claimsB t = true) (ft : ℕ) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (hF : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).Fits ft rs cols) :
    ∃ id rB R, rs = rB :: R ∧
      OneAsks p (curOf p) (nxtOf p) (p.nums.stages.drop 2) t (idxOf p)
        ((nextOf p).code, (nextOf p).maskCode) id
        ((((coreSh ⟨t.st, t.book, t.roots⟩).book.place[id]?).map (·.1)).getD 0) rB R
        ((proximityTestKind guardedProximityTestParts p : Block T12 Unit).shown ft rs cols) := by
  obtain ⟨g1, g2, ⟨id, hm, g3⟩, g4, g5, g6, -, -⟩ := guard_says hg
  have PF := planFrom_of_ok p _ _ _ _ _ g5
  have hst : p.nums.stages = curOf p :: nxtOf p :: p.nums.stages.drop 2 := PF.2.2.1
  obtain ⟨_, _, ds, os, _, e2, e3⟩ := k12_letters p g1
  obtain ⟨rB, R, hrs, fB, hV⟩ := view_of_fits g1 g4 g5 g6 ft rs cols hF
  exact ⟨id, rB, R, hrs,
    { stages := hst, rounds := ⟨ds, e2⟩, oracles := ⟨os, e3⟩
      door := by rw [testSh_front hpass]; exact g2
      mask := hm, tidy := ht, plain := hp, claims := hv, seat := g3, cutB := g4, plan := g5
      fitB := fB, view := hV }⟩

/-- **The test at its place returns**: `asksOnRecord`, which the place asks before the test,
returns; the block's decision returns some t'; and `testEnded t'` is true. ft: the number of the
chain's first own tree. -/
theorem seat_returns {p : P12} {t : T12} (hpass : t.pass = .nothing)
    (hg : guardK12 p (coreSh ⟨t.st, t.book, t.roots⟩) t.g t.mask = true)
    (ht : stTidyB t.st = true)
    (hp : ∀ G, t.st.groups[t.g]? = some G → ∀ r ∈ (runRows t.st G).toList, PlainRow r)
    (hv : claimsB t = true) (ft : ℕ) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (hF : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).Fits ft rs cols)
    (hvals : valsK12 p t (rs.map noDigest)
      ((proximityTestKind guardedProximityTestParts p : Block T12 Unit).shown ft rs cols) = true) :
    asksOnRecord p t = .ok () ∧
      ∃ t', (proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide t (rs.map noDigest)
        ((proximityTestKind guardedProximityTestParts p : Block T12 Unit).shown ft rs cols) = .ok t' ∧ testEnded t' = true := by
  obtain ⟨id, rB, R, rfl, A⟩ := asks_of_guard hpass hg ht hp hv ft rs cols hF
  obtain ⟨-, -, -, -, g5, -, g7, g8⟩ := guard_says hg
  obtain ⟨⟨_, _, _, _, Pl⟩, -⟩ := planFrom_of_ok p _ _ _ _ _ g5
  obtain ⟨t', hd⟩ := (k12_accept_iff_B A).2 hvals
  refine ⟨?_, t', hd, ended_of_accept p Pl.early Pl.one t t' _ _ hd
    (by rw [thinSh_front hpass]; exact g8)⟩
  have hD := A.door
  unfold doorB at hD
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hD
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hD
  have h4' : (match t.mask with
    | some id => cameB (curOf p) (testSh t).core t.g (idxOf p) id
    | none => (testSh t).core.st.oracles.length == (testSh t).core.book.place.length) = true := h4
  rw [A.mask] at h4'
  obtain ⟨G, H⟩ := testFront_of h1 A.mask h4' ht hp
  have B := batOwes_of h2 H.group
  have F := frontOwes_of h3 hv H.group
  have a1 : t.mask.isSome = true := by
    rw [A.mask]
    rfl
  have a4 : layoutIsStage (curOf p) (layoutOf t.st G) = true := by
    unfold seatLayB at g7
    have e : (coreSh ⟨t.st, t.book, t.roots⟩).st = stSh t.st := rfl
    rw [e, grp_get, H.group] at g7
    simp only [has, Option.map_some, Option.getD_some] at g7
    rw [layoutS_eq, layoutOf_own H.group] at g7
    exact g7
  have a5 : H2K.First.gpOk p (behindBatching t G (layoutOf t.st G)) = true := (B.gp {} rfl).1
  have a6 : H2K.First.labelsOk p (behindBatching t G (layoutOf t.st G)) = true := (B.gp {} rfl).2
  unfold asksOnRecord
  rw [H.group, layout_eq t.st t.g G H.group, A.stages]
  simp only [a1, F.pub, combineAt_of_order t.st t.g G H.group H.order, a4, a5, a6, need, bind,
    Except.bind, if_true]

end ProofFile.Honest.Sh

#print axioms ProofFile.Honest.Sh.guard_says
#print axioms ProofFile.Honest.Sh.testSh_front
#print axioms ProofFile.Honest.Sh.thinSh_front
#print axioms ProofFile.Honest.Sh.asks_of_guard
#print axioms ProofFile.Honest.Sh.seat_returns
#print axioms ProofFile.Honest.Sh.seatLayB
#print axioms ProofFile.Honest.Sh.guardK12
