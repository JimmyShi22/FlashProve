-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/Shape/TestFinishSix.lean: the proximity test as it is placed at the first
chain's finish (`atFinish`, Johnson/Desc/K12/AtFinish.lean) returns, under a guard of six clauses.
"Returns" means: its decision, and its step, give `.ok` and not a refusal. The guard is
`guardFinish`. The other hypotheses are three marks on the structure before the test, the library's
test on rounds and columns (`Block.Fits`) and one test on values (`valsK12`): see "Hypotheses".
Definitions and theorems.

Why six. `seat_returns` (Johnson/Desc/K12/Honest/Shape/TestSeatAsks.lean) is written for the test's
place in the key file's first chain (Johnson/Desc/Key/Ranges.lean) and takes the guard `guardK12` of
eight clauses. The last two belong to that place. In the proof of `seat_returns` the seventh
(`seatLayB`) proves only `layoutIsStage`, one of the tests that that place makes before the test
(Ranges.lean). The eighth (`endedB`) proves only "the test has run to its end" (`testEnded`,
Ranges.lean), which that place's way out asks (`leaveRanges`, Johnson/Desc/Key/Chain1.lean). The
finish's way out (`leaveFinish`, AtFinish.lean) asks nothing. So whoever lays the whole guard in
front of a step at the finish may stop a run on shapes for a clause that the return does not need.
General in the place. The verifier's state alone: no prover, no coin, no frame for an honest side.
(The frame: Johnson/Desc/ProofFile/Honest/Frame.lean.)

In the list: p is the place (`P12`, Johnson/Desc/K12/Frame.lean): the numbers of a place at which a
proximity test is, among them its stages (`p.nums.stages`; `curOf p` and `nxtOf p`,
TestAtKeyRanges.lean, are the first two, or a default where there is none). The plan is what is
computed from p only. The sub-protocol is `proximityTestKind guardedProximityTestParts p` (Frame.lean;
Johnson/Desc/K12/JoinGuarded.lean): the kind K12's own `Block` (Johnson/Desc/Block.lean), over the
structure t (`T12`, Johnson/Desc/K12/Join.lean). t has the statement `st`, the book of trees `book`,
the count of roots `roots`, the number `g` of the group under test, `pass` (what passes from one
part of the test to the next) and `mask` (the number of the message that holds the present stage's
mask, if it has come). The door is the test's first parts, up to and including the first fold
(TestDoor.lean). s is the first chain's state (`S`, Johnson/Desc/First/State.lean). `atFinish p` is
the sub-protocol inside a way in and a way out (`Block.inside`): `enterFinish s` returns a structure
t or refuses, and `leaveFinish` writes the statement, the book and the count of roots back into s.
The shape c (`CoreSh`, Johnson/Desc/Ground/Shape/Core.lean) is what `coreSh` reads of these three.
The rows that the test takes in are `runRows t.st G` (OnBytes/Slice/BlkBegin.lean), G being group
number `t.g`. The three marks are `stTidyB t.st` (Johnson/Desc/Ground/Shape/Marks.lean), "no row
that the test takes in has a written-out factor" (`PlainRow`, OnBytes/Slice/BlkPlain.lean) and
`claimsB t` (TestDoor.lean). rs are rounds, cols are columns, ft is the number of the chain's first
own tree. `Block.Fits`, `Block.shown` and `Block.want` (Johnson/Top/H0/StepLaws/StepLaws.lean) are
the two tests of `Block.step`, the groups of columns that it shows the decision, and the columns
that it reads. The decision is shown the rounds without their digests (`rs.map noDigest`).

  `finish_returns_six`: where `enterFinish s` returns t, under the hypotheses below: the
    sub-protocol's decision at t returns some t', and the decision of `atFinish p` at s returns s
    with the statement, the book and the count of roots of t'
  `finish_step_returns_six`: under the same hypotheses the step of `atFinish p` at ft, s, rs and
    cols returns some state, with the number of columns that the sub-protocol reads (the length of
    `Block.want`)
  `guardFinish`, `guardFinish_says`, `guardK12_six`, `guardFinish_of_K12`: the first six clauses of
    `guardK12`: the sub-protocol's own test on the plan · the door's Bool · a mask is named, and the
    one tree's seat · the batching's cut · the plan's test from the first stage on · the first
    switch opens one tree of the stage's range; `guardK12` is this guard and its last two clauses;
    where it says yes, so do the six and the eighth. In Lean the six are, in this order: `planOk` of
    the sub-protocol; `doorB` (TestDoor.lean); `mask` is some id, and `seat1B` (TestSeat.lean)
    passes at id and at the number of the tree that the book's shape has for id (0 if it has none);
    `batCut` (Johnson/Prover/Link/FormBat.lean) at the first declared round; `planFromOk`
    (Johnson/Prover/Link/StepPlanOk.lean) from stage number 0 on, at the declared rounds after the
    first and at the codes in the shape; `openA0B` (TestFits.lean). `guardFinish` is the definition.
    `guardFinish_says` states the six as a proposition. `guardK12_six` is the equation of `guardK12`
    with `guardFinish`, `seatLayB` and `endedB` joined by `&&`. `guardFinish_of_K12`: where
    `guardK12` passes, so do `guardFinish` and `endedB`
  `asks_of_six`, `k12_accept_iff_six`, `k12_returns_six`: at a structure t with `t.pass = .nothing`,
    under the six clauses, the three marks and `Block.Fits`. `asks_of_six`: rs has a first round,
    and `OneAsks` (TestReturnsOneIff.lean) holds; the proof is the text of `asks_of_guard`
    (TestSeatAsks.lean), which uses no more than the six. `k12_accept_iff_six`: the sub-protocol's
    decision returns if and only if `valsK12` (TestValsB.lean) passes. `k12_returns_six`: so it
    returns where `valsK12` passes
  `ended_rider`: at `t.pass = .nothing`, under the six clauses and `endedB`, the eighth clause of
    `guardK12`: whatever the sub-protocol's decision returns at t, at any rounds and groups of
    columns, passes `testEnded`: "the test has run to its end"
  `enterFinish_nothing`: what `enterFinish` returns has `pass = .nothing`
  `takenPlainB`, `takenPlainB_iff`, `taken_of_B`, `taken_of_plain`: "no row that the test takes in
    has a written-out factor" as a Bool: of these rows only, not of the whole statement; true where
    the group is not there. The Bool is true if and only if the proposition holds; the direction
    from the Bool has a name of its own; `stPlainB` (Marks.lean), the mark on the whole statement,
    gives the Bool
  `valsFinishSixB`, `valsAtFinishB`, `valsOrIdleB`: definitions: the three marks and `valsK12` as
    one Bool at the structure t; the same at the chain's state s, in two forms. `valsAtFinishB` is
    false where `enterFinish s` refuses: it suits a theorem in which the tests on values are a
    hypothesis. `valsOrIdleB` is true there: it suits whoever has to show the Bool true
  `finish_returns_six_B`, `finish_step_returns_six_B`, `finish_returns_at`, `finish_returns_idle`:
    the theorems from these Bools. The first two: the decision and the step, from `valsFinishSixB`
    at t. The last two: the decision, with the tests on values stated at s. `finish_returns_at`
    takes `valsAtFinishB`, and the guard at whatever `enterFinish s` returns. `finish_returns_idle`
    takes `valsOrIdleB`, and "`enterFinish s` returns t" as a hypothesis of its own. In all four the
    state that is returned is only said to exist

By what. `asks_of_six` takes the guard apart by `guardFinish_says` and calls `planFrom_of_ok`
(StepPlanOk.lean), `k12_letters` (Johnson/Prover/Link/LinkJoinB.lean), `view_of_fits`
(TestFits.lean) and `testSh_front` (TestSeatAsks.lean). `k12_accept_iff_six` is `k12_accept_iff_B`
(TestValsB.lean) at what `asks_of_six` gives. `ended_rider` calls `planFrom_of_ok`,
`ended_of_accept` (Johnson/Desc/ProofFile/Honest/K12/Ended.lean) and `thinSh_front`
(TestSeatAsks.lean). At the finish: `Seat.enterFinish_ok`, `Seat.inside_ok`, `Seat.step_inside`,
`Seat.leaveFinish_ok` (Johnson/Desc/K12/SeatLaws.lean) and `step_iff` (StepLaws.lean). For the Bool
on the rows: `rowPlainB_iff` (Marks.lean) and `runRows_plain` (TestDoor.lean). The theorems from the
Bools unfold them and end in the two main theorems.

Hypotheses of `finish_returns_six` and `finish_step_returns_six`. he: `enterFinish s` returns t. hg:
`guardFinish` passes at p, at the shape of `t.st`, `t.book` and `t.roots`, at `t.g` and at `t.mask`.
ht: `stTidyB t.st` passes. hp: if group number `t.g` is there, every row that the test takes in is a
`PlainRow`. hv: `claimsB t` passes. hF: `Block.Fits ft rs cols` holds of the sub-protocol. hvals:
`valsK12 p t` passes at `rs.map noDigest` and at the groups of `Block.shown ft rs cols`.

Limits.
- All limits of TestReturnsOne.lean, TestValsB.lean and TestFits.lean hold here too.
- One tree at the first stage; the mask has come earlier; no row with a written-out factor among
  those taken in.
- `valsK12` is, under the six, the view's test and the marks, equivalent to the sub-protocol's own
  accept (`k12_accept_iff_six`): all form is spared, nothing of the algebra. The view's test is
  `Block.Fits`. `valsK12` runs the test's own parts (TestValsB.lean): under these hypotheses,
  whoever shows it true shows that the sub-protocol accepts.
- `claimsB` reads values; `stTidyB` reads values at one spot.
- That `enterFinish s` returns is a hypothesis. In `finish_returns_at` it is contained in the Bool:
  `valsAtFinishB` is false where `enterFinish s` refuses.
- What a description puts around `atFinish` is not treated: a name; a guard on the mark of a failed
  test (`guardMark`, Johnson/Desc/ProofFile/Frames1.lean); a guard that the reply is not written
  (`Block.guarded`, Johnson/Desc/SeatGuard.lean).
- What `atFinish p` asks of the plan (its `planOk`) is not treated.
- The guard is evaluated at no place here; that it is true where `guardK12` is, is `guardK12_six`
  (used in `guardFinish_of_K12`).
- Three Bools are true by default: `takenPlainB` where the group is not there; `valsOrIdleB` where
  `enterFinish s` refuses; `valsK12` at a place with fewer than two stages, at no round, and in the
  further cases that TestValsB.lean lists. There a true value is vacuous.
- One statement is proved twice. `asks_of_guard` (TestSeatAsks.lean) is `asks_of_six` with
  `guardFinish_of_K12`: that is not stated in Lean. The two proofs are the same text but for the
  lemma that takes the guard apart; they are written separately, and neither is derived from the
  other.
- So is a second one: `finish_returns` (TestFinishReturns.lean in this folder, not in the library
  yet, which this file does not import) is `finish_returns_six` with `guardFinish_of_K12` and
  `ended_rider`: that is not stated in Lean either. It asks the whole `guardK12`, eight clauses.
- No member stands in this file. That is: in this file no theorem is applied at written values, and
  no state s is given at which `enterFinish s` returns and the guard passes at what it returns.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.Shape.TestSeatAsks
import Johnson.Desc.K12.SeatLaws
import Johnson.Top.H0.StepLaws.StepLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Sh
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Key (testEnded)
open Johnson.Prover.Link
open H2K.JointK (laidS)
open ProofFile.Honest.K12 (endedB ended_of_accept)

/-! ## 1 The guard -/

/-- The guard of six clauses. c: the shape of statement, book and count of roots. g: the group
under test. mask: the first fold's mask. -/
def guardFinish (p : P12) (c : CoreSh) (g : ℕ) (mask : Option ℕ) : Bool :=
  (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk &&
  doorB p (curOf p) (nxtOf p) (((H2K.JointK.laidOf p).take 1).map (·.1)) (idxOf p)
    ((nextOf p).code, (nextOf p).maskCode) ⟨c, g, .nothing, mask⟩ &&
  (mask.any fun id =>
    seat1B (curOf p) (laidS p) c g id (((c.book.place[id]?).map (·.1)).getD 0)) &&
  batCut (((H2K.JointK.laidOf p).take 1).map (·.1)) &&
  planFromOk p (nxtOf p :: p.nums.stages.drop 2) 0 (curOf p) (laidS p) c.st.codes &&
  openA0B (curOf p) (laidS p)

/-- `guardK12` (TestSeatAsks.lean) is this guard and its own last two clauses, `seatLayB` and
`endedB`. -/
theorem guardK12_six (p : P12) (c : CoreSh) (g : ℕ) (mask : Option ℕ) :
    guardK12 p c g mask =
      (guardFinish p c g mask && seatLayB (curOf p) c g && endedB p ⟨c, g, .nothing, mask⟩) := rfl

/-- Where `guardK12` passes, so do the six clauses, and its eighth clause, `endedB`. -/
theorem guardFinish_of_K12 {p : P12} {c : CoreSh} {g : ℕ} {mask : Option ℕ}
    (h : guardK12 p c g mask = true) :
    guardFinish p c g mask = true ∧ endedB p ⟨c, g, .nothing, mask⟩ = true := by
  rw [guardK12_six] at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.2⟩

/-- The six clauses of `guardFinish`, as a proposition. -/
theorem guardFinish_says {p : P12} {c : CoreSh} {g : ℕ} {mask : Option ℕ}
    (h : guardFinish p c g mask = true) :
    (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true ∧
    doorB p (curOf p) (nxtOf p) (((H2K.JointK.laidOf p).take 1).map (·.1)) (idxOf p)
      ((nextOf p).code, (nextOf p).maskCode) ⟨c, g, .nothing, mask⟩ = true ∧
    (∃ id, mask = some id ∧
      seat1B (curOf p) (laidS p) c g id (((c.book.place[id]?).map (·.1)).getD 0) = true) ∧
    batCut (((H2K.JointK.laidOf p).take 1).map (·.1)) = true ∧
    planFromOk p (nxtOf p :: p.nums.stages.drop 2) 0 (curOf p) (laidS p) c.st.codes = true ∧
    openA0B (curOf p) (laidS p) = true := by
  unfold guardFinish at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨g1, g2⟩, g3⟩, g4⟩, g5⟩, g6⟩ := h
  refine ⟨g1, g2, ?_, g4, g5, g6⟩
  cases mask with
  | none => cases g3
  | some id => exact ⟨id, rfl, g3⟩

/-! ## 2 The kind's own sub-protocol -/

/-- `OneAsks` (TestReturnsOneIff.lean) from the six clauses, the three marks and the library's test
on rounds and columns (`Block.Fits`). -/
theorem asks_of_six {p : P12} {t : T12} (hpass : t.pass = .nothing)
    (hg : guardFinish p (coreSh ⟨t.st, t.book, t.roots⟩) t.g t.mask = true)
    (ht : stTidyB t.st = true)
    (hp : ∀ G, t.st.groups[t.g]? = some G → ∀ r ∈ (runRows t.st G).toList, PlainRow r)
    (hv : claimsB t = true) (ft : ℕ) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (hF : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).Fits ft rs cols) :
    ∃ id rB R, rs = rB :: R ∧
      OneAsks p (curOf p) (nxtOf p) (p.nums.stages.drop 2) t (idxOf p)
        ((nextOf p).code, (nextOf p).maskCode) id
        ((((coreSh ⟨t.st, t.book, t.roots⟩).book.place[id]?).map (·.1)).getD 0) rB R
        ((proximityTestKind guardedProximityTestParts p : Block T12 Unit).shown ft rs cols) := by
  obtain ⟨g1, g2, ⟨id, hm, g3⟩, g4, g5, g6⟩ := guardFinish_says hg
  have PF := planFrom_of_ok p _ _ _ _ _ g5
  have hst : p.nums.stages = curOf p :: nxtOf p :: p.nums.stages.drop 2 := PF.2.2.1
  obtain ⟨_, _, ds, os, _, e2, e3⟩ := k12_letters p g1
  obtain ⟨rB, R, hrs, fB, hV⟩ := view_of_fits g1 g4 g5 g6 ft rs cols hF
  exact ⟨id, rB, R, hrs,
    { stages := hst, rounds := ⟨ds, e2⟩, oracles := ⟨os, e3⟩
      door := by rw [testSh_front hpass]; exact g2
      mask := hm, tidy := ht, plain := hp, claims := hv, seat := g3, cutB := g4, plan := g5
      fitB := fB, view := hV }⟩

/-- Where `t.pass` is `.nothing`: under the six clauses, the three marks and `Block.Fits`, the
sub-protocol's decision returns if and only if `valsK12` passes. -/
theorem k12_accept_iff_six {p : P12} {t : T12} (hpass : t.pass = .nothing)
    (hg : guardFinish p (coreSh ⟨t.st, t.book, t.roots⟩) t.g t.mask = true)
    (ht : stTidyB t.st = true)
    (hp : ∀ G, t.st.groups[t.g]? = some G → ∀ r ∈ (runRows t.st G).toList, PlainRow r)
    (hv : claimsB t = true) (ft : ℕ) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (hF : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).Fits ft rs cols) :
    (∃ t', (proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide t (rs.map noDigest)
      ((proximityTestKind guardedProximityTestParts p : Block T12 Unit).shown ft rs cols) = .ok t') ↔
      valsK12 p t (rs.map noDigest)
        ((proximityTestKind guardedProximityTestParts p : Block T12 Unit).shown ft rs cols) = true := by
  obtain ⟨id, rB, R, rfl, A⟩ := asks_of_six hpass hg ht hp hv ft rs cols hF
  exact k12_accept_iff_B A

/-- The decision of the kind's own sub-protocol returns, under the six clauses. -/
theorem k12_returns_six {p : P12} {t : T12} (hpass : t.pass = .nothing)
    (hg : guardFinish p (coreSh ⟨t.st, t.book, t.roots⟩) t.g t.mask = true)
    (ht : stTidyB t.st = true)
    (hp : ∀ G, t.st.groups[t.g]? = some G → ∀ r ∈ (runRows t.st G).toList, PlainRow r)
    (hv : claimsB t = true) (ft : ℕ) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (hF : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).Fits ft rs cols)
    (hvals : valsK12 p t (rs.map noDigest)
      ((proximityTestKind guardedProximityTestParts p : Block T12 Unit).shown ft rs cols) = true) :
    ∃ t', (proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide t (rs.map noDigest)
      ((proximityTestKind guardedProximityTestParts p : Block T12 Unit).shown ft rs cols) = .ok t' :=
  (k12_accept_iff_six hpass hg ht hp hv ft rs cols hF).2 hvals

/-- Under `endedB`, the eighth clause of `guardK12`, besides the six: what the decision returns
passes `testEnded`, "the test has run to its end". -/
theorem ended_rider {p : P12} {t t' : T12} (hpass : t.pass = .nothing)
    (hg : guardFinish p (coreSh ⟨t.st, t.book, t.roots⟩) t.g t.mask = true)
    (hE : endedB p ⟨coreSh ⟨t.st, t.book, t.roots⟩, t.g, .nothing, t.mask⟩ = true)
    (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide t rs gs = .ok t') : testEnded t' = true := by
  obtain ⟨-, -, -, -, g5, -⟩ := guardFinish_says hg
  obtain ⟨⟨_, _, _, _, Pl⟩, -⟩ := planFrom_of_ok p _ _ _ _ _ g5
  exact ended_of_accept p Pl.early Pl.one t t' _ _ hd (by rw [thinSh_front hpass]; exact hE)

/-! ## 3 At the finish -/

/-- What `enterFinish` returns has `pass = .nothing`. -/
theorem enterFinish_nothing {s : S} {t : T12} (he : enterFinish s = .ok t) :
    t.pass = .nothing := by
  obtain ⟨o, -, -, -, rfl⟩ := Seat.enterFinish_ok s t he
  rfl

/-- **The decision of `atFinish p` returns, under the six clauses.** It returns s with the
statement, the book and the count of roots of what the sub-protocol's decision returns. ft: the
number of the chain's first own tree. -/
theorem finish_returns_six {p : P12} {s : S} {t : T12} (he : enterFinish s = .ok t)
    (hg : guardFinish p (coreSh ⟨t.st, t.book, t.roots⟩) t.g t.mask = true)
    (ht : stTidyB t.st = true)
    (hp : ∀ G, t.st.groups[t.g]? = some G → ∀ r ∈ (runRows t.st G).toList, PlainRow r)
    (hv : claimsB t = true) (ft : ℕ) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (hF : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).Fits ft rs cols)
    (hvals : valsK12 p t (rs.map noDigest)
      ((proximityTestKind guardedProximityTestParts p : Block T12 Unit).shown ft rs cols) = true) :
    ∃ t', (proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide t (rs.map noDigest)
        ((proximityTestKind guardedProximityTestParts p : Block T12 Unit).shown ft rs cols) = .ok t' ∧
      (atFinish p).decide s (rs.map noDigest) ((proximityTestKind guardedProximityTestParts p : Block T12 Unit).shown ft rs cols) =
        .ok { s with st := t'.st, book := t'.book, roots := t'.roots } := by
  obtain ⟨t', hd⟩ := k12_returns_six (enterFinish_nothing he) hg ht hp hv ft rs cols hF hvals
  exact ⟨t', hd, (Seat.inside_ok enterFinish (proximityTestKind guardedProximityTestParts p : Block T12 Unit) leaveFinish s _
    _ _).2 ⟨t, t', he, hd, (Seat.leaveFinish_ok s _ t').2 rfl⟩⟩

/-- **The step of `atFinish p` returns, under the six clauses**, with the number of columns that the
sub-protocol reads. -/
theorem finish_step_returns_six {p : P12} {s : S} {t : T12} (he : enterFinish s = .ok t)
    (hg : guardFinish p (coreSh ⟨t.st, t.book, t.roots⟩) t.g t.mask = true)
    (ht : stTidyB t.st = true)
    (hp : ∀ G, t.st.groups[t.g]? = some G → ∀ r ∈ (runRows t.st G).toList, PlainRow r)
    (hv : claimsB t = true) (ft : ℕ) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (hF : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).Fits ft rs cols)
    (hvals : valsK12 p t (rs.map noDigest)
      ((proximityTestKind guardedProximityTestParts p : Block T12 Unit).shown ft rs cols) = true) :
    ∃ s', (atFinish p).step ft s rs cols =
      .ok (s', ((proximityTestKind guardedProximityTestParts p : Block T12 Unit).want ft rs).length) := by
  obtain ⟨t', hd, -⟩ := finish_returns_six he hg ht hp hv ft rs cols hF hvals
  exact ⟨_, (Seat.step_inside ft enterFinish (proximityTestKind guardedProximityTestParts p : Block T12 Unit) leaveFinish s _ rs
    cols _).2 ⟨t, t', he, (step_iff ft _ t t' rs cols _).2 ⟨hF, hd, rfl⟩,
      (Seat.leaveFinish_ok s _ t').2 rfl⟩⟩

/-! ## 4 The tests on values as one Bool -/

/-- No row that the test takes in has a written-out factor, as a Bool. True where the group is
not there. -/
def takenPlainB (t : T12) : Bool :=
  (t.st.groups[t.g]?).all fun G => (runRows t.st G).toList.all rowPlainB

/-- Where the Bool is true, every row that the test takes in is a `PlainRow`. -/
theorem taken_of_B {t : T12} (h : takenPlainB t = true) :
    ∀ G, t.st.groups[t.g]? = some G → ∀ r ∈ (runRows t.st G).toList, PlainRow r := by
  intro G hG r hr
  unfold takenPlainB at h
  rw [hG] at h
  exact rowPlainB_iff.1 (List.all_eq_true.1 h r hr)

/-- The Bool is true if and only if every row that the test takes in is a `PlainRow`. -/
theorem takenPlainB_iff {t : T12} : takenPlainB t = true ↔
    ∀ G, t.st.groups[t.g]? = some G → ∀ r ∈ (runRows t.st G).toList, PlainRow r := by
  refine ⟨taken_of_B, fun h => ?_⟩
  unfold takenPlainB
  cases hG : t.st.groups[t.g]? with
  | none => rfl
  | some G => exact List.all_eq_true.2 fun r hr => rowPlainB_iff.2 (h G hG r hr)

/-- `stPlainB`, the mark on the whole statement, gives the Bool. -/
theorem taken_of_plain {t : T12} (h : stPlainB t.st = true) : takenPlainB t = true := by
  unfold takenPlainB
  cases hG : t.st.groups[t.g]? with
  | none => rfl
  | some G =>
    exact List.all_eq_true.2 fun r hr => rowPlainB_iff.2 (runRows_plain h hG r hr)

/-- The three marks and the test on values (`valsK12`), as one Bool, at a structure t; it is
meant for the structure that `enterFinish` returns. -/
def valsFinishSixB (p : P12) (t : T12) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))) :
    Bool :=
  stTidyB t.st && takenPlainB t && claimsB t && valsK12 p t rs gs

/-- The same at the chain's state: false where `enterFinish s` refuses. That suits a theorem in
which the tests on values are a hypothesis; whoever has to show this Bool true has to show that
`enterFinish s` returns. -/
def valsAtFinishB (p : P12) (s : S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))) :
    Bool :=
  match enterFinish s with
  | .ok t => valsFinishSixB p t rs gs
  | .error _ => false

/-- The same at the chain's state: true where `enterFinish s` refuses: it is vacuous there. That
suits whoever has to show the Bool true; the theorem from it (`finish_returns_idle`) takes
"`enterFinish s` returns" as a hypothesis of its own. -/
def valsOrIdleB (p : P12) (s : S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))) :
    Bool :=
  match enterFinish s with
  | .ok t => valsFinishSixB p t rs gs
  | .error _ => true

/-- The decision of `atFinish p` returns, from `valsFinishSixB` at t. -/
theorem finish_returns_six_B {p : P12} {s : S} {t : T12} (he : enterFinish s = .ok t)
    (hg : guardFinish p (coreSh ⟨t.st, t.book, t.roots⟩) t.g t.mask = true) (ft : ℕ)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (hF : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).Fits ft rs cols)
    (hv : valsFinishSixB p t (rs.map noDigest)
      ((proximityTestKind guardedProximityTestParts p : Block T12 Unit).shown ft rs cols) = true) :
    ∃ s', (atFinish p).decide s (rs.map noDigest)
      ((proximityTestKind guardedProximityTestParts p : Block T12 Unit).shown ft rs cols) =
      .ok s' := by
  unfold valsFinishSixB at hv
  simp only [Bool.and_eq_true] at hv
  obtain ⟨⟨⟨v1, v2⟩, v3⟩, v4⟩ := hv
  obtain ⟨t', -, h⟩ := finish_returns_six he hg v1 (taken_of_B v2) v3 ft rs cols hF v4
  exact ⟨_, h⟩

/-- The step of `atFinish p` returns, from `valsFinishSixB` at t. -/
theorem finish_step_returns_six_B {p : P12} {s : S} {t : T12} (he : enterFinish s = .ok t)
    (hg : guardFinish p (coreSh ⟨t.st, t.book, t.roots⟩) t.g t.mask = true) (ft : ℕ)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (hF : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).Fits ft rs cols)
    (hv : valsFinishSixB p t (rs.map noDigest)
      ((proximityTestKind guardedProximityTestParts p : Block T12 Unit).shown ft rs cols) = true) :
    ∃ s', (atFinish p).step ft s rs cols =
      .ok (s', ((proximityTestKind guardedProximityTestParts p : Block T12 Unit).want ft rs).length) := by
  unfold valsFinishSixB at hv
  simp only [Bool.and_eq_true] at hv
  obtain ⟨⟨⟨v1, v2⟩, v3⟩, v4⟩ := hv
  exact finish_step_returns_six he hg v1 (taken_of_B v2) v3 ft rs cols hF v4

/-- At the chain's state: the tests on values are stated at s (`valsAtFinishB`); the guard is a
hypothesis at whatever `enterFinish s` returns. -/
theorem finish_returns_at {p : P12} {s : S}
    (hg : ∀ t, enterFinish s = .ok t →
      guardFinish p (coreSh ⟨t.st, t.book, t.roots⟩) t.g t.mask = true) (ft : ℕ)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (hF : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).Fits ft rs cols)
    (hv : valsAtFinishB p s (rs.map noDigest)
      ((proximityTestKind guardedProximityTestParts p : Block T12 Unit).shown ft rs cols) = true) :
    ∃ s', (atFinish p).decide s (rs.map noDigest)
      ((proximityTestKind guardedProximityTestParts p : Block T12 Unit).shown ft rs cols) =
      .ok s' := by
  unfold valsAtFinishB at hv
  cases he : enterFinish s with
  | error e =>
    rw [he] at hv
    cases hv
  | ok t =>
    rw [he] at hv
    exact finish_returns_six_B he (hg t he) ft rs cols hF hv

/-- At the chain's state, by `valsOrIdleB`, the Bool that is vacuous where `enterFinish s`
refuses: that `enterFinish s` returns is a hypothesis of its own. -/
theorem finish_returns_idle {p : P12} {s : S} {t : T12} (he : enterFinish s = .ok t)
    (hg : guardFinish p (coreSh ⟨t.st, t.book, t.roots⟩) t.g t.mask = true) (ft : ℕ)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (hF : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).Fits ft rs cols)
    (hv : valsOrIdleB p s (rs.map noDigest)
      ((proximityTestKind guardedProximityTestParts p : Block T12 Unit).shown ft rs cols) = true) :
    ∃ s', (atFinish p).decide s (rs.map noDigest)
      ((proximityTestKind guardedProximityTestParts p : Block T12 Unit).shown ft rs cols) = .ok s' := by
  unfold valsOrIdleB at hv
  rw [he] at hv
  exact finish_returns_six_B he hg ft rs cols hF hv

end ProofFile.Honest.Sh

#print axioms ProofFile.Honest.Sh.guardK12_six
#print axioms ProofFile.Honest.Sh.guardFinish_of_K12
#print axioms ProofFile.Honest.Sh.guardFinish_says
#print axioms ProofFile.Honest.Sh.asks_of_six
#print axioms ProofFile.Honest.Sh.k12_accept_iff_six
#print axioms ProofFile.Honest.Sh.k12_returns_six
#print axioms ProofFile.Honest.Sh.ended_rider
#print axioms ProofFile.Honest.Sh.enterFinish_nothing
#print axioms ProofFile.Honest.Sh.finish_returns_six
#print axioms ProofFile.Honest.Sh.finish_step_returns_six
#print axioms ProofFile.Honest.Sh.taken_of_B
#print axioms ProofFile.Honest.Sh.takenPlainB_iff
#print axioms ProofFile.Honest.Sh.taken_of_plain
#print axioms ProofFile.Honest.Sh.finish_returns_six_B
#print axioms ProofFile.Honest.Sh.finish_step_returns_six_B
#print axioms ProofFile.Honest.Sh.finish_returns_at
#print axioms ProofFile.Honest.Sh.finish_returns_idle
#print axioms ProofFile.Honest.Sh.guardFinish
#print axioms ProofFile.Honest.Sh.takenPlainB
#print axioms ProofFile.Honest.Sh.valsFinishSixB
#print axioms ProofFile.Honest.Sh.valsAtFinishB
#print axioms ProofFile.Honest.Sh.valsOrIdleB
