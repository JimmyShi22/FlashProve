-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LShapeTest.lean: the clauses `FitsAtL` (ClosingData.lean)
of the first chain's closing proximity test, as a test with code.

`FitsAtL q p Dp s u Ly` has 21 clauses. Eight read the test's parameters q and the sender's place p
alone. Thirteen read the plain data Dp that the verifier's guard makes of its record behind the
batching, at an empty batched row. Of Dp they read the members' seats, the fresh table's seat, the
list of trees, the group's layout, and of the book each tree's depth and width: all of these stand
in the shape of the plain data (`PlainS`, Johnson/Desc/K12/Honest/Shape/TestDoor.lean).

  `seatIsTest`, `seatIsTest_iff`   `SeatIs` (Johnson/Desc/K12/Honest/SentMember.lean) as a Bool
  `closingPlaceTest`            seven of the eight clauses on q, p and the sending's layout
  `closingShapeTest`            the thirteen clauses on the shape of the plain data
  `closingFitsTest`             both, at the layout that `layTrees` returns: the eighth clause
  `closingFitsTest_iff`         the test is true just where `FitsAtL` holds at some seat, tree
                                and layout
  `closingFitsAtShape`          the test at what the guard makes on the thin shape of the state in
                                front
  `closingFitsTest_of_shape`    from the thin shape to the library's plain data
  `treeCount_of_fits`           the plain data have one tree

Who calls it. LSeatsWritten.lean calls `seatIsTest`, `seatIsTest_iff` and `closingPlaceTest`. No law
of LShapeAtHead.lean or behind it calls the tests on a shape (`closingShapeTest`, `closingFitsTest`,
`closingFitsAtShape`) or their laws: there `FitsAtL` comes of `fits_at_every_reached_record`
(LSeatsLaw.lean).

Limits.
- The test is shown true at no parameters and no shape here (`closingSeats_written`,
  LSeatsWritten.lean, is a closed line at the written values, with `closingPlaceTest` among the
  clauses of its test).
- The test says what `FitsAtL` says and no more. The clause on the member's first row reads `oM`,
  which is 0 also where the layout names no first row. No clause asks that the fresh table has no
  main row. The guard's own clauses ask both (`gpL`, Johnson/Desc/K12/Law/FirstOk.lean).
- By a reading, not shown here: where the shape comes from `gpOfS`, the clauses on the list of
  trees, on depth and on width follow from the others, and the guard's own clauses ask three more
  of the thirteen (the fresh table's rows, a degree of 1 or 3, the first row). So fewer than
  thirteen facts are left to the shape.
- Nothing on the prover's rows, on completeness, on soundness or on hiding.
Words, for this file and the files LShape*, LSeats*, LReturns* of this folder.
  the head         the library's premise `P5J.AtMgA` (or `P5J.AtMg`): the three public files are in
                   the goals' scope, and the description of the proof file is laid of them
  border k         in front of member number k of a chain's list of sub-protocols
  reached          a state to which the sub-protocols' accepting steps lead from the chain's first
                   state
  the finish       the last code switch of the first chain, member 353; `finishAt` returns its place
  the blank ground what `ProofFile.blankBy` returns at the public part: a filling is made at it
  the way in       `enterFinish`: from the chain's state to the record T inside the proximity test
  the thin shape   of a record: the shape of statement, book and roots, the group, what is passed,
                   the mask's number (`ThinSh`)
  the thread, a stand, the letters   `Thread`, `Thr`, `FirstThread.Letters` (Honest/Thread/): the
                   honest run's invariant; a border, coins, state and prover's state at which it
                   holds; its open parameters
  a message's seat in LSeats*: the message as a part of a tree (`Seat1`): its shape, the tree's
  place
                   in the book, the part, the tree's shape and number. (RunBySpec.lean's "seat"
                   is another thing: what puts a test's block into a chain.)
  a closed line    a fact on written values alone, shown by `decide +kernel`
  patched          a job whose state on entry is replaced at one input and front (`atStand`)
Further terms: Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingData
import Johnson.Desc.ProofFile.Honest.K12.FrontThin
import Johnson.Desc.K12.Honest.Shape.TestDoor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open OnBytes (TreeLay layTrees Group)
open VerifiableInference.Desc.K12 (P12 T12)
open H2K.First (Plain Seat1 oM kk gpOf)
open Johnson.Prover.Link (batT)
open Johnson.Prover.Send (shapeAt)
open OnBytes.Slice (codeOf)
open ProofFile.Honest.K12 (stA SeatIs)
open ProofFile.Honest.K12.Thin (thin_batT)
open ProofFile.Honest.Sh (PlainS ThinSh thinSh plainSh batThin gpOfS gpOfS_eq logAtS widthAtS logAtS_eq
  widthAtS_eq)

/-- `SeatIs`, clause by clause, as a Bool. -/
def seatIsTest (a : Fmt.M1.Stage) (P : VerifiableInference.Desc.K1.Par) (Ly : TreeLay) (k : ℕ)
    (s : Seat1) : Bool :=
  decide (s.sh = shapeAt P k) &&
  decide (s.tsh = Ly.shapes.getD (Ly.tree.getD k 0) {}) &&
  decide (s.part = Ly.part.getD k 0) &&
  decide (s.sh.mainDeg = 1 ∨ s.sh.mainDeg = 3) &&
  decide (0 < s.sh.mainRows → codeOf (P.codes.base.getD s.sh.code default) = a.C) &&
  decide (0 < s.sh.maskRows → codeOf (P.codes.mask.getD s.sh.maskCode default) = a.Z)

theorem seatIsTest_iff (a : Fmt.M1.Stage) (P : VerifiableInference.Desc.K1.Par) (Ly : TreeLay)
    (k : ℕ) (s : Seat1) : seatIsTest a P Ly k s = true ↔ SeatIs a P Ly k s := by
  unfold seatIsTest
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ => ⟨h1, h2, h3, h4, h5, h6⟩,
    fun H => ⟨⟨⟨⟨⟨H.shape, H.tree⟩, H.part⟩, H.deg⟩, H.codeM⟩, H.codeZ⟩⟩

/-- **Seven of the eight clauses that read the test's parameters, the sender's place and the
sending's layout.** The eighth, that Ly is the sending's layout, is asked in `closingFitsTest`. -/
def closingPlaceTest (q : P12) (p : K2.SwitchPlace) (Ly : TreeLay) : Bool :=
  VerifiableInference.Desc.K1.planOkOwn (parL p) &&
  decide (1 < (parL p).sent.size) &&
  decide ((sentL p).size = 2) &&
  decide (Ly.tree.getD 0 0 = 0) &&
  decide (Ly.tree.getD 1 0 = 0) &&
  decide (0 < Ly.shapes.size) &&
  decide (OnBytes.ceilLog2 (shapeL p).mainRows = kk (stA q))

/-- **The thirteen clauses that read the plain data**, on their shape. False unless there is one
member and one tree. -/
def closingShapeTest (q : P12) (p : K2.SwitchPlace) (Ly : TreeLay) (D : PlainS) : Bool :=
  match D.mems, D.ts with
  | [s], [u] =>
    seatIsTest (stA q) (parL p) Ly 0 s &&
    seatIsTest (stA q) (parL p) Ly 1 D.fresh &&
    decide (s.t = u) &&
    decide (D.fresh.t = u) &&
    decide (D.fresh.sh.maskRows = 2 ^ (stA q).h) &&
    decide (s.sh.mainDeg = 3) &&
    decide (s.sh.maskRows = 0) &&
    decide (s.sh.mainRows = 2 ^ kk (stA q)) &&
    decide (oM D.L 0 = 0) &&
    decide (logAtS D.book u =
      (((VerifiableInference.Desc.Own.treesMade p.sizes.codes (sentL p)).getD {}).shapes.getD 0
        default).logN) &&
    decide (widthAtS D.book u = (Ly.shapes.getD 0 {}).mainWidth + (Ly.shapes.getD 0 {}).maskWidth)
  | _, _ => false

/-- **The test**: all 21 clauses, at the layout that `layTrees` returns. False where it returns
none. -/
def closingFitsTest (q : P12) (p : K2.SwitchPlace) (D : PlainS) : Bool :=
  match layTrees (parL p).codes (parL p).sent with
  | some Ly => closingPlaceTest q p Ly && closingShapeTest q p Ly D
  | none => false

/-- **The test is true at the shape of the plain data just where `FitsAtL` holds** at some seat,
some tree and some layout. -/
theorem closingFitsTest_iff (q : P12) (p : K2.SwitchPlace) (Dp : Plain) :
    closingFitsTest q p (plainSh Dp) = true ↔ ∃ s u Ly, FitsAtL q p Dp s u Ly := by
  constructor
  · intro h
    unfold closingFitsTest at h
    split at h
    · rename_i Ly hLy
      rw [Bool.and_eq_true] at h
      obtain ⟨hp, hs⟩ := h
      unfold closingPlaceTest at hp
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
      obtain ⟨⟨⟨⟨⟨⟨p1, p2⟩, p3⟩, p4⟩, p5⟩, p6⟩, p7⟩ := hp
      unfold closingShapeTest at hs
      split at hs
      · rename_i s u hm ht
        simp only [Bool.and_eq_true, decide_eq_true_eq, seatIsTest_iff] at hs
        obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨s1, s2⟩, s3⟩, s4⟩, s5⟩, s6⟩, s7⟩, s8⟩, s9⟩, s10⟩, s11⟩ := hs
        refine ⟨s, u, Ly, ?_⟩
        exact
          { plan := p1, lay := hLy, two := p2, count := p3, mems := hm, ts := ht, seat := s1
            fresh := s2, tree0 := p4, tree1 := p5, some0 := p6, at0 := s3, at1 := s4, rowsF := s5
            deg := s6, noMask := s7, rows := s8, logRows := p7, first := s9
            depth := (logAtS_eq Dp.book u).symm.trans s10
            width := (widthAtS_eq Dp.book u).symm.trans s11 }
      · cases hs
    · cases h
  · rintro ⟨s, u, Ly, H⟩
    have hm : (plainSh Dp).mems = [s] := H.mems
    have ht : (plainSh Dp).ts = [u] := H.ts
    unfold closingFitsTest
    rw [H.lay]
    show (closingPlaceTest q p Ly && closingShapeTest q p Ly (plainSh Dp)) = true
    rw [Bool.and_eq_true]
    constructor
    · unfold closingPlaceTest
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨⟨⟨⟨H.plan, H.two⟩, H.count⟩, H.tree0⟩, H.tree1⟩, H.some0⟩, H.logRows⟩
    · unfold closingShapeTest
      rw [hm, ht]
      simp only [Bool.and_eq_true, decide_eq_true_eq, seatIsTest_iff]
      exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨H.seat, H.fresh⟩, H.at0⟩, H.at1⟩, H.rowsF⟩, H.deg⟩, H.noMask⟩, H.rows⟩,
        H.first⟩, (logAtS_eq Dp.book u).trans H.depth⟩, (widthAtS_eq Dp.book u).trans H.width⟩

/-- **The test at what the guard makes on the thin shape of the state in front.** False where the
batching returns nothing, where it passes no claim, and where the guard makes no plain data. -/
def closingFitsAtShape (q : P12) (p : K2.SwitchPlace) (a₀ : ThinSh) : Bool :=
  match batThin q a₀ with
  | some aB =>
    match aB.pass with
    | .claim L =>
      match gpOfS q aB (stA q) L with
      | some D => closingFitsTest q p D
      | none => false
    | _ => false
  | none => false

/-- Where the test on the thin shape is true, it is true at the shape of the plain data that the
library's function makes. hPass: the state passes nothing on. hEarly: the masks come early. -/
theorem closingFitsTest_of_shape (q : P12) (p : K2.SwitchPlace) (t : T12)
    (hPass : t.pass = .nothing) (hEarly : q.early = true)
    (h : closingFitsAtShape q p (thinSh t) = true) (G : Group)
    (hG : t.st.groups[t.g]? = some G) (Dp : Plain)
    (hD : gpOf q (batT t G {}) (stA q) (OnBytes.Means.layoutOf t.st G) = some Dp) :
    closingFitsTest q p (plainSh Dp) = true := by
  unfold closingFitsAtShape at h
  split at h
  · rename_i aB hB
    have eT := thin_batT q t G {} aB hPass hEarly hG hB
    split at h
    · rename_i L hL
      have eL : L = OnBytes.Means.layoutOf t.st G := by
        have k : (thinSh (batT t G {})).pass = .claim (OnBytes.Means.layoutOf t.st G) := rfl
        rw [eT, hL] at k
        injection k
      subst eL
      have k := gpOfS_eq q (batT t G {}) (stA q) (OnBytes.Means.layoutOf t.st G)
      rw [eT, hD] at k
      rw [k] at h
      exact h
    · cases h
  · cases h

/-- Under `FitsAtL` the plain data have one tree. -/
theorem treeCount_of_fits {q : P12} {p : K2.SwitchPlace} {Dp : Plain} {s : Seat1} {u : ℕ}
    {Ly : TreeLay} (H : FitsAtL q p Dp s u Ly) : Dp.ts.length = 1 := by
  rw [H.ts]
  rfl

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.seatIsTest
#print axioms ProofFile.Honest.K12.AtProof.seatIsTest_iff
#print axioms ProofFile.Honest.K12.AtProof.closingPlaceTest
#print axioms ProofFile.Honest.K12.AtProof.closingShapeTest
#print axioms ProofFile.Honest.K12.AtProof.closingFitsTest
#print axioms ProofFile.Honest.K12.AtProof.closingFitsTest_iff
#print axioms ProofFile.Honest.K12.AtProof.closingFitsAtShape
#print axioms ProofFile.Honest.K12.AtProof.closingFitsTest_of_shape
#print axioms ProofFile.Honest.K12.AtProof.treeCount_of_fits
