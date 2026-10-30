--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Honest/Shape/TestMarksAtRanges.lean: THE THREE MARKS ON THE STRUCTURE IN FRONT OF
THE KEY FILE's PROXIMITY TEST ON THE RANGES, BEHIND THE SUB-PROTOCOL THAT LAYS THE LOOKUPS' ROWS
("rng.0.rows": `layRows`, Johnson/Desc/Key/Link.lean): from an accept of that sub-protocol, at all
values. In the first chain nothing lies between it and the test (Johnson/Desc/Key/Chain1.lean).
Steps of the verifier's: nothing is shown of any prover.

  `layRows_says`   what an accept says: the ranges' group held no open row and its test had not
      begun; the rows that the lookups have written are laid by ONE call of the ground's
      `addRowsP`; nothing else of the state is turned.
  ★ `layRows_marks`   behind it: the first mark (`stTidyB`) and "no row of the statement has a
      written-out factor" (`stPlainB`) are kept, the second where the written rows have none; AND
      THE MARK ON THE OPEN ROWS (`claimsAtB`, Johnson/Desc/Ground/Shape/Claims.lean) HOLDS AT THE
      RANGES' GROUP FROM NOTHING: in front the group has no open row, and the adding lays the mark
      on what it adds.
  `claims_at_door`   under the guard (`guardK12`, TestSeatAsks.lean) the group's test has not
      begun: so that mark gives the front's named test on the open rows (`claimsB`).
  ★★ `marks_at_door`   so, at the test's structure as the seat makes it of the state behind
      "rng.0.rows": `stTidyB`, `stPlainB` and `claimsB`.

By what. Calls: `addRows_tidy`, `addRows_plain` (Johnson/Desc/Ground/Shape/MoreMarks.lean),
`addRows_claims`, `claimsAt_iff` (Claims.lean), `claimsB_of_mark` (TestClaims.lean),
`testFront_of`, `batOwes_of` (TestDoor.lean), `runRows_plain`.

Limits. THREE PREMISES ARE CARRIED FROM IN FRONT, SHOWN HERE OF NO RUN: the first mark and
`stPlainB` at the state in front of "rng.0.rows", and that no row that the lookups have written has
a written-out factor. That the guard holds at a run's state is a premise. Nothing on the values of
the test's own rounds. Nothing on completeness, on soundness or on what is hidden.


-/
import Johnson.Desc.K12.Honest.Shape.TestSeatAsks
import Johnson.Desc.K12.Honest.Shape.TestClaims
import Johnson.Desc.Ground.Shape.MoreMarks
import Johnson.Desc.Key.Chain1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Sh
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.Ground (addRowsP)
open VerifiableInference.Desc.Key (FirstState layRows lookupsOf quietAt)
open Johnson.Prover.Link

/-- **What an accept of "rng.0.rows" says.** -/
theorem layRows_says {one : OneTime} {s s' : FirstState} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} (h : (layRows one).decide s rs gs = .ok s') :
    ((s.d.st.groups[s.grp]?).any fun G => G.rows.isEmpty && !G.inRun) = true ∧
      ∃ d, addRowsP s.d s.grp s.base.rows.flatten = some d ∧ s' = { s with d := d } := by
  by_cases c1 : s.base.rows.length = (lookupsOf one).length
  · have c1b : (s.base.rows.length == (lookupsOf one).length) = true := beq_iff_eq.2 c1
    cases c2 : ((s.d.st.groups[s.grp]?).any fun G => G.rows.isEmpty && !G.inRun) with
    | false => simp [layRows, quietAt, c1, c2, need, bind, Except.bind] at h
    | true =>
      cases hd : addRowsP s.d s.grp s.base.rows.flatten with
      | none => simp [layRows, quietAt, c1, c2, hd, named, need, bind, Except.bind] at h
      | some d =>
        simp only [layRows, quietAt, c1b, c2, hd, named, need, bind, Except.bind, pure,
          Except.pure, if_true] at h
        exact ⟨rfl, d, rfl, (Except.ok.inj h).symm⟩
  · simp [layRows, quietAt, c1, need, bind, Except.bind] at h

/-- ★ **The three marks behind "rng.0.rows".** -/
theorem layRows_marks {one : OneTime} {s s' : FirstState} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} (h : (layRows one).decide s rs gs = .ok s')
    (ht : stTidyB s.d.st = true) (hp : stPlainB s.d.st = true)
    (hw : ∀ r ∈ s.base.rows.flatten, rowPlainB r = true) :
    stTidyB s'.d.st = true ∧ stPlainB s'.d.st = true ∧ claimsAtB s'.d.st s'.grp = true := by
  obtain ⟨c2, d, hd, rfl⟩ := layRows_says h
  refine ⟨addRows_tidy _ _ _ _ hd ht, addRows_plain _ _ _ _ hd hp hw,
    addRows_claims _ _ _ _ hd _ (claimsAt_iff.2 fun G hG r hr => ?_)⟩
  rw [hG] at c2
  have c3 : (G.rows.isEmpty && !G.inRun) = true := c2
  rw [Bool.and_eq_true] at c3
  have e : G.rows = #[] := Array.isEmpty_iff.1 c3.1
  rw [e] at hr
  cases hr

/-- Under the guard the mark on the open rows gives the front's named test. -/
theorem claims_at_door {p : P12} {t : T12} (hpass : t.pass = .nothing)
    (hg : guardK12 p (coreSh ⟨t.st, t.book, t.roots⟩) t.g t.mask = true)
    (ht : stTidyB t.st = true) (hp : stPlainB t.st = true)
    (hc : claimsAtB t.st t.g = true) : claimsB t = true := by
  obtain ⟨-, g2, ⟨id, hm, -⟩, -, -, -, -, -⟩ := guard_says hg
  rw [← testSh_front hpass] at g2
  unfold doorB at g2
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at g2
  obtain ⟨⟨⟨h1, h2⟩, -⟩, h4⟩ := g2
  have h4' : (match t.mask with
    | some id => cameB (curOf p) (testSh t).core t.g (idxOf p) id
    | none => (testSh t).core.st.oracles.length == (testSh t).core.book.place.length) = true := h4
  rw [hm] at h4'
  obtain ⟨G, H⟩ := testFront_of h1 hm h4' ht fun _ hG => runRows_plain hp hG
  exact claimsB_of_mark H.group (batOwes_of h2 H.group).idle hc

/-- ★★ **THE THREE MARKS AT THE TEST's STRUCTURE AS THE SEAT MAKES IT**, behind "rng.0.rows". -/
theorem marks_at_door {one : OneTime} {p : P12} {s s' : FirstState} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} (h : (layRows one).decide s rs gs = .ok s')
    (ht : stTidyB s.d.st = true) (hp : stPlainB s.d.st = true)
    (hw : ∀ r ∈ s.base.rows.flatten, rowPlainB r = true)
    (hg : guardK12 p (coreSh ⟨s'.d.st, s'.d.book, s'.d.roots⟩) s'.grp s'.rider = true) :
    stTidyB s'.d.st = true ∧ stPlainB s'.d.st = true ∧
      claimsB { st := s'.d.st, book := s'.d.book, roots := s'.d.roots, g := s'.grp
                pass := .nothing, mask := s'.rider } = true := by
  obtain ⟨a1, a2, a3⟩ := layRows_marks h ht hp hw
  exact ⟨a1, a2, claims_at_door (p := p) rfl hg a1 a2 a3⟩

end ProofFile.Honest.Sh

#print axioms ProofFile.Honest.Sh.layRows_says
#print axioms ProofFile.Honest.Sh.layRows_marks
#print axioms ProofFile.Honest.Sh.claims_at_door
#print axioms ProofFile.Honest.Sh.marks_at_door
