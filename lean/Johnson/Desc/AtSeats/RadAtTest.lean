-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/RadAtTest.lean: RadAt (Johnson/Desc/AtSeats/MemsAtPlan.lean: the one equation on the
radii that the field mems of PlanAt leaves at the members by the make) AS A TEST WITH
CODE, with its law; the test over all fifty later places; and its accept by Lean's kernel AT THE
WRITTEN LIST's OWN RADII. A law file; no running text imports it. Why. No lemma in the library gives
the VALUE of a radius of these members (they are read off the rows of the sendings at the
three public files). So RadAt stays a named test on public values: here it has code, so that it can
be evaluated at a set of files.
  radAtB n radM ps P rad nT, radAt_of: the test; its accept gives RadAt
  radFiftyB n radM ps q gp: the test at all fifty later places of the first chain's parameters q,
      gp: P := parLater q gp l (k1Ix l d + 1) moment · rad := radRec (3 * l + moment) P (K1's
      files' radii off the written list: FiftyAtFull.lean) · nT := 3 * l + moment + 1
  radW k i: the radius that the written list has for sending number k's i-th oracle message with an
      OOD sample
  rad_written: radFiftyB at radM := radW, the written seats, 82 sendings, the placeholder qFull:
      Lean's kernel: THE WRITTEN LIST AGREES WITH ITSELF ALONG THE TWO ROADS (by sending and place;
      by record and message)
  rad_says: at each of the fifty a plan's seat stands at the message's seat: so the test is true for
      want of a case at none
  rad_rejects: the negative tests: every radius 0 (what the reader P5T.radOf gives where the
      rows have none) · every radius turned by one · one sending's radius alone turned by one:
      each rejects
  rad_one_number: WHAT THE TEST CANNOT SEE: at all fifty the written radius is ONE number
      (2433820): so it does not part one later sending from another: with the sendings' numbers
      shifted by one it still accepts (seen by the evaluator before this file was typed)

What is not claimed. THAT THE MEMBERS' RADII (P5T.radOf of the rows at the files) ARE radW:
no theorem; an evaluation at a set of files can show it there. Nothing on soundness.

-/
import Johnson.Desc.AtSeats.MemsAtPlan
import Johnson.Desc.K1.Law.FiftyAtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes
open IM (k1Ix)
open Johnson.G (sendsFullLit packFullLit)

/-- **RadAt, as a test.** -/
def radAtB (n : ℕ) (radM : ℕ → ℕ → ℕ) (ps : List P5T.PSeat) (P : Par) (rad : ℕ → ℕ) (nT : ℕ) :
    Bool :=
  (List.finRange (shapesOf P).length).all fun j =>
    !decide (sampledAt P j) || (List.range n).all fun k =>
      (P5T.mineAt ps k).zipIdx.all fun y =>
        !(y.1.seat == (nT + (layOf P).tree.getD j.val 0, (layOf P).part.getD j.val 0)) ||
          radM k y.2 == rad j.val

theorem radAt_of {n : ℕ} {radM : ℕ → ℕ → ℕ} {ps : List P5T.PSeat} {P : Par} {rad : ℕ → ℕ} {nT : ℕ}
    (h : radAtB n radM ps P rad nT = true) : RadAt n radM ps P rad nT := by
  intro j hj k hk i p hp hs
  have h1 := List.all_eq_true.1 h j (List.mem_finRange j)
  rw [decide_eq_true hj, Bool.not_true, Bool.false_or] at h1
  have h2 := List.all_eq_true.1 (List.all_eq_true.1 h1 k (List.mem_range.2 hk)) (p, i)
    (List.mem_zipIdx_iff_getElem?.2 hp)
  have h3 : (!(p.seat == (nT + (layOf P).tree.getD j.val 0, (layOf P).part.getD j.val 0)) ||
      radM k i == rad j.val) = true := h2
  rw [hs, beq_self_eq_true, Bool.not_true, Bool.false_or] at h3
  exact eq_of_beq h3

/-- The test at all fifty later places of q, gp. -/
def radFiftyB (n : ℕ) (radM : ℕ → ℕ → ℕ) (ps : List P5T.PSeat) (q : Params.First)
    (gp : _root_.Desc.Plain.GPar) : Bool :=
  (List.range 25).all fun l => [false, true].all fun d =>
    radAtB n radM ps (parLater q gp l (k1Ix l d + 1) (cond d 2 1))
      (radRec (3 * l + cond d 2 1) (parLater q gp l (k1Ix l d + 1) (cond d 2 1)))
      (3 * l + cond d 2 1 + 1)

theorem radFifty_at {n : ℕ} {radM : ℕ → ℕ → ℕ} {ps : List P5T.PSeat} {q : Params.First}
    {gp : _root_.Desc.Plain.GPar} (h : radFiftyB n radM ps q gp = true) (l : ℕ) (hl : l < 25)
    (d : Bool) :
    RadAt n radM ps (parLater q gp l (k1Ix l d + 1) (cond d 2 1))
      (radRec (3 * l + cond d 2 1) (parLater q gp l (k1Ix l d + 1) (cond d 2 1)))
      (3 * l + cond d 2 1 + 1) :=
  radAt_of (List.all_eq_true.1 (List.all_eq_true.1 h l (List.mem_range.2 hl)) d
    (by cases d <;> simp))

/-- The written list's radius of sending k's i-th oracle message with an OOD sample. -/
def radW (k i : ℕ) : ℕ :=
  ((((litAt sendsFullLit packFullLit 2 0)[k]?).bind fun y => y.2.l[i]?).map (·.2)).getD 0

/-- At each of the fifty some plan's seat stands at the seat of the place's message number 0. -/
def radHitsB (n : ℕ) (ps : List P5T.PSeat) (q : Params.First) (gp : _root_.Desc.Plain.GPar) :
    Bool :=
  (List.range 25).all fun l => [false, true].all fun d =>
    (List.range n).any fun k => (P5T.mineAt ps k).any fun y =>
      y.seat == (3 * l + cond d 2 1 + 1 +
          (layOf (parLater q gp l (k1Ix l d + 1) (cond d 2 1))).tree.getD 0 0,
        (layOf (parLater q gp l (k1Ix l d + 1) (cond d 2 1))).part.getD 0 0)

set_option maxRecDepth 1000000 in
/-- **The written list agrees with itself along the two roads.** -/
theorem rad_written : radFiftyB Johnson.G.proofSendsFull.1.sends.length radW P5T.psFull qFull
    ⟨1, 0⟩ = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- It is true for want of a case at none of the fifty. -/
theorem rad_says : radHitsB Johnson.G.proofSendsFull.1.sends.length P5T.psFull qFull ⟨1, 0⟩ =
    true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Negative tests: every radius 0 (what the reader P5T.radOf gives where the rows have none);
every radius turned by one; one sending's radius alone turned by one (number 22: segment 7, the
first later moment). -/
theorem rad_rejects :
    (radFiftyB Johnson.G.proofSendsFull.1.sends.length (fun _ _ => 0) P5T.psFull qFull ⟨1, 0⟩ ||
      radFiftyB Johnson.G.proofSendsFull.1.sends.length (fun k i => radW k i + 1) P5T.psFull qFull
        ⟨1, 0⟩ ||
      radFiftyB Johnson.G.proofSendsFull.1.sends.length
        (fun k i => if k = 22 then radW k i + 1 else radW k i) P5T.psFull qFull ⟨1, 0⟩) =
      false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- What the test cannot see: at all fifty the radius is one number. -/
theorem rad_one_number : ((List.range 25).all fun l => [1, 2].all fun m =>
    radW (3 * l + m) 0 == 2433820) = true := by decide +kernel

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.radAt_of
#print axioms VerifiableInference.Desc.K1.radFifty_at
#print axioms VerifiableInference.Desc.K1.rad_written
#print axioms VerifiableInference.Desc.K1.rad_says
#print axioms VerifiableInference.Desc.K1.rad_rejects
#print axioms VerifiableInference.Desc.K1.rad_one_number
