-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/LotOwnKeyPointsRead.lean: WHICH CHALLENGES A LOOKUP's LAST KEY POINTS READ. The point of the
claim on the keys of a part (`ptsOf … |>.keyPt p` at the part's number of levels, Honest/K3/Heard.lean) is made of the challenges of
the part's last key level and of the "LINE" behind it. Where these rounds lie below j, the point is read off the first j
challenges. At letters: a face, a base, a bound.

  `lookupElemAt_of_front`, `varChals_of_front`   a round's first element below j, and a sumcheck's challenges that end below j
  `keyPointReadsBelow`, `keyPointsReadBelow`    the public test, as a Bool: for a part; for all parts of a face
  `key_point_of_front`                          under the test the last key point of EVERY part number is read off the first j
                                                challenges: a part that is not there has no level, and its point no coordinate

Limits. Definitions and three small theorems on reading a list by number. Nothing on what a verifier hears. Nothing on
completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K3.Heard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtKey
open ProofFile.Honest.K3 (LFace Stage roundAt varChals ptsOf behind)

/-- A round's first element, below j, is read off the first j challenges. -/
theorem lookupElemAt_of_front {h h' : List Fmt.Drawn} {j : ℕ} (e : h.take j = h'.take j) {i : ℕ}
    (hi : i < j) : ProofFile.Honest.K3.elemAt h i = ProofFile.Honest.K3.elemAt h' i := by
  have g : h[i]? = h'[i]? := by
    rw [← List.getElem?_take_of_lt hi, e, List.getElem?_take_of_lt hi]
  unfold ProofFile.Honest.K3.elemAt ProofFile.Honest.K3.elemsAt
  rw [g]

/-- A sumcheck's first n variables' challenges, where they end below j. -/
theorem varChals_of_front {h h' : List Fmt.Drawn} {j : ℕ} (e : h.take j = h'.take j) (f : LFace)
    (base : ℕ) (s : Stage) (n : ℕ) (hb : roundAt f base s + 1 + n ≤ j) :
    varChals f base h s n = varChals f base h' s n := by
  unfold varChals
  refine List.map_congr_left fun l hl => lookupElemAt_of_front e ?_
  have := List.mem_range.1 hl
  omega

/-- **The public test for a part**: the rounds of its last key level, and the "LINE" behind it, lie below j. -/
def keyPointReadsBelow (f : LFace) (base j p : ℕ) : Bool :=
  match f.parts.getD p 0 with
  | 0 => true
  | m + 1 => decide (roundAt f base (.key p m) + 1 + m ≤ j) &&
      decide (roundAt f base (.keyLine p m) < j)

/-- **The public test for a face**: at all its parts. -/
def keyPointsReadBelow (f : LFace) (base j : ℕ) : Bool :=
  (List.range f.parts.length).all (keyPointReadsBelow f base j)

/-- **Under the test a part's last key point is read off the first j challenges**, at every part number. -/
theorem key_point_of_front {f : LFace} {base j : ℕ} (hB : keyPointsReadBelow f base j = true)
    {h h' : List Fmt.Drawn} (e : h.take j = h'.take j) (p : ℕ) :
    (ptsOf f base h).keyPt p (f.parts.getD p 0) = (ptsOf f base h').keyPt p (f.parts.getD p 0) := by
  by_cases hp : p < f.parts.length
  · have g : keyPointReadsBelow f base j p = true :=
      List.all_eq_true.1 hB p (List.mem_range.2 hp)
    unfold keyPointReadsBelow at g
    generalize f.parts.getD p 0 = n at g ⊢
    cases n with
    | zero => rfl
    | succ m =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at g
      show behind m (f.orders p m) (varChals f base h (.key p m) m)
          (ProofFile.Honest.K3.elemAt h (roundAt f base (.keyLine p m))) =
        behind m (f.orders p m) (varChals f base h' (.key p m) m)
          (ProofFile.Honest.K3.elemAt h' (roundAt f base (.keyLine p m)))
      rw [varChals_of_front e f base (.key p m) m g.1, lookupElemAt_of_front e g.2]
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hp)]
    rfl

end ProofFile.Honest.K12.AtKey

#print axioms ProofFile.Honest.K12.AtKey.lookupElemAt_of_front
#print axioms ProofFile.Honest.K12.AtKey.varChals_of_front
#print axioms ProofFile.Honest.K12.AtKey.keyPointReadsBelow
#print axioms ProofFile.Honest.K12.AtKey.keyPointsReadBelow
#print axioms ProofFile.Honest.K12.AtKey.key_point_of_front
