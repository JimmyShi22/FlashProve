-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Slice/BlkCsKept.lean: what a form on a kept member's main table, carried over by the
program's code switch, adds to a row, in the field.

A kept member of the old group is sent a second time, as an oracle message of its own. Its table is
the old one except at the places of the pad of its sample: there the new message has a new pad, and
the old pad's entries lie in the rest, in the new oracle message g. `switchAddKept`
(OnBytes/Iop/Cs.lean) carries a form on the old main table over: to the same entries of the new
message, but at the pad's places to where the old pad is in g. Definitions, statements and proofs.
Main names:
  `padTerm`: what one place of the old pad adds. `coefAt_padLoop`: the loop over the pad's places.
  `coefAt_addKept`: the row's coefficient (`coefAt`) behind `switchAddKept`, on every entry of every
    table: the one before, the form on the new message's main table, and the pad's terms. No
    premise.
  `sum_zipIdx`, `sum_zipIdx_fst`, `sum_index`: sums over a numbered list.
  `addKept_new`: on the new message's main table: the form's entries, but 0 at the pad's places; if
    the new message is not g and no two places of the pad have one index.
  `addKept_g`: on the table of g that takes the rest: the form's entries at the pad's places, at the
    places `places.get (oldPadAt + k)` (`stretchAt`, OnBytes/Slice/BlkCsStretch.lean); if the new
    message is not g.
  `addKept_other`: every other table is left as it was.
Limits: that the new message is not g, and that the pad's places have different indices, are
premises. A pad's place is read by its index alone: that it lies in the main table is not asked.
Nothing on the run of the block. Nothing on soundness.

-/
import OnBytes.Slice.BlkCsStretch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Slice

/-- What one place of the old pad adds: the form's entry there is taken off the new message and laid
where the old pad is in g. -/
def padTerm (anew g : ℕ) (restPart : Part) (places : SwitchPlaces) (oldPadAt : ℕ) (c : Form)
    (o : ℕ) (part : Part) (J : ℕ) (p : PadPlace × ℕ) : GE :=
  (if anew == o && Part.main == part && p.1.index == J then -formAt c p.1.index else 0) +
    if g == o && restPart == part && places.get (oldPadAt + p.2) == J then formAt c p.1.index
    else 0

/-- The loop over the pad's places. -/
theorem coefAt_padLoop (anew g : ℕ) (restPart : Part) (places : SwitchPlaces) (oldPadAt : ℕ)
    (c : Form) (o : ℕ) (part : Part) (J : ℕ) : ∀ (l : List (PadPlace × ℕ)) (row : Row),
    coefAt (l.foldl
      (fun r p =>
        let there := c.entry p.1.index
        (r.addUnit anew .main p.1.index (negE there)).addUnit g restPart
          (places.get (oldPadAt + p.2)) there) row) o part J =
      coefAt row o part J +
        (l.map (padTerm anew g restPart places oldPadAt c o part J)).sum
  | [], _ => by simp
  | p :: l, row => by
    rw [List.foldl_cons, coefAt_padLoop anew g restPart places oldPadAt c o part J l,
      coefAt_addUnit, coefAt_addUnit, List.map_cons, List.sum_cons, readE_neg]
    unfold padTerm formAt
    ring

/-- **A form on a kept member, carried over**: no premise. -/
theorem coefAt_addKept (row : Row) (pad : List PadPlace) (anew g : ℕ) (restPart : Part)
    (places : SwitchPlaces) (oldPadAt : ℕ) (c : Form) (o : ℕ) (part : Part) (J : ℕ) :
    coefAt (switchAddKept row pad anew g restPart places oldPadAt c) o part J =
      coefAt row o part J + (if anew == o && part == .main then formAt c J else 0) +
        (pad.zipIdx.map (padTerm anew g restPart places oldPadAt c o part J)).sum := by
  unfold switchAddKept
  rw [coefAt_padLoop, coefAt_addForm]

/-! ## Closed forms -/

/-- A sum over a numbered list, as a sum over the numbers. -/
theorem sum_zipIdx (F : PadPlace → ℕ → GE) : ∀ (l : List PadPlace) (n : ℕ),
    ((l.zipIdx n).map fun p => F p.1 p.2).sum =
      ∑ k ∈ Finset.range l.length, F (l.getD k default) (n + k)
  | [], _ => by simp
  | a :: l, n => by
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, sum_zipIdx F l (n + 1), List.length_cons,
      Finset.sum_range_succ']
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [List.getD_cons_succ]
    congr 1
    omega

/-- A sum over a numbered list that does not read the numbers. -/
theorem sum_zipIdx_fst (G : PadPlace → GE) : ∀ (l : List PadPlace) (n : ℕ),
    ((l.zipIdx n).map fun p => G p.1).sum = (l.map G).sum
  | [], _ => rfl
  | a :: l, n => by
    rw [List.zipIdx_cons, List.map_cons, List.map_cons, List.sum_cons, List.sum_cons,
      sum_zipIdx_fst G l (n + 1)]

/-- A sum that at most one place of the pad hits. -/
theorem sum_index (f : ℕ → GE) (J : ℕ) : ∀ l : List PadPlace, (l.map (·.index)).Nodup →
    (l.map fun p => if p.index == J then f p.index else 0).sum =
      if J ∈ l.map (·.index) then f J else 0
  | [], _ => by simp
  | a :: l, h => by
    rw [List.map_cons, List.nodup_cons] at h
    rw [List.map_cons, List.sum_cons, sum_index f J l h.2]
    by_cases e : a.index = J
    · subst e
      simp [h.1]
    · have e' : ¬ J = a.index := fun k => e k.symm
      simp [e, e']

section
variable (row : Row) (pad : List PadPlace) (anew g : ℕ) (restPart : Part)
  (places : SwitchPlaces) (oldPadAt : ℕ) (c : Form)

/-- On the new message's main table: the form's entries, but 0 at the pad's places. -/
theorem addKept_new (hg : anew ≠ g) (hn : (pad.map (·.index)).Nodup) (J : ℕ) :
    coefAt (switchAddKept row pad anew g restPart places oldPadAt c) anew .main J =
      coefAt row anew .main J + if J ∈ pad.map (·.index) then 0 else formAt c J := by
  rw [coefAt_addKept, add_assoc]
  congr 1
  have hg' : (g == anew) = false := beq_false_of_ne fun k => hg k.symm
  have e : pad.zipIdx.map (padTerm anew g restPart places oldPadAt c anew .main J) =
      pad.zipIdx.map fun p =>
        (fun q : PadPlace => if q.index == J then (fun i => -formAt c i) q.index else 0) p.1 := by
    refine List.map_congr_left fun p _ => ?_
    unfold padTerm
    simp [hg']
  rw [e, sum_zipIdx_fst
    (fun q : PadPlace => if q.index == J then (fun i => -formAt c i) q.index else 0) pad 0]
  rw [sum_index (fun i => -formAt c i) J pad hn]
  by_cases hJ : J ∈ pad.map (·.index)
  · simp [hJ]
  · simp [hJ]

/-- On the table of g that takes the rest: the form's entries at the pad's places, laid where the
old pad is. -/
theorem addKept_g (hg : anew ≠ g) (J : ℕ) :
    coefAt (switchAddKept row pad anew g restPart places oldPadAt c) g restPart J =
      coefAt row g restPart J +
        stretchAt places oldPadAt pad.length (fun k => formAt c (pad.getD k default).index) J := by
  rw [coefAt_addKept]
  have hg' : (anew == g) = false := beq_false_of_ne hg
  have e : pad.zipIdx.map (padTerm anew g restPart places oldPadAt c g restPart J) =
      pad.zipIdx.map fun p => (fun (q : PadPlace) (k : ℕ) =>
        if places.get (oldPadAt + k) = J then formAt c q.index else 0) p.1 p.2 := by
    refine List.map_congr_left fun p _ => ?_
    unfold padTerm
    simp [hg']
  rw [e, sum_zipIdx (fun (q : PadPlace) (k : ℕ) =>
    if places.get (oldPadAt + k) = J then formAt c q.index else 0) pad 0]
  unfold stretchAt
  simp [hg']

/-- Every other table is left as it was. -/
theorem addKept_other (o : ℕ) (part : Part) (h1 : ¬ (o = anew ∧ part = .main))
    (h2 : ¬ (o = g ∧ part = restPart)) (J : ℕ) :
    coefAt (switchAddKept row pad anew g restPart places oldPadAt c) o part J =
      coefAt row o part J := by
  rw [coefAt_addKept]
  have a1 : (anew == o && part == .main) = false := by
    by_contra k
    simp only [Bool.not_eq_false, Bool.and_eq_true, beq_iff_eq] at k
    exact h1 ⟨k.1.symm, k.2⟩
  have a1' : (anew == o && Part.main == part) = false := by
    by_contra k
    simp only [Bool.not_eq_false, Bool.and_eq_true, beq_iff_eq] at k
    exact h1 ⟨k.1.symm, k.2.symm⟩
  have a2 : (g == o && restPart == part) = false := by
    by_contra k
    simp only [Bool.not_eq_false, Bool.and_eq_true, beq_iff_eq] at k
    exact h2 ⟨k.1.symm, k.2.symm⟩
  have e : pad.zipIdx.map (padTerm anew g restPart places oldPadAt c o part J) =
      pad.zipIdx.map fun _ => (0 : GE) := by
    refine List.map_congr_left fun p _ => ?_
    unfold padTerm
    simp [a1', a2]
  rw [e, a1]
  simp

end

end OnBytes.Slice

#print axioms OnBytes.Slice.coefAt_addKept
#print axioms OnBytes.Slice.addKept_new
#print axioms OnBytes.Slice.addKept_g
#print axioms OnBytes.Slice.addKept_other
