-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Tail/EndsRel.lean: the single equations of OnBytes/Tie/Pv/Tail/Ends.lean are the
clauses of the relation after the smallness test's round, and the gaps of its claims.

Statements and proofs. Cb/Pv/Tail/Block.lean has the relation after the round (`relOut`): the digits
are in their tables, every tie holds, every read holds. Cb/Pv/Tail/Claims.lean writes the ties and
reads as forms, Cb/Pv/Tail/ClaimsT.lean gives them exponents.
Main names:
  `thB`: the drawn entries of a matrix, as elements of the ring.
  `relOut_iff_gaps`: `relOut` says: the digits are in their tables, every `tieGap` is 0, every
    `readGap` is 0.
  `tieForm_gap`, `readForm_gap`: the gap of the form of a tie is `tieGap`, that of a read `readGap`.
  `exps_tie`, `exps_read`: the exponents of Cb/Pv/Tail/ClaimsT.lean, at the plan's number of claims,
    `step` and `eqF`, are `eTie` and `eRead`; a read's number is `qOf`.
Limits: nothing here says that `qOf` is one to one, or that it is the order in which the verifier
adds its reads. A read's weights stand on all rows of cells here; in
OnBytes/Tie/Pv/Tail/EndAll.lean a read's equation runs over the rows of its segment alone.
-/
import Cb.Pv.Tail.ClaimsT
import OnBytes.Tie.Pv.Tail.Ends

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail

open Finset Cb.Pv.Tail

section Ring

variable {K : Type} [CommRing K] {s : Size} (Λ : Letters K s)

/-- The drawn entries of matrix μ. -/
def thB (β : Dr s) (μ : Fin s.NM) : Fin s.tau → Fin (s.k μ) → K :=
  fun u c => (((β μ u c).val : ℤ) : K)

theorem sum_ext0 {m : ℕ} (w X : Fin m → K) : ∑ i : Fin m, ext0 w i * X i = ∑ i, w i * X i :=
  sum_congr rfl fun i _ => by rw [ext0, dif_pos i.2]

/-- The relation after the round, by gaps. -/
theorem relOut_iff_gaps (x : Λ.X) (β : Dr s) (msg : Λ.M) (Z : Dig K s) :
    relOut Λ x β msg Z ↔
      (∀ μ u i, Cb.Rng.InTab s.lo (Z.zl μ u i) ∧ Cb.Rng.InTab s.hi (Z.zh μ u i)) ∧
      (∀ (μ : Fin s.NM) u (i' : Fin (Alg.symRows (s.m μ))),
        tieGap (s.rad : ℤ) (s.lo : K) (s.beta : K) (thB β μ) (Λ.sym msg μ) (Z.zl μ) (Z.zh μ) u
          i' = 0) ∧
      (∀ μ u r, readGap (s.lo : K) (s.beta : K) (thB β μ) (ext0 (Λ.w x μ r)) (Λ.tab msg μ r)
        (Z.zl μ) (Z.zh μ) u = 0) := by
  unfold relOut
  refine and_congr_right fun _ => and_congr ?_ ?_
  · refine forall_congr' fun μ => forall_congr' fun u => forall_congr' fun i' => ?_
    unfold tieGap
    rw [sub_eq_zero]
    exact eq_comm
  · refine forall_congr' fun μ => forall_congr' fun u => forall_congr' fun r => ?_
    unfold readGap
    rw [sub_eq_zero, sum_ext0]
    exact eq_comm

end Ring

section Field

variable {K : Type} [Field K] {s : Size} (Λ : Letters K s)

/-- three sums and a constant against a weighted sum of combinations -/
theorem three_gap {n m : ℕ} (lo beta : K) (t y : Fin n → K) (w zl zh : Fin m → K) :
    ∑ c, -t c * y c + (∑ i, w i * zl i + ∑ i, lo * w i * zh i) - beta * ∑ i, w i =
      ∑ i, w i * (zl i + lo * zh i - beta) - ∑ c, t c * y c := by
  have e : ∑ i, w i * (zl i + lo * zh i - beta) =
      (∑ i, w i * zl i + ∑ i, lo * w i * zh i) - beta * ∑ i, w i := by
    rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  have e2 : ∑ c, -t c * y c = -∑ c, t c * y c := by
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun c _ => by ring
  rw [e, e2]
  ring

/-- The gap of the form of a tie. -/
theorem tieForm_gap (β : Dr s) (msg : Λ.M) (Z : Dig K s) (μ : Fin s.NM) (u : Fin s.tau)
    (i' : Fin (Alg.symRows (s.m μ))) :
    (tieForm β μ u i').gap (vals Λ msg Z) =
      tieGap (s.rad : ℤ) (s.lo : K) (s.beta : K) (thB β μ) (Λ.sym msg μ) (Z.zl μ) (Z.zh μ) u
        i' := by
  unfold TWhole.Form.gap tieForm formOf tieGap
  rw [sum_formOf, List.map_append, List.map_append, List.sum_append, List.sum_append,
    List.map_map, List.map_map, List.map_map, Cb.Pv.Tail.sum_finRange, Cb.Pv.Tail.sum_finRange,
    Cb.Pv.Tail.sum_finRange, pack_lin]
  have e : ∑ i, (Z.zl μ u i + (s.lo : K) * Z.zh μ u i - (s.beta : K)) *
        Alg.pack (s.rad : ℤ) (unit i) (i' : ℕ) =
      ∑ i, cf s μ i' i * (Z.zl μ u i + (s.lo : K) * Z.zh μ u i - (s.beta : K)) :=
    sum_congr rfl fun i _ => mul_comm _ _
  rw [e]
  exact three_gap _ _ _ _ _ _ _

/-- The gap of the form of a read. -/
theorem readForm_gap (x : Λ.X) (β : Dr s) (msg : Λ.M) (Z : Dig K s) (μ : Fin s.NM)
    (u : Fin s.tau) (r : Fin (s.nr μ)) :
    (readForm Λ x β μ u r).gap (vals Λ msg Z) =
      readGap (s.lo : K) (s.beta : K) (thB β μ) (ext0 (Λ.w x μ r)) (Λ.tab msg μ r) (Z.zl μ)
        (Z.zh μ) u := by
  unfold TWhole.Form.gap readForm formOf readGap
  rw [sum_formOf, List.map_append, List.map_append, List.sum_append, List.sum_append,
    List.map_map, List.map_map, List.map_map, Cb.Pv.Tail.sum_finRange, Cb.Pv.Tail.sum_finRange,
    Cb.Pv.Tail.sum_finRange, sum_ext0]
  exact three_gap _ _ _ _ _ _ _

end Field

/-! ## The exponents -/

/-- The numbers from which the exponents are made. -/
def pexp (pc : ℕ) (t : TSize) : PExp := ⟨pc, step t.tau, eqF t.tau t.m⟩

theorem exps_tie (pc : ℕ) (t : TSize) (μ : Fin t.size.NM) (u : Fin t.size.tau)
    (i' : Fin (Alg.symRows (t.size.m μ))) :
    ((pexp pc t).exps t).tie μ u i' = eTie pc t.tau t.m μ i' u := rfl

theorem exps_read (pc : ℕ) (t : TSize) (μ : Fin t.size.NM) (u : Fin t.size.tau)
    (r : Fin (t.size.nr μ)) :
    ((pexp pc t).exps t).read μ u r = eRead pc t.tau t.m t.NM (qOf t μ r) u := rfl

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.relOut_iff_gaps
#print axioms OnBytes.Tie.Pv.Tail.tieForm_gap
#print axioms OnBytes.Tie.Pv.Tail.readForm_gap
