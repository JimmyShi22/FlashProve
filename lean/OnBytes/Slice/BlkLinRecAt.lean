-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkLinRecAt.lean: the row of a stored table's record on the folded row, entry by
entry.

OnBytes/Slice/BlkLinRec.lean reads the program's row of the record's answer number i in two parts,
as the program makes it: a vector cut at the message's length, and a mend at each pad. This file
adds the two up (LinF.rec_coef): at an index of the table the row has the coefficient LinF.recW of
the vector's entry that stands there: before the pads the weight of the seed's point; at coordinate
t of the pad of answer a the seed's factor times the basis element number t if a = i, else 0; beyond
the message 0.

Main definition: `LinF.recW`.
Main theorems: `LinF.sum_padList`, `LinF.index_eq`, `LinF.rec_coef`, `LinF.rec_other`.

Not claimed. Nothing on any sample map of the library's.

-/
import OnBytes.Slice.BlkLinRec
import OnBytes.Slice.BlkCross

set_option autoImplicit false

namespace OnBytes.Slice.LinF
open Prob Cb

/-- A sum over the pads, as a sum over the answers and the coordinates. -/
theorem sum_padList (f : ℕ × ℕ → GE) : ∀ n : ℕ,
    ((padList n).map f).sum = ∑ a ∈ Finset.range n, ∑ t ∈ Finset.range 3, f (a, t)
  | 0 => rfl
  | n + 1 => by
    have e : padList (n + 1) = padList n ++ (List.range 3).map fun t => (n, t) := by
      have hr : List.range (n + 1) = List.range n ++ [n] := List.range_succ
      unfold padList
      rw [hr, List.flatMap_append]
      simp
    rw [e, List.map_append, List.sum_append, sum_padList f n, Finset.sum_range_succ]
    refine congrArg (_ + ·) ?_
    simp [List.range_succ, Finset.sum_range_succ, add_assoc]

variable (lay : VectorLay) (u ell answers : ℕ) (z : List GE) (beta : GE) (i : ℕ) (target : GE)

/-- Two entries below the table's size with one index are one entry. -/
theorem index_eq {e e' : ℕ} (h : e < 2 ^ lay.bits) (h' : e' < 2 ^ lay.bits)
    (hi : lay.index e = lay.index e') : e = e' := by
  rw [← entryAt_index lay e h, hi, entryAt_index lay e' h']

/-- **The coefficient of the record's row on entry e of the folded message.** -/
def recW (e : ℕ) : GE :=
  if e < ell - 3 * answers then eqW z.length (fun t => z.getD t 0) e
  else if e < ell then
    (if (e - (ell - 3 * answers)) / 3 = i then
      beta * readE (thetaE ((e - (ell - 3 * answers)) % 3)) else 0)
  else 0

/-- **The row at an index of the table.** -/
theorem rec_coef (hroom : ell ≤ 2 ^ lay.bits) (h3 : 3 * answers ≤ ell) (idx : ℕ)
    (hidx : idx < 2 ^ lay.bits) :
    (rec lay u ell answers z beta i target).coef u .main idx =
      recW ell answers z beta i (lay.entryAt idx) := by
  have he : lay.entryAt idx < 2 ^ lay.bits := entryAt_lt lay idx hidx
  have hie : lay.index (lay.entryAt idx) = idx := index_entryAt lay idx hidx
  generalize lay.entryAt idx = e at he hie
  subst hie
  show (if (u == u && Part.main == Part.main) = true then laid lay _ (lay.index e) else 0) +
    (List.map _ (padList answers)).sum = _
  rw [if_pos (by simp), sum_padList]
  unfold laid
  rw [Nat.mod_eq_of_lt hidx, entryAt_index lay e he]
  beta_reduce
  have hcond : ∀ a t, a < answers → t < 3 →
      ((u == u && Part.main == Part.main &&
        lay.index (ell - 3 * answers + 3 * a + t) == lay.index e) = true ↔
          ell - 3 * answers + 3 * a + t = e) := by
    intro a t ha ht
    simp only [beq_self_eq_true, Bool.true_and, beq_iff_eq]
    constructor
    · exact index_eq lay (lt_of_lt_of_le (by omega) hroom) he
    · intro h
      rw [h]
  unfold recW
  by_cases h1 : e < ell - 3 * answers
  · rw [if_pos h1, if_pos (lt_of_lt_of_le h1 (Nat.sub_le _ _))]
    refine (congrArg (_ + ·)
      (Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun t ht => ?_)).trans (add_zero _)
    refine if_neg fun hc => ?_
    have := (hcond a t (Finset.mem_range.1 ha) (Finset.mem_range.1 ht)).1 hc
    omega
  · rw [if_neg h1]
    by_cases h2 : e < ell
    · rw [if_pos h2, if_pos h2]
      have ha0 : (e - (ell - 3 * answers)) / 3 < answers := by omega
      have ht0 : (e - (ell - 3 * answers)) % 3 < 3 := Nat.mod_lt _ (by decide)
      have hq : ell - 3 * answers + 3 * ((e - (ell - 3 * answers)) / 3) +
          (e - (ell - 3 * answers)) % 3 = e := by omega
      rw [Finset.sum_eq_single ((e - (ell - 3 * answers)) / 3)
        (fun a ha hne => Finset.sum_eq_zero fun t ht => if_neg fun hc => by
          have := (hcond a t (Finset.mem_range.1 ha) (Finset.mem_range.1 ht)).1 hc
          have := Finset.mem_range.1 ht
          omega)
        (fun hn => absurd (Finset.mem_range.2 ha0) hn),
        Finset.sum_eq_single ((e - (ell - 3 * answers)) % 3)
        (fun t ht hne => if_neg fun hc => by
          have := (hcond _ t ha0 (Finset.mem_range.1 ht)).1 hc
          omega)
        (fun hn => absurd (Finset.mem_range.2 ht0) hn),
        if_pos ((hcond _ _ ha0 ht0).2 hq), hq]
      by_cases hi : (e - (ell - 3 * answers)) / 3 = i
      · rw [if_pos hi, if_pos (by rw [hi]; exact beq_self_eq_true i)]
        ring
      · rw [if_neg hi, if_neg (by simpa using hi)]
        ring
    · rw [if_neg h2, if_neg h2, zero_add]
      refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun t ht => if_neg fun hc => ?_
      have := (hcond a t (Finset.mem_range.1 ha) (Finset.mem_range.1 ht)).1 hc
      have := Finset.mem_range.1 ha
      have := Finset.mem_range.1 ht
      omega

/-- **Off the main table of the folded row's oracle message the row has no coefficient.** -/
theorem rec_other (o : ℕ) (part : Part) (idx : ℕ) (h : ¬ (u = o ∧ Part.main = part)) :
    (rec lay u ell answers z beta i target).coef o part idx = 0 := by
  have hb : (u == o && Part.main == part) = false := by
    rw [Bool.eq_false_iff]
    intro hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact h hc
  show (if (u == o && Part.main == part) = true then _ else 0) + (List.map _ _).sum = 0
  rw [hb]
  simp

end OnBytes.Slice.LinF
