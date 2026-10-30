-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/NumPieces.lean: A NUMBERING OF THE WEIGHT PANELS' PIECES (`Piece D`,
Cb/Pv/Lay/At/SeamW.lean) IN THE LIST ORDER OF THE PANELS: piece i of panel p has the number
v0Of D p + i, v0Of D p being the number of pieces of the panels that stand before p in `pans D`. For
the letter `num` of the value (Johnson/Road/K4/Value.lean). Numbers alone.

  `offIn c l p`: the sum of c over the members of l in front of the first p.
  `offIn_lt`, `offIn_inj`, `offIn_surj`: the numbers offIn c l p + i, p ∈ l, i < c p, lie below the
    sum of c over l; two of them are equal only for the same p and i; if l has no member twice,
    every number below the sum is one of them.
  `v0Of D p`, `nWK D`: at c := cntB D and l := pans D; the sum.
  `numK D : Fin (nWK D) ≃ Piece D`; `numK_val`: ((numK D).symm ⟨p, i⟩).val = v0Of D p + i.

Limits. THAT THE VERIFIER NUMBERS ITS WEIGHT CLAIMS SO (the walk of its counter over the panels) IS
NOT SAID HERE.
-/
import Cb.Pv.Lay.At.SeamW
import Johnson.Road.FormsKeysSigC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open Inst.Model.FFSeg (Dim Pan pans)
open Cb.Pv.Lay.At (cntB Piece)

/-- The sum of c over the members of l in front of the first p. -/
def offIn (c : Pan → ℕ) : List Pan → Pan → ℕ
  | [], _ => 0
  | q :: l, p => if q = p then 0 else c q + offIn c l p

theorem offIn_lt (c : Pan → ℕ) : ∀ (l : List Pan) (p : Pan) (i : ℕ), p ∈ l → i < c p →
    offIn c l p + i < (l.map c).sum
  | [], _, _, hp, _ => absurd hp List.not_mem_nil
  | q :: l, p, i, hp, hi => by
    simp only [offIn, List.map_cons, List.sum_cons]
    by_cases h : q = p
    · subst h
      rw [if_pos rfl]
      omega
    · rw [if_neg h]
      have := offIn_lt c l p i ((List.mem_cons.1 hp).resolve_left fun e => h e.symm) hi
      omega

theorem offIn_inj (c : Pan → ℕ) : ∀ (l : List Pan) (p q : Pan) (i j : ℕ), p ∈ l → q ∈ l →
    i < c p → j < c q → offIn c l p + i = offIn c l q + j → p = q ∧ i = j
  | [], _, _, _, _, hp, _, _, _, _ => absurd hp List.not_mem_nil
  | a :: l, p, q, i, j, hp, hq, hi, hj, h => by
    simp only [offIn] at h
    by_cases h1 : a = p <;> by_cases h2 : a = q
    · subst h1
      subst h2
      rw [if_pos rfl] at h
      exact ⟨rfl, by omega⟩
    · subst h1
      rw [if_pos rfl, if_neg h2] at h
      omega
    · subst h2
      rw [if_neg h1, if_pos rfl] at h
      omega
    · rw [if_neg h1, if_neg h2] at h
      exact offIn_inj c l p q i j ((List.mem_cons.1 hp).resolve_left fun e => h1 e.symm)
        ((List.mem_cons.1 hq).resolve_left fun e => h2 e.symm) hi hj (by omega)

theorem offIn_surj (c : Pan → ℕ) : ∀ (l : List Pan), l.Nodup → ∀ n, n < (l.map c).sum →
    ∃ p ∈ l, ∃ i, i < c p ∧ offIn c l p + i = n
  | [], _, n, hn => absurd hn (Nat.not_lt_zero n)
  | a :: l, hl, n, hn => by
    simp only [List.map_cons, List.sum_cons] at hn
    by_cases h : n < c a
    · exact ⟨a, List.mem_cons_self, n, h, by simp [offIn]⟩
    · obtain ⟨p, hp, i, hi, e⟩ := offIn_surj c l (List.nodup_cons.1 hl).2 (n - c a) (by omega)
      have hne : a ≠ p := fun e' => (List.nodup_cons.1 hl).1 (e' ▸ hp)
      refine ⟨p, List.mem_cons_of_mem _ hp, i, hi, ?_⟩
      simp only [offIn]
      rw [if_neg hne]
      omega

/-- The number of pieces of the panels that stand before p. -/
def v0Of (D : Dim) (p : Pan) : ℕ := offIn (cntB D) (pans D) p

/-- The number of all pieces. -/
def nWK (D : Dim) : ℕ := ((pans D).map (cntB D)).sum

/-- **The pieces, numbered in the list order of the panels.** -/
noncomputable def numK (D : Dim) : Fin (nWK D) ≃ Piece D :=
  (Equiv.ofBijective
    (fun pc : Piece D => (⟨v0Of D pc.1.1 + pc.2.val,
      offIn_lt (cntB D) (pans D) pc.1.1 pc.2.val pc.1.2 pc.2.isLt⟩ : Fin (nWK D)))
    ⟨fun x y h => by
      obtain ⟨⟨p, hp⟩, i⟩ := x
      obtain ⟨⟨q, hq⟩, j⟩ := y
      obtain ⟨e1, e2⟩ := offIn_inj (cntB D) (pans D) p q i.val j.val hp hq i.isLt j.isLt
        (congrArg Fin.val h)
      subst e1
      have e3 : i = j := Fin.ext e2
      subst e3
      rfl,
    fun n => by
      obtain ⟨p, hp, i, hi, e⟩ := offIn_surj (cntB D) (pans D) (Cb.Pv.Lay.End.Sig.pans_nodup D)
        n.val n.isLt
      exact ⟨⟨⟨p, hp⟩, ⟨i, hi⟩⟩, Fin.ext e⟩⟩).symm

theorem numK_val (D : Dim) (pc : Piece D) :
    ((numK D).symm pc).val = v0Of D pc.1.1 + pc.2.val := rfl

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.numK_val
#print axioms OnBytes.Road.K4.offIn_surj
