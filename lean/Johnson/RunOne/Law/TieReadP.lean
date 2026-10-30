-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/TieReadP.lean: THE SECOND
READING LEMMA OF THE CLAIMS' TIE: the table's sentence on a claim that reads the planes (worth l
"planes": Johnson/Desc/Key/KeyK3Items.lean: the lead form's worth + scalar · ⟨v, the bits⟩ reads 0)
holds exactly if the kind's law's row rowP, turned or not, has its target as its value
(Johnson/Desc/First/Look/KeyLaw/Statement.lean, SaysAt.lean), at the mask entries and the bits read.

Main names:
  sum_grid: a sum over a · b numbers, as a sum over b rows of a.
  read_planeSum: ⟨v, the bits⟩, read: the sum over planes and rows of the vector's entry times the
    bit.
  plane_iff_rowP: THE IFF, at any family of bits.
  bits_at: the bits by (row, plane), where bit i reads as a table B at (i / 2 ^ mu, i % 2 ^ mu): so
    at bitVecL (TiePlanes.lean) they are the library's Planes.bitsOf.

Object: definitions of the table's files and of K3's files; no block's text.
User: TieDone.lean and TieDoneBack.lean call plane_iff_rowP.
Letters: G, a ledger · home, a table of homes · mk, the mask entries · f, a face · c, a claim that
reads the planes · bit, the bits by number.

Limits. The sentence's side clauses (no entries of virtual rows; slots below the homes' size) are
not treated. Nothing on soundness.
-/
import Johnson.RunOne.Law.TieRead
import Johnson.RunOne.Law.TiePlanes
import Johnson.Desc.Key.KeySumRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.TieReadP
open OnBytes OnBytes.Slice
open OnBytes.Model (Fork Aff)
open VerifiableInference.Desc.K3 (Face PlaneClaim)
open VerifiableInference.Desc.Key (affAt planeSum sumE_read)
open VerifiableInference.Desc.K3.KeyLaw (mfOf valOf rowP valueF pairsF)
open Johnson.RunOne.Law.TieRead

/-- A sum over a · b numbers, as a sum over b rows of a. -/
theorem sum_grid (a : ℕ) (g : ℕ → GE) : ∀ b : ℕ,
    ∑ i ∈ Finset.range (a * b), g i = ∑ t ∈ Finset.range b, ∑ j ∈ Finset.range a, g (j + a * t)
  | 0 => by simp
  | b + 1 => by
    rw [Nat.mul_succ, Finset.sum_range_add, sum_grid a g b, Finset.sum_range_succ]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [Nat.add_comm]

/-- ⟨v, the bits⟩, read. -/
theorem read_planeSum (f : Face) (pairs : List (E × E)) (bit : ℕ → E) :
    readE (planeSum f pairs bit) =
      ∑ j ∈ Finset.range (2 ^ f.mu), ∑ t ∈ Finset.range (2 ^ f.d),
        Lk6.Mid.pairsAt (pairsF pairs) (j + 2 ^ f.mu * t) * readE (bit (j + 2 ^ f.mu * t)) := by
  unfold planeSum
  rw [sumE_read readE readE_zero readE_add, Nat.pow_add, sum_grid, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun t _ => ?_
  rw [readE_mul, Lk6.Mid.entry_read _ rfl]
  show readE oneE * Lk6.Mid.pairsAt (pairsF pairs) _ * _ = _
  rw [readE_one, one_mul]

variable (G : Fork) (home : Array Slot) (mk : Slot → E)

/-- **The sentence on a claim that reads the planes holds exactly if the kind's law's row has its
target as its value.** -/
theorem plane_iff_rowP (f : Face) (c : PlaneClaim) (bit : ℕ → E) (turned : Bool) :
    readE (addE (affAt G home mk c.lead) (mulE c.scalar (planeSum f c.pairs bit))) =
        readE zeroE ↔
      valueF f.mu f.d (rowP G (fun n => home.getD n default) turned c) (fun s => readE (mk s))
        (fun t j => readE (bit (j + 2 ^ f.mu * t))) =
        (rowP G (fun n => home.getD n default) turned c).target := by
  rw [readE_add, readE_mul, read_affAt, read_planeSum, readE_zero]
  have e : ∀ l : PscF.MaskForm,
      ((PscF.scaleForm (-1) l).map fun p : Slot × GE => p.2 * readE (mk p.1)).sum =
        - (l.map fun p => p.2 * readE (mk p.1)).sum := by
    intro l
    unfold PscF.scaleForm
    induction l with
    | nil => simp
    | cons t l ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      ring
  cases turned with
  | true =>
    unfold valueF rowP
    simp only [if_true, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [e]
    constructor
    · intro h
      linear_combination h
    · intro h
      linear_combination h
  | false =>
    unfold valueF rowP
    simp only [Bool.false_eq_true, if_false, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
    constructor
    · intro h
      linear_combination -h
    · intro h
      linear_combination -h

/-- The bits by (row, plane), where bit number i reads as a table at (i / 2 ^ mu, i % 2 ^ mu). -/
theorem bits_at (mu : ℕ) (bit : ℕ → E) (Bt : ℕ → ℕ → GE)
    (h : ∀ i, readE (bit i) = Bt (i / 2 ^ mu) (i % 2 ^ mu)) (t j : ℕ) (hj : j < 2 ^ mu) :
    readE (bit (j + 2 ^ mu * t)) = Bt t j := by
  rw [h, Nat.add_mul_div_left _ _ (Nat.pow_pos (by omega)), Nat.div_eq_of_lt hj, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]

end Johnson.RunOne.Law.TieReadP

#print axioms Johnson.RunOne.Law.TieReadP.read_planeSum
#print axioms Johnson.RunOne.Law.TieReadP.plane_iff_rowP
#print axioms Johnson.RunOne.Law.TieReadP.bits_at
