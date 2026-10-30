-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetReadBitsFldBlk.lean: several cells at (feature, position) of one stacked matrix, with one
split into row and column sources, cost, under the premises below, at most Q pieces if they lie in
the parts with numbers below Q (2 · Q if the offsets are no multiples of 2^f), not one for each
cell.

Separable with at most n pieces in the shapes R, C (the numbers of rows and columns of each
segment's matrix), of a function F of a vertex b < 2^v of a cube and of matrices A: at every vertex
b and for all A the value F b A is a constant k b plus at most n pieces, the same at all vertices
(`Sep`, `SepV`, `SPiece`, Cm/TargetReadBits.lean). What a piece is: the sentence "Separable …" of
Cm/TargetReadBitsBlk.lean's head holds here too.

Statements (`Cm.TR.Spec.sep_feats0`, `Cm.TR.Spec.sep_feats`, `Cm.TR.Spec.sep_featsAny`) and their
proofs, in one file. Generic: any field; no model's sizes, but for the height 65,536 of a slot
(`hSlot`, Cm/SegLayout.lean), which `stack` has. They are the three rules of
Cm/TargetReadBitsFld.lean on one cell, said of m cells and derived from the base rule for m cells
(`sep_blocks`, Cm/TargetReadBitsBlk.lean).


Why: a value of a model is Σ_k base^k · (cell k): its cells lie in one matrix, at features that
differ by multiples of 2^f: the same rows in their parts, other columns (a value has an offset too:
`cVal`, Cm/SegPilotKit.lean; the features differ so where 2^f divides the array's width: `ff_clean`,
Cm/TargetReadBitsFldFF.lean). With the rules for one cell and `Spec.sep_sum`
(Cm/TargetReadBits.lean) it would cost (number of cells) · Q pieces; the number of pieces is the
number of reads.

Main names:
  The cells: t the number of the row sources cs, u of the column sources rs, Src.OK (cs ++ rs) v;
    for k < m: the feature φ_k := c k + 2^f · jh k u + jl t, a guard gU k u, a coefficient cf k u;
    shared: the guard gT t, the low digits jl t < 2^f, the position pos t, and c k mod 2^f = c₀ for
    all k. F b A := Σ_{k < m} (if gT t ∧ gU k u then cf k u · A seg (featPl W slot f T φ_k (pos t))
    else 0); under the guards these places lie in the shapes R, C.
  `Spec.sep_feats0`: c₀ = 0, (c k / 2^f + jh k u) / W < Q ⇒ at most Q pieces.
  `Spec.sep_feats`: any c₀, (c k / 2^f + jh k u + 1) / W < Q ⇒ at most 2 · Q pieces.
  `Spec.sep_featsAny`, the fall-back: φ_k := φ k u any functions of the column sources, φ k u / 2^f
    / W < Q ⇒ at most Q · 2^f pieces.
  All premises run over k < m, t < 2^|cs|, u < 2^|rs| only; each on t alone stands under gT t, each
    on u alone under gU k u.

Notation: `Seg.stack W slot row col` (Cm/SegLayout.lean): a pair of natural numbers, from four
natural numbers, := ((slot + col / W) * hSlot + row, col % W): (row, column) of a matrix that begins
at a slot, in a segment of width W: column c lies in part c / W; `φ`, `i`: natural numbers; in the
head of Cm/TargetReadBitsFld.lean, feature φ, position i; in `Spec.sep_featsAny` φ : ℕ → ℕ → ℕ, and
φ k u stands at the place of φ in `featPl`; `featPl W slot f T φ i` (Cm/TargetReadBitsFld.lean): a
pair of natural numbers, from six natural numbers, := Seg.stack W slot ((φ % 2 ^ f) * T + i) (φ / 2
^ f): the place of (feature, position) in a matrix that begins at a slot, stacked in parts of width
W; `featOf c f jl jh t u` (Cm/TargetReadBitsFld.lean): a natural number, from natural numbers c, f,
t, u and functions jl, jh : ℕ → ℕ, := c + 2 ^ f * jh u + jl t: the feature; in `Spec.sep_feats0` and
`Spec.sep_feats` featOf (c k) f jl (jh k) t u, with c : ℕ → ℕ, jh : ℕ → ℕ → ℕ.

Limits: this file does not say that a model's values have this form: Cm/TargetReadBitsFldFF.lean. It
does not say that so many pieces are needed.

Terms: lean/GLOSSARY.md.
-/
import Cm.TargetReadBitsFldProofs
import Cm.TargetReadBitsBlk

set_option autoImplicit false

namespace Cm.TR

open Cb Blocks Finset

namespace Spec

def sep_feats0 : Prop :=
  ∀ (E : Type) [Field E] (R C : ℕ → ℕ) (v seg m Q : ℕ) (cs rs : List Src) (gT : ℕ → Prop)
      [DecidablePred gT] (gU : ℕ → ℕ → Prop) [∀ k, DecidablePred (gU k)] (cf : ℕ → ℕ → E)
      (jl pos : ℕ → ℕ) (jh : ℕ → ℕ → ℕ) (c : ℕ → ℕ) (f T W slot : ℕ),
    Src.OK (cs ++ rs) v → (∀ k < m, 2 ^ f ∣ c k) → (∀ t < 2 ^ cs.length, gT t → jl t < 2 ^ f) →
    (∀ k < m, ∀ u < 2 ^ rs.length, gU k u → (c k / 2 ^ f + jh k u) / W < Q) →
    (∀ k < m, ∀ t < 2 ^ cs.length, ∀ u < 2 ^ rs.length, gT t → gU k u →
      (featPl W slot f T (featOf (c k) f jl (jh k) t u) (pos t)).1 < R seg ∧
      (featPl W slot f T (featOf (c k) f jl (jh k) t u) (pos t)).2 < C seg) →
    SepV R C v Q fun b A => ∑ k ∈ range m, if gT (Src.num cs v b) ∧ gU k (Src.num rs v b) then
      cf k (Src.num rs v b) *
        A seg (featPl W slot f T (featOf (c k) f jl (jh k) (Src.num cs v b) (Src.num rs v b))
            (pos (Src.num cs v b))).1
          (featPl W slot f T (featOf (c k) f jl (jh k) (Src.num cs v b) (Src.num rs v b))
            (pos (Src.num cs v b))).2
      else 0

def sep_feats : Prop :=
  ∀ (E : Type) [Field E] (R C : ℕ → ℕ) (v seg m Q : ℕ) (cs rs : List Src) (gT : ℕ → Prop)
      [DecidablePred gT] (gU : ℕ → ℕ → Prop) [∀ k, DecidablePred (gU k)] (cf : ℕ → ℕ → E)
      (jl pos : ℕ → ℕ) (jh : ℕ → ℕ → ℕ) (c : ℕ → ℕ) (c₀ f T W slot : ℕ),
    Src.OK (cs ++ rs) v → (∀ k < m, c k % 2 ^ f = c₀) → (∀ t < 2 ^ cs.length, gT t → jl t < 2 ^ f) →
    (∀ k < m, ∀ u < 2 ^ rs.length, gU k u → (c k / 2 ^ f + jh k u + 1) / W < Q) →
    (∀ k < m, ∀ t < 2 ^ cs.length, ∀ u < 2 ^ rs.length, gT t → gU k u →
      (featPl W slot f T (featOf (c k) f jl (jh k) t u) (pos t)).1 < R seg ∧
      (featPl W slot f T (featOf (c k) f jl (jh k) t u) (pos t)).2 < C seg) →
    SepV R C v (2 * Q) fun b A => ∑ k ∈ range m, if gT (Src.num cs v b) ∧ gU k (Src.num rs v b) then
      cf k (Src.num rs v b) *
        A seg (featPl W slot f T (featOf (c k) f jl (jh k) (Src.num cs v b) (Src.num rs v b))
            (pos (Src.num cs v b))).1
          (featPl W slot f T (featOf (c k) f jl (jh k) (Src.num cs v b) (Src.num rs v b))
            (pos (Src.num cs v b))).2
      else 0

def sep_featsAny : Prop :=
  ∀ (E : Type) [Field E] (R C : ℕ → ℕ) (v seg m Q : ℕ) (cs rs : List Src) (gT : ℕ → Prop)
    [DecidablePred gT] (gU : ℕ → ℕ → Prop) [∀ k, DecidablePred (gU k)] (cf : ℕ → ℕ → E)
    (pos : ℕ → ℕ) (φ : ℕ → ℕ → ℕ) (f T W slot : ℕ),
    Src.OK (cs ++ rs) v → (∀ k < m, ∀ u < 2 ^ rs.length, gU k u → φ k u / 2 ^ f / W < Q) →
    (∀ k < m, ∀ t < 2 ^ cs.length, ∀ u < 2 ^ rs.length, gT t → gU k u →
      (featPl W slot f T (φ k u) (pos t)).1 < R seg ∧
      (featPl W slot f T (φ k u) (pos t)).2 < C seg) →
    SepV R C v (Q * 2 ^ f) fun b A => ∑ k ∈ range m, if gT (Src.num cs v b) ∧ gU k (Src.num rs v b) then
      cf k (Src.num rs v b) *
        A seg (featPl W slot f T (φ k (Src.num rs v b)) (pos (Src.num cs v b))).1
          (featPl W slot f T (φ k (Src.num rs v b)) (pos (Src.num cs v b))).2
      else 0

end Spec

/-- The cells under the guard "no carry". -/
theorem sep_featsLo (E : Type) [Field E] (R C : ℕ → ℕ) (v seg m Q : ℕ) (cs rs : List Src)
    (gT : ℕ → Prop) [DecidablePred gT] (gU : ℕ → ℕ → Prop) [∀ k, DecidablePred (gU k)]
    (cf : ℕ → ℕ → E) (jl pos : ℕ → ℕ) (jh : ℕ → ℕ → ℕ) (c : ℕ → ℕ) (c₀ f T W slot : ℕ)
    (hOK : Src.OK (cs ++ rs) v) (hc : ∀ k < m, c k % 2 ^ f = c₀)
    (hQ : ∀ k < m, ∀ u < 2 ^ rs.length, gU k u → (c k / 2 ^ f + jh k u) / W < Q)
    (hS : ∀ k < m, ∀ t < 2 ^ cs.length, ∀ u < 2 ^ rs.length, gT t → gU k u →
      (featPl W slot f T (featOf (c k) f jl (jh k) t u) (pos t)).1 < R seg ∧
      (featPl W slot f T (featOf (c k) f jl (jh k) t u) (pos t)).2 < C seg) :
    SepV R C v Q fun b A => ∑ k ∈ range m, if (gT (Src.num cs v b) ∧ c₀ + jl (Src.num cs v b) < 2 ^ f) ∧ gU k (Src.num rs v b) then
      cf k (Src.num rs v b) *
        A seg (featPl W slot f T (featOf (c k) f jl (jh k) (Src.num cs v b) (Src.num rs v b))
            (pos (Src.num cs v b))).1
          (featPl W slot f T (featOf (c k) f jl (jh k) (Src.num cs v b) (Src.num rs v b))
            (pos (Src.num cs v b))).2
      else 0 := by
  have h0 := sep_blocks E R C v seg m (List.range Q) cs rs (fun t => gT t ∧ c₀ + jl t < 2 ^ f) gU cf
    (fun k u => (c k / 2 ^ f + jh k u) / W)
    (fun t q => (slot + q) * Seg.hSlot + ((c₀ + jl t) * T + pos t))
    (fun k u => (c k / 2 ^ f + jh k u) % W) hOK List.nodup_range
    (fun k hk u hu h => List.mem_range.2 (hQ k hk u hu h)) fun k hk t ht u hu h1 h2 => by
      have h := hS k hk t ht u hu h1.1 h2
      unfold featOf at h
      rw [featPl_lo W slot f T (c k) (jh k u) (jl t) (pos t) (by rw [hc k hk]; exact h1.2),
        hc k hk] at h
      exact h
  rw [List.length_range] at h0
  refine sep_congr E R C v Q _ _ (fun b _ A => Finset.sum_congr rfl fun k hk => ?_) h0
  have hk' := Finset.mem_range.1 hk
  by_cases hg : (gT (Src.num cs v b) ∧ c₀ + jl (Src.num cs v b) < 2 ^ f) ∧ gU k (Src.num rs v b)
  · rw [if_pos hg, if_pos hg]
    unfold featOf
    rw [featPl_lo W slot f T (c k) _ _ _ (by rw [hc k hk']; exact hg.1.2), hc k hk']
  · rw [if_neg hg, if_neg hg]

/-- The cells under the guard "carry". -/
theorem sep_featsHi (E : Type) [Field E] (R C : ℕ → ℕ) (v seg m Q : ℕ) (cs rs : List Src)
    (gT : ℕ → Prop) [DecidablePred gT] (gU : ℕ → ℕ → Prop) [∀ k, DecidablePred (gU k)]
    (cf : ℕ → ℕ → E) (jl pos : ℕ → ℕ) (jh : ℕ → ℕ → ℕ) (c : ℕ → ℕ) (c₀ f T W slot : ℕ)
    (hOK : Src.OK (cs ++ rs) v) (hc : ∀ k < m, c k % 2 ^ f = c₀)
    (hl : ∀ t < 2 ^ cs.length, gT t → jl t < 2 ^ f)
    (hQ : ∀ k < m, ∀ u < 2 ^ rs.length, gU k u → (c k / 2 ^ f + jh k u + 1) / W < Q)
    (hS : ∀ k < m, ∀ t < 2 ^ cs.length, ∀ u < 2 ^ rs.length, gT t → gU k u →
      (featPl W slot f T (featOf (c k) f jl (jh k) t u) (pos t)).1 < R seg ∧
      (featPl W slot f T (featOf (c k) f jl (jh k) t u) (pos t)).2 < C seg) :
    SepV R C v Q fun b A => ∑ k ∈ range m, if (gT (Src.num cs v b) ∧ 2 ^ f ≤ c₀ + jl (Src.num cs v b)) ∧ gU k (Src.num rs v b) then
      cf k (Src.num rs v b) *
        A seg (featPl W slot f T (featOf (c k) f jl (jh k) (Src.num cs v b) (Src.num rs v b))
            (pos (Src.num cs v b))).1
          (featPl W slot f T (featOf (c k) f jl (jh k) (Src.num cs v b) (Src.num rs v b))
            (pos (Src.num cs v b))).2
      else 0 := by
  have h0 := sep_blocks E R C v seg m (List.range Q) cs rs (fun t => gT t ∧ 2 ^ f ≤ c₀ + jl t) gU cf
    (fun k u => (c k / 2 ^ f + jh k u + 1) / W)
    (fun t q => (slot + q) * Seg.hSlot + ((c₀ + jl t - 2 ^ f) * T + pos t))
    (fun k u => (c k / 2 ^ f + jh k u + 1) % W) hOK List.nodup_range
    (fun k hk u hu h => List.mem_range.2 (hQ k hk u hu h)) fun k hk t ht u hu h1 h2 => by
      have h := hS k hk t ht u hu h1.1 h2
      unfold featOf at h
      rw [featPl_hi W slot f T (c k) (jh k u) (jl t) (pos t)
            (hl t ht h1.1) (by rw [hc k hk]; exact h1.2), hc k hk] at h
      exact h
  rw [List.length_range] at h0
  refine sep_congr E R C v Q _ _ (fun b _ A => Finset.sum_congr rfl fun k hk => ?_) h0
  have hk' := Finset.mem_range.1 hk
  by_cases hg : (gT (Src.num cs v b) ∧ 2 ^ f ≤ c₀ + jl (Src.num cs v b)) ∧ gU k (Src.num rs v b)
  · rw [if_pos hg, if_pos hg]
    unfold featOf
    rw [featPl_hi W slot f T (c k) _ _ _ (hl _ (num_lt cs v b) hg.1.1)
          (by rw [hc k hk']; exact hg.1.2), hc k hk']
  · rw [if_neg hg, if_neg hg]

theorem sep_feats0 : Spec.sep_feats0 := by
  intro E _ R C v seg m Q cs rs gT _ gU _ cf jl pos jh c f T W slot hOK hc hl hQ hS
  refine sep_congr E R C v Q _ _ (fun b _ A => Finset.sum_congr rfl fun k _ => ?_)
    (sep_featsLo E R C v seg m Q cs rs gT gU cf jl pos jh c 0 f T W slot hOK
      (fun k hk => Nat.mod_eq_zero_of_dvd (hc k hk)) hQ hS)
  by_cases hg : gT (Src.num cs v b) ∧ gU k (Src.num rs v b)
  · rw [if_pos hg, if_pos ⟨⟨hg.1, by rw [Nat.zero_add]; exact hl _ (num_lt cs v b) hg.1⟩, hg.2⟩]
  · rw [if_neg hg, if_neg fun h => hg ⟨h.1.1, h.2⟩]

theorem sep_feats : Spec.sep_feats := by
  intro E _ R C v seg m Q cs rs gT _ gU _ cf jl pos jh c c₀ f T W slot hOK hc hl hQ hS
  have hQ0 : ∀ k < m, ∀ u < 2 ^ rs.length, gU k u → (c k / 2 ^ f + jh k u) / W < Q :=
    fun k hk u hu h => lt_of_le_of_lt (Nat.div_le_div_right (Nat.le_succ _)) (hQ k hk u hu h)
  rw [two_mul]
  refine sep_congr E R C v (Q + Q) _ _ (fun b _ A => ?_)
    (sep_add E R C v Q Q _ _
      (sep_featsLo E R C v seg m Q cs rs gT gU cf jl pos jh c c₀ f T W slot hOK hc hQ0 hS)
      (sep_featsHi E R C v seg m Q cs rs gT gU cf jl pos jh c c₀ f T W slot hOK hc hl hQ hS))
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hg : gT (Src.num cs v b) ∧ gU k (Src.num rs v b)
  · by_cases hk : c₀ + jl (Src.num cs v b) < 2 ^ f
    · rw [if_pos hg, if_pos ⟨⟨hg.1, hk⟩, hg.2⟩,
        if_neg fun h => absurd hk (not_lt.2 h.1.2), add_zero]
    · rw [if_pos hg, if_neg fun h => hk h.1.2, if_pos ⟨⟨hg.1, not_lt.1 hk⟩, hg.2⟩, zero_add]
  · rw [if_neg hg, if_neg fun h => hg ⟨h.1.1, h.2⟩, if_neg fun h => hg ⟨h.1.1, h.2⟩, add_zero]

theorem sep_featsAny : Spec.sep_featsAny := by
  intro E _ R C v seg m Q cs rs gT _ gU _ cf pos φ f T W slot hOK hQ hS
  have hM : 0 < 2 ^ f := Nat.pos_of_ne_zero (by positivity)
  have hq1 : ∀ x : ℕ, (x / 2 ^ f / W * 2 ^ f + x % 2 ^ f) / 2 ^ f = x / 2 ^ f / W := fun x => by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hM,
      Nat.div_eq_of_lt (Nat.mod_lt _ hM), Nat.zero_add]
  have hq2 : ∀ x : ℕ, (x / 2 ^ f / W * 2 ^ f + x % 2 ^ f) % 2 ^ f = x % 2 ^ f := fun x => by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_mod]
  have hpl : ∀ x i : ℕ, featPl W slot f T x i =
      ((slot + (x / 2 ^ f / W * 2 ^ f + x % 2 ^ f) / 2 ^ f) * Seg.hSlot +
          ((x / 2 ^ f / W * 2 ^ f + x % 2 ^ f) % 2 ^ f * T + i),
        x / 2 ^ f % W) := fun x i => by
    rw [hq1, hq2]
    rfl
  have h0 := sep_blocks E R C v seg m (List.range (Q * 2 ^ f)) cs rs gT gU cf
    (fun k u => φ k u / 2 ^ f / W * 2 ^ f + φ k u % 2 ^ f)
    (fun t q => (slot + q / 2 ^ f) * Seg.hSlot + (q % 2 ^ f * T + pos t))
    (fun k u => φ k u / 2 ^ f % W) hOK
    List.nodup_range
    (fun k hk u hu h => List.mem_range.2 (by
      have h1 := hQ k hk u hu h
      have h2 := Nat.mod_lt (φ k u) hM
      calc
        φ k u / 2 ^ f / W * 2 ^ f + φ k u % 2 ^ f < φ k u / 2 ^ f / W * 2 ^ f + 2 ^ f :=
          Nat.add_lt_add_left h2 _
        _ = (φ k u / 2 ^ f / W + 1) * 2 ^ f := by ring
        _ ≤ Q * 2 ^ f := Nat.mul_le_mul_right _ h1))
    fun k hk t ht u hu h1 h2 => by
      have h := hS k hk t ht u hu h1 h2
      rw [hpl] at h
      exact h
  rw [List.length_range] at h0
  refine sep_congr E R C v (Q * 2 ^ f) _ _ (fun b _ A => Finset.sum_congr rfl fun k _ => ?_) h0
  by_cases hg : gT (Src.num cs v b) ∧ gU k (Src.num rs v b)
  · rw [if_pos hg, if_pos hg, hpl]
  · rw [if_neg hg, if_neg hg]

end Cm.TR
