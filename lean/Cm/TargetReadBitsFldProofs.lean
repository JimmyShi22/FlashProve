-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetReadBitsFldProofs.lean: the proofs of the statements of Cm/TargetReadBitsFld.lean (fields
of a vertex as numbers of sources; the base rule of "separable" for a cell at (feature, position) in
a stacked matrix).

Separable with at most n pieces in the shapes R, C (the numbers of rows and columns of each
segment's matrix), of a function F of a vertex b < 2^v of a cube and of matrices A: at every vertex
b and for all A the value F b A is a constant k b plus at most n pieces, the same at all vertices; a
piece is Σ_{r < R seg, y < C seg} α t r · β u y · A seg r y: one segment, a table on rows times a
table on columns, t and u the numbers that two lists cs, rs of sources of bits form at b, which
together name no variable twice and none outside the cube (`Sep`, `SepV`, `SPiece`,
Cm/TargetReadBits.lean).

Each statement of Cm/TargetReadBitsFld.lean is proved here under the same name; that file has the
definitions. No assumed theorem. From Cm/SegIdxRun.lean (runs of variables),
Cm/SegIdxUnitProofs.lean (`num_append`, `num_lt`), Cm/SegIdxProofs.lean (`vars_append`) and
Cm/TargetReadBitsProofs.lean (`sep_cell`, `sep_add`, `sep_sum`, `sep_congr`).

Main names (statements and hypotheses: Cm/TargetReadBitsFld.lean):
  `fld_num`: the number of fldS v o w at the vertex b.
  `flds_num`: the number of fldsS v l at b: the fields as digits.
  `flds_ok`: the premise `Src.OK` of the base rule for row fields l and column fields l'.
  `flds_two`: two fields as one number, and back.
  `sep_cases`: F from its cases "F where h b = a, else 0".
  `sep_feat0`: the cell at (feature, position), the offset a multiple of 2^f.
  `sep_feat`: the cell at (feature, position): any offset; the carry into the column.
  `sep_featAny`: the fall-back: the feature any function of the column sources.

Notation: `hSlot` (Cm/SegLayout.lean): a natural number: rows of a slot; `Seg.stack W slot row col`
(Cm/SegLayout.lean): a pair of natural numbers, from four natural numbers, := ((slot + col / W) *
hSlot + row, col % W): (row, column) of a matrix that begins at a slot, in a segment of width W:
column c lies in part c / W; `φ`, `i`: natural numbers; in the head of Cm/TargetReadBitsFld.lean,
feature φ, position i; in `Spec.sep_featAny` φ : ℕ → ℕ, and φ u stands at the place of φ in
`featPl`; `featPl W slot f T φ i` (Cm/TargetReadBitsFld.lean): a pair of natural numbers, from six
natural numbers, := Seg.stack W slot ((φ % 2 ^ f) * T + i) (φ / 2 ^ f): the place of (feature,
position) in a matrix that begins at a slot, stacked in parts of width W; `t`, `u`: natural numbers;
in the head of Cm/TargetReadBitsFld.lean, t the number of the row sources cs, u of the column
sources rs; `featOf c f jl jh t u` (Cm/TargetReadBitsFld.lean): a natural number, from natural
numbers c, f, t, u and functions jl, jh : ℕ → ℕ, := c + 2 ^ f * jh u + jl t: the feature; `pos`: a
function ℕ → ℕ; in the head of Cm/TargetReadBitsFld.lean, the position pos t; in the statements pos
t stands at the place of i in `featPl`.

Limits: what the head of Cm/TargetReadBitsFld.lean lists as not said is not said here either. That
is: that a model's atoms have the form that its statements ask; anything on places of the look-up's
bits and of the attention segments; that 2 · Q, or m · n, pieces are needed.

Terms: lean/GLOSSARY.md.
-/
import Cm.TargetReadBitsFld
import Cm.TargetReadBitsProofs

set_option autoImplicit false

namespace Cm.TR

open Cb Blocks Finset

theorem fld_num : Spec.fld_num := fun v o w b h => by
  unfold fldS fld
  rw [num_run (v - o - w) w (by omega) b]
  congr 3
  omega

theorem flds_len (v : ℕ) : ∀ l : List (ℕ × ℕ), (fldsS v l).length = fldsW l
  | [] => rfl
  | p :: l => by
      show (fldS v p.1 p.2 ++ fldsS v l).length = p.2 + fldsW l
      rw [List.length_append, flds_len v l]
      unfold fldS
      rw [run_length]

theorem flds_num : Spec.flds_num := by
  intro v l b
  induction l with
  | nil => intro _; rfl
  | cons p l ih =>
      intro h
      show Src.num (fldS v p.1 p.2 ++ fldsS v l) v b = fld p.1 p.2 b * 2 ^ fldsW l + fldsN l b
      rw [num_append, fld_num v p.1 p.2 b (h p (List.mem_cons_self ..)), flds_len,
        ih fun q hq => h q (List.mem_cons_of_mem _ hq)]

theorem flds_append (v : ℕ) : ∀ l l' : List (ℕ × ℕ), fldsS v (l ++ l') = fldsS v l ++ fldsS v l'
  | [], _ => rfl
  | p :: l, l' => by
      show fldS v p.1 p.2 ++ fldsS v (l ++ l') = (fldS v p.1 p.2 ++ fldsS v l) ++ fldsS v l'
      rw [flds_append v l l', List.append_assoc]

theorem mem_vars_flds (v : ℕ) :
    ∀ (l : List (ℕ × ℕ)) (u : ℕ),
      u ∈ Src.vars (fldsS v l) → ∃ p ∈ l, v - p.1 - p.2 ≤ u ∧ u < v - p.1 - p.2 + p.2
  | [], u, h => absurd h List.not_mem_nil
  | p :: l, u, h => by
      have h' : u ∈ Src.vars (fldS v p.1 p.2 ++ fldsS v l) := h
      rw [vars_append] at h'
      rcases List.mem_append.1 h' with h1 | h1
      · exact ⟨p, List.mem_cons_self .., mem_vars_run.1 h1⟩
      · obtain ⟨q, hq, h2⟩ := mem_vars_flds v l u h1
        exact ⟨q, List.mem_cons_of_mem _ hq, h2⟩

theorem flds_ok1 (v : ℕ) : ∀ l : List (ℕ × ℕ), FldFits v l → FldApart l → Src.OK (fldsS v l) v
  | [], _, _ => ok_nil v
  | p :: l, hf, ha => by
      have hp := hf p (List.mem_cons_self ..)
      obtain ⟨ha1, ha2⟩ := List.pairwise_cons.1 ha
      refine ok_append (ok_run (by omega))
        (flds_ok1 v l (fun q hq => hf q (List.mem_cons_of_mem _ hq)) ha2) fun u hu u' hu' => ?_
      have h1 := mem_vars_run.1 hu
      obtain ⟨q, hq, h2⟩ := mem_vars_flds v l u' hu'
      have h3 := ha1 q hq
      have h4 := hf q (List.mem_cons_of_mem _ hq)
      omega

theorem flds_ok : Spec.flds_ok := fun v l l' hf ha => by
  rw [← flds_append]
  exact flds_ok1 v _ hf ha

theorem flds_two : Spec.flds_two := fun o w o' w' b => by
  have e : fldsN [(o, w), (o', w')] b = fld o w b * 2 ^ w' + fld o' w' b := by
    show fld o w b * 2 ^ (w' + 0) + (fld o' w' b * 2 ^ 0 + 0) = _
    simp
  have hlt : fld o' w' b < 2 ^ w' := Nat.mod_lt _ (Nat.pos_of_ne_zero (by positivity))
  refine ⟨e, ?_, ?_⟩
  · rw [e, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.pos_of_ne_zero (by positivity)),
      Nat.div_eq_of_lt hlt, Nat.zero_add]
  · rw [e, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]

theorem sep_cases : Spec.sep_cases := fun E _ R C v n m h F hh hF => by
  refine sep_congr E R C v (m * n) _ _ (fun b hb A => ?_)
    (sep_sum E R C v n m (fun a b A => if h b = a then F b A else 0) hF)
  rw [Finset.sum_ite_eq]
  rw [if_pos (Finset.mem_range.2 (hh b hb))]

/-- Quotient and remainder of a feature by the number of features in a column. -/
theorem feat_split (M c jh jl : ℕ) (hM : 0 < M) :
    (c + M * jh + jl) % M = (c % M + jl) % M ∧
    (c + M * jh + jl) / M = c / M + jh + (c % M + jl) / M := by
  have e : c + M * jh + jl = (c % M + jl) + M * (c / M + jh) := by
    have := Nat.div_add_mod c M
    rw [Nat.mul_add]
    omega
  rw [e, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ hM]
  exact ⟨rfl, by omega⟩

/-- The place, without a carry. -/
theorem featPl_lo (W slot f T c jh jl i : ℕ) (h : c % 2 ^ f + jl < 2 ^ f) :
    featPl W slot f T (c + 2 ^ f * jh + jl) i =
      ((slot + (c / 2 ^ f + jh) / W) * Seg.hSlot + ((c % 2 ^ f + jl) * T + i),
        (c / 2 ^ f + jh) % W) := by
  obtain ⟨h1, h2⟩ := feat_split (2 ^ f) c jh jl (Nat.pos_of_ne_zero (by positivity))
  unfold featPl Seg.stack
  rw [h1, h2, Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h, Nat.add_zero]

/-- The place, with a carry. -/
theorem featPl_hi (W slot f T c jh jl i : ℕ) (hl : jl < 2 ^ f) (h : 2 ^ f ≤ c % 2 ^ f + jl) :
    featPl W slot f T (c + 2 ^ f * jh + jl) i =
      ((slot + (c / 2 ^ f + jh + 1) / W) * Seg.hSlot + ((c % 2 ^ f + jl - 2 ^ f) * T + i),
        (c / 2 ^ f + jh + 1) % W) := by
  have hM : 0 < 2 ^ f := Nat.pos_of_ne_zero (by positivity)
  obtain ⟨h1, h2⟩ := feat_split (2 ^ f) c jh jl hM
  have hc : c % 2 ^ f < 2 ^ f := Nat.mod_lt _ hM
  have e : c % 2 ^ f + jl = (c % 2 ^ f + jl - 2 ^ f) + 2 ^ f * 1 := by omega
  have hr : c % 2 ^ f + jl - 2 ^ f < 2 ^ f := by omega
  have m1 : (c % 2 ^ f + jl) % 2 ^ f = c % 2 ^ f + jl - 2 ^ f := by
    rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    omega
  have d1 : (c % 2 ^ f + jl) / 2 ^ f = 1 := by
    rw [e, Nat.add_mul_div_left _ _ hM, Nat.div_eq_of_lt (by omega)]
  unfold featPl Seg.stack
  rw [h1, h2, m1, d1]

/-- The cell with a guard on the carry: no carry. -/
theorem sep_featLo (E : Type) [Field E] (R C : ℕ → ℕ) (v seg Q : ℕ) (cs rs : List Src)
    (gT gU : ℕ → Prop) [DecidablePred gT] [DecidablePred gU] (cf : ℕ → E)
    (jl pos jh : ℕ → ℕ) (c f T W slot : ℕ)
    (hOK : Src.OK (cs ++ rs) v) (hQ : ∀ u < 2 ^ rs.length, gU u → (c / 2 ^ f + jh u) / W < Q)
    (hS : ∀ t < 2 ^ cs.length, ∀ u < 2 ^ rs.length, gT t → gU u →
      (featPl W slot f T (featOf c f jl jh t u) (pos t)).1 < R seg ∧
      (featPl W slot f T (featOf c f jl jh t u) (pos t)).2 < C seg) :
    SepV R C v Q fun b A => if (gT (Src.num cs v b) ∧ c % 2 ^ f + jl (Src.num cs v b) < 2 ^ f) ∧ gU (Src.num rs v b) then
      cf (Src.num rs v b) *
        A seg (featPl W slot f T (featOf c f jl jh (Src.num cs v b) (Src.num rs v b))
            (pos (Src.num cs v b))).1
          (featPl W slot f T (featOf c f jl jh (Src.num cs v b) (Src.num rs v b))
            (pos (Src.num cs v b))).2
      else 0 := by
  refine sep_congr E R C v Q _ _ (fun b _ A => ?_)
    (sep_cell E R C v seg Q cs rs (fun t => gT t ∧ c % 2 ^ f + jl t < 2 ^ f) gU cf
      (fun u => (c / 2 ^ f + jh u) / W)
      (fun t q => (slot + q) * Seg.hSlot + ((c % 2 ^ f + jl t) * T + pos t))
      (fun u => (c / 2 ^ f + jh u) % W) hOK hQ
      fun t ht u hu h1 h2 => by
        have h := hS t ht u hu h1.1 h2
        unfold featOf at h
        rw [featPl_lo W slot f T c (jh u) (jl t) (pos t) h1.2] at h
        exact h)
  by_cases hg : (gT (Src.num cs v b) ∧ c % 2 ^ f + jl (Src.num cs v b) < 2 ^ f) ∧
    gU (Src.num rs v b)
  · rw [if_pos hg, if_pos hg]
    unfold featOf
    rw [featPl_lo W slot f T c _ _ _ hg.1.2]
  · rw [if_neg hg, if_neg hg]

/-- The cell with a guard on the carry: a carry. -/
theorem sep_featHi (E : Type) [Field E] (R C : ℕ → ℕ) (v seg Q : ℕ) (cs rs : List Src)
    (gT gU : ℕ → Prop) [DecidablePred gT] [DecidablePred gU] (cf : ℕ → E)
    (jl pos jh : ℕ → ℕ) (c f T W slot : ℕ)
    (hOK : Src.OK (cs ++ rs) v) (hl : ∀ t < 2 ^ cs.length, gT t → jl t < 2 ^ f)
    (hQ : ∀ u < 2 ^ rs.length, gU u → (c / 2 ^ f + jh u + 1) / W < Q)
    (hS : ∀ t < 2 ^ cs.length, ∀ u < 2 ^ rs.length, gT t → gU u →
      (featPl W slot f T (featOf c f jl jh t u) (pos t)).1 < R seg ∧
      (featPl W slot f T (featOf c f jl jh t u) (pos t)).2 < C seg) :
    SepV R C v Q fun b A => if (gT (Src.num cs v b) ∧ 2 ^ f ≤ c % 2 ^ f + jl (Src.num cs v b)) ∧ gU (Src.num rs v b) then
      cf (Src.num rs v b) *
        A seg (featPl W slot f T (featOf c f jl jh (Src.num cs v b) (Src.num rs v b))
            (pos (Src.num cs v b))).1
          (featPl W slot f T (featOf c f jl jh (Src.num cs v b) (Src.num rs v b))
            (pos (Src.num cs v b))).2
      else 0 := by
  refine sep_congr E R C v Q _ _ (fun b _ A => ?_)
    (sep_cell E R C v seg Q cs rs (fun t => gT t ∧ 2 ^ f ≤ c % 2 ^ f + jl t) gU cf
      (fun u => (c / 2 ^ f + jh u + 1) / W)
      (fun t q => (slot + q) * Seg.hSlot + ((c % 2 ^ f + jl t - 2 ^ f) * T + pos t))
      (fun u => (c / 2 ^ f + jh u + 1) % W) hOK hQ
      fun t ht u hu h1 h2 => by
        have h := hS t ht u hu h1.1 h2
        unfold featOf at h
        rw [featPl_hi W slot f T c (jh u) (jl t) (pos t) (hl t ht h1.1) h1.2] at h
        exact h)
  by_cases hg : (gT (Src.num cs v b) ∧ 2 ^ f ≤ c % 2 ^ f + jl (Src.num cs v b)) ∧
    gU (Src.num rs v b)
  · rw [if_pos hg, if_pos hg]
    unfold featOf
    rw [featPl_hi W slot f T c _ _ _ (hl _ (num_lt cs v b) hg.1.1) hg.1.2]
  · rw [if_neg hg, if_neg hg]

theorem sep_feat0 : Spec.sep_feat0 := by
  intro E _ R C v seg Q cs rs gT gU _ _ cf jl pos jh c f T W slot hOK hc hl hQ hS
  have hc0 : c % 2 ^ f = 0 := Nat.mod_eq_zero_of_dvd hc
  refine sep_congr E R C v Q _ _ (fun b _ A => ?_)
    (sep_featLo E R C v seg Q cs rs gT gU cf jl pos jh c f T W slot hOK hQ hS)
  by_cases hg : gT (Src.num cs v b) ∧ gU (Src.num rs v b)
  · rw [if_pos hg,
      if_pos ⟨⟨hg.1, by rw [hc0, Nat.zero_add]; exact hl _ (num_lt cs v b) hg.1⟩, hg.2⟩]
  · rw [if_neg hg, if_neg fun h => hg ⟨h.1.1, h.2⟩]

theorem sep_feat : Spec.sep_feat := by
  intro E _ R C v seg Q cs rs gT gU _ _ cf jl pos jh c f T W slot hOK hl hQ hS
  have hQ0 : ∀ u < 2 ^ rs.length, gU u → (c / 2 ^ f + jh u) / W < Q := fun u hu h =>
    lt_of_le_of_lt (Nat.div_le_div_right (Nat.le_succ _)) (hQ u hu h)
  rw [two_mul]
  refine sep_congr E R C v (Q + Q) _ _ (fun b _ A => ?_)
    (sep_add E R C v Q Q _ _
      (sep_featLo E R C v seg Q cs rs gT gU cf jl pos jh c f T W slot hOK hQ0 hS)
      (sep_featHi E R C v seg Q cs rs gT gU cf jl pos jh c f T W slot hOK hl hQ hS))
  by_cases hg : gT (Src.num cs v b) ∧ gU (Src.num rs v b)
  · by_cases hk : c % 2 ^ f + jl (Src.num cs v b) < 2 ^ f
    · rw [if_pos hg, if_pos ⟨⟨hg.1, hk⟩, hg.2⟩,
        if_neg fun h => absurd hk (not_lt.2 h.1.2), add_zero]
    · rw [if_pos hg, if_neg fun h => hk h.1.2, if_pos ⟨⟨hg.1, not_lt.1 hk⟩, hg.2⟩, zero_add]
  · rw [if_neg hg, if_neg fun h => hg ⟨h.1.1, h.2⟩, if_neg fun h => hg ⟨h.1.1, h.2⟩, add_zero]

theorem sep_featAny : Spec.sep_featAny := by
  intro E _ R C v seg Q cs rs gT gU _ _ cf pos φ f T W slot hOK hQ hS
  have hM : 0 < 2 ^ f := Nat.pos_of_ne_zero (by positivity)
  have hq1 : ∀ u, (φ u / 2 ^ f / W * 2 ^ f + φ u % 2 ^ f) / 2 ^ f = φ u / 2 ^ f / W := fun u => by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hM,
      Nat.div_eq_of_lt (Nat.mod_lt _ hM), Nat.zero_add]
  have hq2 : ∀ u, (φ u / 2 ^ f / W * 2 ^ f + φ u % 2 ^ f) % 2 ^ f = φ u % 2 ^ f := fun u => by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_mod]
  have hpl : ∀ t u, featPl W slot f T (φ u) (pos t) =
      ((slot + (φ u / 2 ^ f / W * 2 ^ f + φ u % 2 ^ f) / 2 ^ f) * Seg.hSlot +
          ((φ u / 2 ^ f / W * 2 ^ f + φ u % 2 ^ f) % 2 ^ f * T + pos t),
        φ u / 2 ^ f % W) := fun t u => by
    rw [hq1, hq2]
    rfl
  refine sep_congr E R C v (Q * 2 ^ f) _ _ (fun b _ A => ?_)
    (sep_cell E R C v seg (Q * 2 ^ f) cs rs gT gU cf
      (fun u => φ u / 2 ^ f / W * 2 ^ f + φ u % 2 ^ f)
      (fun t q => (slot + q / 2 ^ f) * Seg.hSlot + (q % 2 ^ f * T + pos t))
      (fun u => φ u / 2 ^ f % W) hOK
      (fun u hu h => by
        have h1 := hQ u hu h
        have h2 := Nat.mod_lt (φ u) hM
        calc
          φ u / 2 ^ f / W * 2 ^ f + φ u % 2 ^ f < φ u / 2 ^ f / W * 2 ^ f + 2 ^ f :=
            Nat.add_lt_add_left h2 _
          _ = (φ u / 2 ^ f / W + 1) * 2 ^ f := by ring
          _ ≤ Q * 2 ^ f := Nat.mul_le_mul_right _ h1)
      fun t ht u hu h1 h2 => by
        have h := hS t ht u hu h1 h2
        rw [hpl] at h
        exact h)
  by_cases hg : gT (Src.num cs v b) ∧ gU (Src.num rs v b)
  · rw [if_pos hg, if_pos hg, hpl]
  · rw [if_neg hg, if_neg hg]

end Cm.TR
