-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Ends/AlgCongr.lean: which weights and which rotary entries the library's key of a
feed-forward segment reads.
States: (key_congr_w) THE LIBRARY's KEY OF A FEED-FORWARD SEGMENT READS THE WEIGHTS INSIDE THEIR
MATRICES' RANGES ALONE: if two families of weights w, w' agree there (AgreeW), the keys on them are
one, at every layer of the segment on which the family is present and every entry x below the
family's length. (key_congr_tb) THE SAME OF THE TABLES: a key reads the rotary tables alone, at the
segment's layers, its positions and the pairs of channels of a head (AgreeT).
Why: the library's layerR is 0 outside a matrix's rows and columns; weights that are read from cells
by another rule need not be. A tie between the two can hold on the ranges alone.
Under: a layer with experts has f = 2 fe hidden units; the width of a head is even, and for
key_congr_tb not 0; key_congr_tb speaks of the positions i below D.T.
-/
import Inst.Model.FF.Trace

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Alg

open Finset
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Arr Fam LW key len present val hh Ag Au Av Ad AY Aq Ak Y' isExpL
  routed isExp)

variable {K : Type} [CommRing K]

/-- Two families of weights agree inside the ranges that the keys of a segment read. -/
structure AgreeW (D : Dim) (w w' : ℕ → LW K) : Prop where
  /-- the queries' matrix -/
  Wq : ∀ l < D.nl, ∀ j < D.d, ∀ x < D.dq, (w l).Wq j x = (w' l).Wq j x
  /-- the keys' -/
  Wk : ∀ l < D.nl, ∀ j < D.d, ∀ x < D.dkv, (w l).Wk j x = (w' l).Wk j x
  /-- the values' -/
  Wv : ∀ l < D.nl, ∀ j < D.d, ∀ x < D.dkv, (w l).Wv j x = (w' l).Wv j x
  /-- the attention output's -/
  Wo : ∀ l < D.nl, ∀ j < D.dq, ∀ x < D.d, (w l).Wo j x = (w' l).Wo j x
  /-- the gate's: dense, or the shared expert's -/
  Wg : ∀ l < D.nl, ∀ j < D.d, ∀ x < (if isExpL l then D.fe else D.f),
    (w l).Wg j x = (w' l).Wg j x
  /-- the up product's -/
  Wu : ∀ l < D.nl, ∀ j < D.d, ∀ x < (if isExpL l then D.fe else D.f),
    (w l).Wu j x = (w' l).Wu j x
  /-- the down product's -/
  Wd : ∀ l < D.nl, ∀ j < (if isExpL l then D.fe else D.f), ∀ x < D.d,
    (w l).Wd j x = (w' l).Wd j x
  /-- the router's, on a layer with experts -/
  Wr : ∀ l < D.nl, isExpL l = true → ∀ j < D.d, ∀ x < D.nx, (w l).Wr j x = (w' l).Wr j x
  /-- the routed experts' gates -/
  Eg : ∀ l < D.nl, isExpL l = true → ∀ e < D.nx, ∀ j < D.d, ∀ x < D.fe,
    (w l).Eg e j x = (w' l).Eg e j x
  /-- their up products -/
  Eu : ∀ l < D.nl, isExpL l = true → ∀ e < D.nx, ∀ j < D.d, ∀ x < D.fe,
    (w l).Eu e j x = (w' l).Eu e j x
  /-- their down products -/
  Ed : ∀ l < D.nl, isExpL l = true → ∀ e < D.nx, ∀ j < D.fe, ∀ x < D.d,
    (w l).Ed e j x = (w' l).Ed e j x

variable {D : Dim} {w w' : ℕ → LW K} (t : Cell → K)

/-- What «routed» says. -/
theorem routed_iff (l x : ℕ) : routed D l x = true ↔ isExpL l = true ∧ D.fe ≤ x := by
  unfold routed
  simp

/-- The gate's accumulator. -/
theorem Ag_congr (A : AgreeW D w w') (hffe : D.f = D.fe + D.fe) {l x : ℕ} (hl : l < D.nl)
    (hx : x < D.f) (i : ℕ) : Ag D t w l x i = Ag D t w' l x i := by
  unfold Ag
  by_cases hr : routed D l x = true
  · obtain ⟨he, hfe⟩ := (routed_iff l x).mp hr
    rw [if_pos hr, if_pos hr]
    refine sum_congr rfl fun e hE => ?_
    congr 1
    refine sum_congr rfl fun j hj => ?_
    rw [A.Eg l hl he e (mem_range.mp hE) j (mem_range.mp hj) (x - D.fe) (by omega)]
  · rw [if_neg hr, if_neg hr]
    refine sum_congr rfl fun j hj => ?_
    have hx' : x < (if isExpL l then D.fe else D.f) := by
      by_cases he : isExpL l = true
      · rw [if_pos he]
        by_contra hc
        exact hr ((routed_iff l x).mpr ⟨he, by omega⟩)
      · rw [if_neg he]
        exact hx
    rw [A.Wg l hl j (mem_range.mp hj) x hx']

/-- The up product's accumulator. -/
theorem Au_congr (A : AgreeW D w w') (hffe : D.f = D.fe + D.fe) {l x : ℕ} (hl : l < D.nl)
    (hx : x < D.f) (i : ℕ) : Au D t w l x i = Au D t w' l x i := by
  unfold Au
  by_cases hr : routed D l x = true
  · obtain ⟨he, hfe⟩ := (routed_iff l x).mp hr
    rw [if_pos hr, if_pos hr]
    refine sum_congr rfl fun e hE => ?_
    congr 1
    refine sum_congr rfl fun j hj => ?_
    rw [A.Eu l hl he e (mem_range.mp hE) j (mem_range.mp hj) (x - D.fe) (by omega)]
  · rw [if_neg hr, if_neg hr]
    refine sum_congr rfl fun j hj => ?_
    have hx' : x < (if isExpL l then D.fe else D.f) := by
      by_cases he : isExpL l = true
      · rw [if_pos he]
        by_contra hc
        exact hr ((routed_iff l x).mpr ⟨he, by omega⟩)
      · rw [if_neg he]
        exact hx
    rw [A.Wu l hl j (mem_range.mp hj) x hx']

/-- The down product's accumulator. -/
theorem Ad_congr (A : AgreeW D w w') {l x : ℕ} (hl : l < D.nl) (hx : x < D.d) (i : ℕ) :
    Ad D t w l x i = Ad D t w' l x i := by
  unfold Ad
  by_cases he : isExpL l = true
  · rw [if_pos he, if_pos he]
    congr 1
    · refine sum_congr rfl fun j hj => ?_
      rw [A.Wd l hl j (by rw [if_pos he]; exact mem_range.mp hj) x hx]
    · refine sum_congr rfl fun e hE => ?_
      congr 1
      refine sum_congr rfl fun j hj => ?_
      rw [A.Ed l hl he e (mem_range.mp hE) j (mem_range.mp hj) x hx]
  · rw [if_neg he, if_neg he]
    refine sum_congr rfl fun j hj => ?_
    rw [A.Wd l hl j (by rw [if_neg he]; exact mem_range.mp hj) x hx]

/-- Queries and keys before the rotation. -/
theorem AY_congr (A : AgreeW D w w') {l x : ℕ} (hl : l < D.nl) (hx : x < D.dqk) (i : ℕ) :
    AY D t w l x i = AY D t w' l x i := by
  unfold AY Aq Ak
  by_cases hq : x < D.dq
  · rw [if_pos hq, if_pos hq]
    refine sum_congr rfl fun j hj => ?_
    rw [A.Wq l hl j (mem_range.mp hj) x hq]
  · rw [if_neg hq, if_neg hq]
    refine sum_congr rfl fun j hj => ?_
    have hx' : x - D.dq < D.dkv := by
      unfold Dim.dqk at hx
      omega
    rw [A.Wk l hl j (mem_range.mp hj) (x - D.dq) hx']

/-- The coordinate behind an even coordinate of a head lies below the width of all heads. -/
theorem succ_lt_heads {c n x : ℕ} (hc : c % 2 = 0) (hx : x < n * c) (he : x % c % 2 = 0) :
    x + 1 < n * c := by
  rcases Nat.eq_zero_or_pos c with h0 | hpos
  · subst h0
    simp at hx
  · have h1 : x % c < c := Nat.mod_lt x hpos
    have h2 : x / c < n := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hx)
    have h3 : (x / c + 1) * c ≤ n * c := Nat.mul_le_mul_right c h2
    have h4 := Nat.div_add_mod x c
    have h5 : (x / c + 1) * c = c * (x / c) + c := by ring
    omega

/-- Queries and keys after the rotation. -/
theorem Y_congr (A : AgreeW D w w') (hev : D.P.ch % 2 = 0) (tb : Tables) (L0 : ℕ) {l x : ℕ}
    (hl : l < D.nl) (hx : x < D.dqk) (i : ℕ) : Y' D t tb L0 w l x i = Y' D t tb L0 w' l x i := by
  have hx0 : x < (D.P.nq + D.P.nkv) * D.P.ch := by
    have e : D.dqk = (D.P.nq + D.P.nkv) * D.P.ch := by
      unfold Dim.dqk Dim.dq Dim.dkv
      ring
    rw [← e]
    exact hx
  have back : ∀ y, y < (D.P.nq + D.P.nkv) * D.P.ch → y < D.dqk := fun y hy => by
    have e : D.dqk = (D.P.nq + D.P.nkv) * D.P.ch := by
      unfold Dim.dqk Dim.dq Dim.dkv
      ring
    rw [e]
    exact hy
  unfold Y'
  by_cases he : x % D.P.ch % 2 = 0
  · simp only [if_pos he]
    rw [AY_congr t A hl hx, AY_congr t A hl (back _ (succ_lt_heads hev hx0 he))]
  · simp only [if_neg he]
    rw [AY_congr t A hl hx, AY_congr t A hl (show x - 1 < D.dqk by omega)]

variable [scl : Scl]

/-- **The library's key reads the weights inside their ranges alone.** -/
theorem key_congr_w (A : AgreeW D w w') (hffe : D.f = D.fe + D.fe) (hev : D.P.ch % 2 = 0)
    (tb : Tables) (L0 : ℕ) (s : Fam) {l x : ℕ} (hl : l < D.nl) (hp : present s l = true)
    (hx : x < len D s) (i : ℕ) : key D t tb L0 w s l x i = key D t tb L0 w' s l x i := by
  cases s
  case G =>
    simp only [key]
    rw [Ag_congr t A hffe hl hx]
  case U =>
    simp only [key]
    rw [Au_congr t A hffe hl hx]
  case QK =>
    simp only [key]
    rw [Y_congr t A hev tb L0 hl hx]
  case O =>
    simp only [key]
    rw [sum_congr rfl fun j hj => by rw [A.Wo l hl j (mem_range.mp hj) x hx]]
  case D =>
    simp only [key]
    rw [Ad_congr t A hl hx]
  case V =>
    simp only [key, Av]
    rw [sum_congr rfl fun j hj => by rw [A.Wv l hl j (mem_range.mp hj) x hx]]
  case LR =>
    have he : isExpL l = true := by
      unfold present at hp
      simpa [isExp] using hp
    simp only [key]
    rw [sum_congr rfl fun j hj => by rw [A.Wr l hl he j (mem_range.mp hj) x hx]]
  all_goals rfl

/-- Two tables agree in the rotary entries that the keys of a segment read: the segment's layers,
its positions, the pairs of channels of a head. -/
structure AgreeT (D : Dim) (tb tb' : Tables) (L0 : ℕ) : Prop where
  /-- the cosines -/
  C : ∀ l < D.nl, ∀ i < D.T, ∀ jj < D.P.ch / 2, tb.C (L0 + l) i jj = tb'.C (L0 + l) i jj
  /-- the sines -/
  S : ∀ l < D.nl, ∀ i < D.T, ∀ jj < D.P.ch / 2, tb.S (L0 + l) i jj = tb'.S (L0 + l) i jj

omit scl in
/-- Queries and keys after the rotation read the rotary tables inside these ranges alone. -/
theorem Y_congr_tb {tb tb' : Tables} {L0 : ℕ} (A : AgreeT D tb tb' L0) (hev : D.P.ch % 2 = 0)
    (hch : 0 < D.P.ch) (w : ℕ → LW K) {l i : ℕ} (hl : l < D.nl) (hi : i < D.T) (x : ℕ) :
    Y' D t tb L0 w l x i = Y' D t tb' L0 w l x i := by
  have h1 : x % D.P.ch < D.P.ch := Nat.mod_lt x hch
  have hj : x % D.P.ch / 2 < D.P.ch / 2 := by omega
  unfold Y'
  simp only [A.C l hl i hi _ hj, A.S l hl i hi _ hj]

/-- **The library's key reads the rotary tables inside their ranges alone**, and no other table. -/
theorem key_congr_tb {tb tb' : Tables} {L0 : ℕ} (A : AgreeT D tb tb' L0) (hev : D.P.ch % 2 = 0)
    (hch : 0 < D.P.ch) (w : ℕ → LW K) (s : Fam) {l i : ℕ} (hl : l < D.nl) (hi : i < D.T) (x : ℕ) :
    key D t tb L0 w s l x i = key D t tb' L0 w s l x i := by
  cases s
  case QK =>
    simp only [key]
    rw [Y_congr_tb t A hev hch w hl hi]
  all_goals rfl

#print axioms key_congr_w
#print axioms key_congr_tb

end OnBytes.Road.Alg
