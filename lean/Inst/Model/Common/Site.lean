-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/Common/Site.lean: how two lookups express a rounding q = rhu(A, k), what they imply, the
honest prover's digits, and the two looked-up values as functions of affine forms (the first without
its accumulator).

`rhu` (Inst/Model/Program.lean) divides by 2^k, rounding half up; a key is a looked-up value. A
rounding q = rhu(A, k) with k ≥ 16 is expressed by two keys. The high digit r1 = rh of the remainder
A + 2^(k−1) − 2^k q = r0 + 2^16 r1 is held in cells (the small integers in a segment's matrices).
The low key A + 2^(k−1) − 2^k q − 2^16 rh must be an entry of `R16`, and the high key 2^(top−k) rh
an entry of `R8` (top = 24, a digit of one cell) or of `R16` (top = 32, a digit of two cells); these
are the range tables of Inst/Model/Tables.lean. Everything here is about numbers at one position:
integers A, q, rh, with bounds as hypotheses (the keys are defined over any commutative ring, the
forms over a field); no cells, no layout. The modulus p and all bounds are parameters. Each row
holds under the hypotheses of its statement.
  `site A q rh k`, `high rh k top`   the two keys, over any commutative ring
  `range_of_key`       a key that is small and congruent to an entry of {0, .., N − 1} is such an
                       entry
  `high_sound`         Step L1 for a high digit: 0 ≤ rh < 2^(k−16) (FL7)
  `site_sound`         the low key, with 0 ≤ rh < 2^(k−16), gives q = rhu A k
  `site_high`          the two together; `site_low`: k = 16, no high digit (the family XR of keys:
                       `Fam`, Inst/Model/FF/Index.lean)
  `rem A k`, `hd A k`    the honest remainder and its high digit; `site_hon`, `high_hon`: both keys
                         are entries of their tables
  `hd_unique`          the relation determines the high digit: rh = hd A k
  `SITE w Q k RH`, `HIGH RH k top`   the low key without its accumulator (at the weight w = 1:
                       `val_SITE_one`), and the high key, as functions of affine forms (`Form`,
                       Blocks/Form.lean), with `val_SITE`, `val_HIGH`

Every shift (Sections 5 to 9). The implementation admits shifts from 1 up (protocol document, 8.G.2,
8.G.5, 8.G.8, 8.G.14). Put dn(k) = max(0, 16 − k) and up(k) = max(k, 16). The scaled remainder
2^dn(k) (A + 2^(k−1) − 2^k q) = lo + 2^16 rh is split in the same two digits. The low key 2^dn(k) (A
+ 2^(k−1) − 2^k q) − 2^16 rh must be an entry of `R16`; the high key 2^(top−up(k)) rh must be an
entry of `R8` or `R16`. No cell, table or count depends on k: below 16 the high digit is still
there, and its key forces it to be 0. The protocol document: an earlier one, not in this repository.
`scl`, `ssite`, `shigh` (as forms `SSITE`, `SHIGH`: `val_SSITE_one`, `val_SHIGH`) are the public
weight 2^dn(k) and the two keys for every k. Each is defined by a branch on the public number k:
from 16 on it is x, `site`, `high` themselves, so at a fixed shift such as 17 the term unfolds to
the one of Section 1 (the examples of Section 9 check this); 2^0 · x = x holds by the laws of a ring
and not by unfolding, so the product alone would not unfold. `scl_eq`, `ssite_eq`, `shigh_eq`,
`SSITE_eq`, `SHIGH_eq` give the implementation's formulas, for every k.
  `ssite_eq_site`, `rhu_scale`   for 1 ≤ k a rounding by k is the rounding by up(k) of the
                       accumulator 2^dn(k) A
  `shigh_sound`, `ssite_sound`, `ssite_high`   the counterparts of `high_sound`, `site_sound`,
                       `site_high`: under the hypotheses of their statements, q = rhu A k and
                       0 ≤ rh < 2^(up(k)−16), so rh = 0 for k ≤ 16 (`high_zero`)
The honest high digit is the same term hd A k for every k (it is 0 for k ≤ 16).

Notation: `N`: a finite type; `E`: a field; `Form N E`: "an affine function of the entries, given by
its constant term (at none) and its coefficients" (Blocks/Form.lean); `Q`, `RH`: forms; `w` (of
`SITE`, `SSITE`): an element of E; `y`: a map N → E; `Form.val y`: "the value of a form"
(Blocks/Form.lean); digit form 0, 1, 2: top = 16, 24, 32 (`Scales.top`,
Inst/Model/FF/ScalesDef.lean).

Limits: Sections 5 to 9 do not say which shifts a model may have (the ranges 1 ≤ k ≤ 24 or 32 and
the no-wrap conditions are hypotheses here and belong to the files that use these definitions), and
they have the digit forms 1 and 2 only: the implementation's form 0 (no high digit at all, k ≤ 16)
is not rendered. None of the soundness statements needs 1 ≤ k: at k = 0 they are about Lean's rhu A
0 = A + 1, which no valid settings (`Lawful`, Inst/Model/Scales.lean) reach. Sections 5 to 8 follow
the implementation. Labels such as (FL7) and "Step L1" link one docstring to another.
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Inst.Model.Common.LedgerSound
import Blocks.Form

set_option autoImplicit false

namespace Inst.Model.Site

open Finset
open Inst.Model.Ledger (lift_eq lift_zero)

/-! ## 1. The two keys -/

section Keys
variable {R : Type} [CommRing R]

/-- The low key of a rounding q = rhu(A, k) with the high digit rh. -/
def site (A q rh : R) (k : ℕ) : R := A + 2 ^ (k - 1) - 2 ^ k * q - 2 ^ 16 * rh

/-- The high key: the high digit times its public multiplier. -/
def high (rh : R) (k top : ℕ) : R := 2 ^ (top - k) * rh

theorem map_site {R' : Type} [CommRing R'] (f : R →+* R') (A q rh : R) (k : ℕ) :
    f (site A q rh k) = site (f A) (f q) (f rh) k := by
  simp [site, map_ofNat]

theorem map_high {R' : Type} [CommRing R'] (f : R →+* R') (rh : R) (k top : ℕ) :
    f (high rh k top) = high (f rh) k top := by
  simp [high, map_ofNat]

end Keys

/-! ## 2. What the keys imply -/

/-- A key in a range table: a key of absolute value at most B that is congruent modulo p to an entry
of {0, .., N − 1}, with B + N ≤ p, is such an entry. -/
theorem range_of_key {p key B N : ℤ} (hB : |key| ≤ B) (hp : B + N ≤ p)
    (h : ∃ t : ℤ, 0 ≤ t ∧ t < N ∧ key ≡ t [ZMOD p]) : 0 ≤ key ∧ key < N := by
  obtain ⟨t, h0, h1, ht⟩ := h
  have hk := abs_le.mp hB
  have e : key = t := lift_eq ht (by rw [abs_lt]; constructor <;> linarith)
  omega

/-- The range of a high digit from its key over the integers, for 16 ≤ k ≤ top = 16 + w. (not all
hypotheses are named here: see the statement below) -/
theorem high_range {k top w : ℕ} (htop : top = 16 + w) (hk16 : 16 ≤ k) (hk : k ≤ top) {rh : ℤ}
    (h0 : 0 ≤ high rh k top) (h1 : high rh k top < 2 ^ w) : 0 ≤ rh ∧ rh < 2 ^ (k - 16) := by
  unfold high at h0 h1
  have hpos : (0 : ℤ) < 2 ^ (top - k) := by positivity
  have e : (2 : ℤ) ^ w = 2 ^ (top - k) * 2 ^ (k - 16) := by
    rw [← pow_add]
    congr 1
    omega
  constructor
  · exact nonneg_of_mul_nonneg_right h0 hpos
  · rw [e] at h1
    exact lt_of_mul_lt_mul_left h1 hpos.le

/-- Step L1 for a high digit, fact (FL7): under the hypotheses below (among them 16 ≤ k ≤ top =
16 + w, where the table has 2^w rows), 0 ≤ rh < 2^(k−16). -/
theorem high_sound {p : ℤ} {k top w : ℕ} (htop : top = 16 + w) (hk16 : 16 ≤ k) (hk : k ≤ top)
    {rh Rb : ℤ} (hR : |rh| ≤ Rb) (hp : 2 ^ (top - k) * Rb + 2 ^ w ≤ p)
    (h : ∃ t : ℤ, 0 ≤ t ∧ t < 2 ^ w ∧ high rh k top ≡ t [ZMOD p]) : 0 ≤ rh ∧ rh < 2 ^ (k - 16) := by
  have hB : |high rh k top| ≤ 2 ^ (top - k) * Rb := by
    unfold high
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 2 ^ (top - k))]
    exact mul_le_mul_of_nonneg_left hR (by positivity)
  obtain ⟨h0, h1⟩ := range_of_key hB hp h
  exact high_range htop hk16 hk h0 h1

/-- A bound on the low key from bounds on its parts. -/
theorem abs_site_le {k : ℕ} {A q rh Ab Qb Rb : ℤ} (hA : |A| ≤ Ab) (hQ : |q| ≤ Qb) (hR : |rh| ≤ Rb) :
    |site A q rh k| ≤ Ab + 2 ^ (k - 1) + 2 ^ k * Qb + 2 ^ 16 * Rb := by
  have hA' := abs_le.mp hA
  have hQ' := abs_le.mp hQ
  have hR' := abs_le.mp hR
  have hk : (0 : ℤ) < 2 ^ k := by positivity
  have hk1 : (0 : ℤ) < 2 ^ (k - 1) := by positivity
  have h1 : 2 ^ k * q ≤ 2 ^ k * Qb := mul_le_mul_of_nonneg_left hQ'.2 hk.le
  have h2 : 2 ^ k * (-Qb) ≤ 2 ^ k * q := mul_le_mul_of_nonneg_left hQ'.1 hk.le
  unfold site
  rw [abs_le]
  constructor <;> linarith

/-- Over the integers, for k ≥ 16: if the low key is an entry of R16 and 0 ≤ rh < 2^(k−16), then q =
rhu(A, k). -/
theorem rhu_of_site {k : ℕ} (hk16 : 16 ≤ k) {A q rh : ℤ} (hrh0 : 0 ≤ rh) (hrh1 : rh < 2 ^ (k - 16))
    (h0 : 0 ≤ site A q rh k) (h1 : site A q rh k < 2 ^ 16) : q = rhu A k := by
  unfold site at h0 h1
  have e : (2 : ℤ) ^ k = 2 ^ 16 * 2 ^ (k - 16) := by
    rw [← pow_add]
    congr 1
    omega
  have hpos : (0 : ℤ) < 2 ^ k := by positivity
  have hr0 : 0 ≤ A + 2 ^ (k - 1) - 2 ^ k * q := by nlinarith
  have hr1 : A + 2 ^ (k - 1) - 2 ^ k * q < 2 ^ k := by
    rw [e] at h0 h1 ⊢
    nlinarith
  have := (Int.ediv_emod_unique hpos).mpr
    ⟨(by ring : (A + 2 ^ (k - 1) - 2 ^ k * q) + 2 ^ k * q = A + 2 ^ (k - 1)), hr0, hr1⟩
  exact this.1.symm

/-- The low key of a rounding, for k ≥ 16: with bounds on A, q, rh and no wrap-around (`hp`), with 0
≤ rh < 2^(k−16), and with the key congruent to an entry of R16: q = rhu(A, k), and the key is an
entry over the integers. -/
theorem site_sound {p : ℤ} {k : ℕ} (hk16 : 16 ≤ k) {A q rh Ab Qb Rb : ℤ} (hA : |A| ≤ Ab)
    (hQ : |q| ≤ Qb) (hR : |rh| ≤ Rb) (hrh0 : 0 ≤ rh) (hrh1 : rh < 2 ^ (k - 16))
    (hp : Ab + 2 ^ (k - 1) + 2 ^ k * Qb + 2 ^ 16 * Rb + 2 ^ 16 ≤ p)
    (h : ∃ t : ℤ, 0 ≤ t ∧ t < 2 ^ 16 ∧ site A q rh k ≡ t [ZMOD p]) :
    q = rhu A k ∧ 0 ≤ site A q rh k ∧ site A q rh k < 2 ^ 16 := by
  obtain ⟨h0, h1⟩ := range_of_key (abs_site_le hA hQ hR) hp h
  exact ⟨rhu_of_site hk16 hrh0 hrh1 h0 h1, h0, h1⟩

/-- A rounding with a high digit: both keys, with bounds on A, q, rh and no wrap-around, for 16 ≤ k
≤ top = 16 + w. top = 24 and w = 8 for a digit of one cell, top = 32 and w = 16 for a digit of two
cells. -/
theorem site_high {p : ℤ} {k top w : ℕ} (htop : top = 16 + w) (hk16 : 16 ≤ k) (hk : k ≤ top)
    {A q rh Ab Qb Rb : ℤ} (hA : |A| ≤ Ab) (hQ : |q| ≤ Qb) (hR : |rh| ≤ Rb)
    (hpH : 2 ^ (top - k) * Rb + 2 ^ w ≤ p)
    (hpL : Ab + 2 ^ (k - 1) + 2 ^ k * Qb + 2 ^ 16 * Rb + 2 ^ 16 ≤ p)
    (hH : ∃ t : ℤ, 0 ≤ t ∧ t < 2 ^ w ∧ high rh k top ≡ t [ZMOD p])
    (hL : ∃ t : ℤ, 0 ≤ t ∧ t < 2 ^ 16 ∧ site A q rh k ≡ t [ZMOD p]) :
    q = rhu A k ∧ 0 ≤ rh ∧ rh < 2 ^ (k - 16) := by
  obtain ⟨h0, h1⟩ := high_sound htop hk16 hk hR hpH hH
  exact ⟨(site_sound hk16 hA hQ hR h0 h1 hpL hL).1, h0, h1⟩

/-- A rounding by 2^16 without a high digit (the family XR): under the hypotheses below,
q = rhu(A, 16). -/
theorem site_low {p : ℤ} {A q Ab Qb : ℤ} (hA : |A| ≤ Ab) (hQ : |q| ≤ Qb)
    (hp : Ab + 2 ^ 15 + 2 ^ 16 * Qb + 2 ^ 16 ≤ p)
    (h : ∃ t : ℤ, 0 ≤ t ∧ t < 2 ^ 16 ∧ A + 2 ^ 15 - 2 ^ 16 * q ≡ t [ZMOD p]) : q = rhu A 16 := by
  have e : site A q 0 16 = A + 2 ^ 15 - 2 ^ 16 * q := by
    unfold site
    norm_num
  refine (site_sound (p := p) (k := 16) le_rfl (rh := 0) (Rb := 0) hA hQ (by simp) le_rfl
    (by norm_num) (by norm_num; linarith) ?_).1
  rw [e]
  exact h

/-! ## 3. The honest digits -/

/-- The remainder of a rounding: rem(A, k) = A + 2^(k−1) − 2^k rhu(A, k). -/
def rem (A : ℤ) (k : ℕ) : ℤ := A + 2 ^ (k - 1) - 2 ^ k * rhu A k

/-- Its high digit: hd(A, k) = ⌊rem(A, k) / 2^16⌋. -/
def hd (A : ℤ) (k : ℕ) : ℤ := rem A k / 2 ^ 16

theorem rem_eq_emod (A : ℤ) (k : ℕ) : rem A k = (A + 2 ^ (k - 1)) % 2 ^ k := by
  unfold rem rhu
  have := Int.emod_add_mul_ediv (A + 2 ^ (k - 1)) (2 ^ k)
  linarith

theorem rem_bounds (A : ℤ) (k : ℕ) : 0 ≤ rem A k ∧ rem A k < 2 ^ k := by
  rw [rem_eq_emod]
  exact ⟨Int.emod_nonneg _ (by positivity), Int.emod_lt_of_pos _ (by positivity)⟩

/-- For k ≥ 16 the honest high digit is in [0, 2^(k−16)). -/
theorem hd_bounds (A : ℤ) {k : ℕ} (hk16 : 16 ≤ k) : 0 ≤ hd A k ∧ hd A k < 2 ^ (k - 16) := by
  obtain ⟨h0, h1⟩ := rem_bounds A k
  have e : (2 : ℤ) ^ k = 2 ^ (k - 16) * 2 ^ 16 := by
    rw [← pow_add]
    congr 1
    omega
  unfold hd
  exact ⟨Int.ediv_nonneg h0 (by norm_num),
    Int.ediv_lt_of_lt_mul (by norm_num) (by rw [← e]; exact h1)⟩

/-- The honest low key is an entry of R16: it is the low digit of the remainder. -/
theorem site_hon (A : ℤ) (k : ℕ) :
    site A (rhu A k) (hd A k) k = rem A k % 2 ^ 16 ∧
    0 ≤ site A (rhu A k) (hd A k) k ∧
    site A (rhu A k) (hd A k) k < 2 ^ 16 := by
  have e : site A (rhu A k) (hd A k) k = rem A k % 2 ^ 16 := by
    have := Int.emod_add_mul_ediv (rem A k) (2 ^ 16)
    unfold site hd
    unfold rem at this ⊢
    linarith
  rw [e]
  exact ⟨rfl, Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩

/-- For 16 ≤ k ≤ top = 16 + w the honest high key is an entry of its table. -/
theorem high_hon (A : ℤ) {k top w : ℕ} (htop : top = 16 + w) (hk16 : 16 ≤ k) (hk : k ≤ top) :
    0 ≤ high (hd A k) k top ∧ high (hd A k) k top < 2 ^ w := by
  obtain ⟨h0, h1⟩ := hd_bounds A hk16
  have hpos : (0 : ℤ) < 2 ^ (top - k) := by positivity
  have e : (2 : ℤ) ^ w = 2 ^ (top - k) * 2 ^ (k - 16) := by
    rw [← pow_add]
    congr 1
    omega
  unfold high
  exact ⟨mul_nonneg hpos.le h0, by rw [e]; exact mul_lt_mul_of_pos_left h1 hpos⟩

/-- The relation determines the high digit: if the low key is an entry of R16 over the integers and
q = rhu(A, k), then rh = hd(A, k). -/
theorem hd_unique {k : ℕ} {A rh : ℤ} (h0 : 0 ≤ site A (rhu A k) rh k)
    (h1 : site A (rhu A k) rh k < 2 ^ 16) : rh = hd A k := by
  unfold site at h0 h1
  unfold hd rem
  have : (A + 2 ^ (k - 1) - 2 ^ k * rhu A k) / 2 ^ 16 = rh :=
    ((Int.ediv_emod_unique (by norm_num : (0 : ℤ) < 2 ^ 16)).mpr
      ⟨(by
          ring : (A + 2 ^ (k - 1) - 2 ^ k * rhu A k - 2 ^ 16 * rh) + 2 ^ 16 * rh =
            A + 2 ^ (k - 1) - 2 ^ k * rhu A k),
        h0, h1⟩).1
  exact this.symm

/-! ## 4. The two functions of affine forms -/

section Forms
open Blocks
variable {N E : Type} [Fintype N] [Field E]

/-- SITE(w, Q, k, RH) = 2^(k−1) w − 2^k Q − 2^16 RH, for a public weight w and forms Q, RH. -/
def SITE (w : E) (Q : Form N E) (k : ℕ) (RH : Form N E) : Form N E :=
  Form.const (2 ^ (k - 1) * w) - (2 ^ k : E) • Q - (2 ^ 16 : E) • RH

/-- HIGH(RH, k, top) = 2^(top−k) RH. -/
def HIGH (RH : Form N E) (k top : ℕ) : Form N E := (2 ^ (top - k) : E) • RH

theorem val_SITE (y : N → E) (w : E) (Q : Form N E) (k : ℕ) (RH : Form N E) :
    Form.val y (SITE w Q k RH) =
      2 ^ (k - 1) * w - 2 ^ k * Form.val y Q - 2 ^ 16 * Form.val y RH := by
  simp [SITE]

theorem val_HIGH (y : N → E) (RH : Form N E) (k top : ℕ) :
    Form.val y (HIGH RH k top) = high (Form.val y RH) k top := by
  simp [HIGH, high]

/-- With the weight 1, SITE is the low key without its accumulator. -/
theorem val_SITE_one (y : N → E) (A : E) (Q : Form N E) (k : ℕ) (RH : Form N E) :
    A + Form.val y (SITE 1 Q k RH) = site A (Form.val y Q) (Form.val y RH) k := by
  rw [val_SITE]
  unfold site
  ring

end Forms

/-! ## 5. Every shift: the two exponents and the two keys -/

/-- dn(k) = max(0, 16 − k): the remainder of a rounding by k is scaled by 2^dn(k), so that it fills
16 bits at least. -/
def dn (k : ℕ) : ℕ := 16 - k

/-- up(k) = max(k, 16): the number of bits of the scaled remainder. -/
def up (k : ℕ) : ℕ := max k 16

theorem dn_of_le {k : ℕ} (h : 16 ≤ k) : dn k = 0 := by unfold dn; omega

theorem up_of_le {k : ℕ} (h : 16 ≤ k) : up k = k := by unfold up; omega

theorem up_of_ge {k : ℕ} (h : k ≤ 16) : up k = 16 := by unfold up; omega

theorem dn_add (k : ℕ) : dn k + k = up k := by unfold dn up; omega

theorem le_up (k : ℕ) : 16 ≤ up k := by unfold up; omega

theorem up_le {k top : ℕ} (h16 : 16 ≤ top) (hk : k ≤ top) : up k ≤ top := by unfold up; omega

section KeysS
variable {R : Type} [CommRing R]

/-- The public weight 2^dn(k), as a function: x from 16 on, 2^(16−k) x below. -/
def scl (k : ℕ) (x : R) : R := if 16 ≤ k then x else 2 ^ dn k * x

/-- The low key for every shift: the scaled remainder without its high digit. -/
def ssite (A q rh : R) (k : ℕ) : R :=
  if 16 ≤ k then site A q rh k else 2 ^ dn k * (A + 2 ^ (k - 1) - 2 ^ k * q) - 2 ^ 16 * rh

/-- The high key for every shift. -/
def shigh (rh : R) (k top : ℕ) : R := if 16 ≤ k then high rh k top else high rh 16 top

theorem scl_of_le {k : ℕ} (h : 16 ≤ k) (x : R) : scl k x = x := if_pos h

/-- From 16 on the low key is the one of Section 1. -/
theorem ssite_of_le {k : ℕ} (h : 16 ≤ k) (A q rh : R) : ssite A q rh k = site A q rh k := if_pos h

/-- From 16 on the high key is the one of Section 1. -/
theorem shigh_of_le {k : ℕ} (h : 16 ≤ k) (rh : R) (top : ℕ) : shigh rh k top = high rh k top :=
  if_pos h

/-- The weight by the implementation's formula. -/
theorem scl_eq (k : ℕ) (x : R) : scl k x = 2 ^ dn k * x := by
  unfold scl
  split_ifs with h
  · rw [dn_of_le h, pow_zero, one_mul]
  · rfl

/-- The low key by the implementation's formula. -/
theorem ssite_eq (A q rh : R) (k : ℕ) :
    ssite A q rh k = 2 ^ dn k * (A + 2 ^ (k - 1) - 2 ^ k * q) - 2 ^ 16 * rh := by
  unfold ssite
  split_ifs with h
  · rw [dn_of_le h, pow_zero, one_mul]
    rfl
  · rfl

/-- The high key is the one of Section 1 at the shift up(k). -/
theorem shigh_eq_high (rh : R) (k top : ℕ) : shigh rh k top = high rh (up k) top := by
  unfold shigh
  split_ifs with h
  · rw [up_of_le h]
  · rw [up_of_ge (by omega)]

/-- The high key by the implementation's formula. -/
theorem shigh_eq (rh : R) (k top : ℕ) : shigh rh k top = 2 ^ (top - up k) * rh :=
  shigh_eq_high rh k top

theorem two_pow_dn_mul (k : ℕ) : (2 : R) ^ dn k * 2 ^ k = 2 ^ up k := by
  rw [← pow_add, dn_add]

/-- A rounding by k ≥ 1 is the rounding by up(k) of the scaled accumulator: the low key. -/
theorem ssite_eq_site {k : ℕ} (h : 1 ≤ k) (A q rh : R) :
    ssite A q rh k = site (2 ^ dn k * A) q rh (up k) := by
  have e : (2 : R) ^ dn k * 2 ^ (k - 1) = 2 ^ (up k - 1) := by
    rw [← pow_add]
    congr 1
    unfold dn up
    omega
  rw [ssite_eq]
  unfold site
  rw [← two_pow_dn_mul, ← e]
  ring

/-- The accumulator enters the low key multiplied by the public weight 2^dn(k). -/
theorem ssite_split (A q rh : R) (k : ℕ) : ssite A q rh k = scl k A + ssite 0 q rh k := by
  rw [ssite_eq, ssite_eq, scl_eq]
  ring

theorem scl_mul (k : ℕ) (a b : R) : scl k a * b = scl k (a * b) := by
  rw [scl_eq, scl_eq, mul_assoc]

theorem mul_scl (k : ℕ) (a b : R) : a * scl k b = scl k (a * b) := by
  rw [scl_eq, scl_eq, mul_left_comm]

theorem map_scl {R' : Type} [CommRing R'] (f : R →+* R') (k : ℕ) (x : R) :
    f (scl k x) = scl k (f x) := by
  simp [scl_eq, map_ofNat]

theorem map_ssite {R' : Type} [CommRing R'] (f : R →+* R') (A q rh : R) (k : ℕ) :
    f (ssite A q rh k) = ssite (f A) (f q) (f rh) k := by
  simp [ssite_eq, map_ofNat]

theorem map_shigh {R' : Type} [CommRing R'] (f : R →+* R') (rh : R) (k top : ℕ) :
    f (shigh rh k top) = shigh (f rh) k top := by
  simp [shigh_eq, map_ofNat]

end KeysS

/-- A rounding by k ≥ 1 is the rounding by up(k) of the scaled accumulator: the quotient. -/
theorem rhu_scale {k : ℕ} (h : 1 ≤ k) (A : ℤ) : rhu (2 ^ dn k * A) (up k) = rhu A k := by
  have e : (2 : ℤ) ^ dn k * 2 ^ (k - 1) = 2 ^ (up k - 1) := by
    rw [← pow_add]
    congr 1
    unfold dn up
    omega
  unfold rhu
  rw [← two_pow_dn_mul, ← e, ← mul_add]
  exact Int.mul_ediv_mul_of_pos _ _ (by positivity)

/-! ## 6. Every shift: what the keys imply -/

theorem two_pow_dn_le (k : ℕ) : (2 : ℤ) ^ dn k ≤ 2 ^ 16 :=
  pow_le_pow_right₀ (by norm_num) (by unfold dn; omega)

theorem two_pow_up_le {k top : ℕ} (h16 : 16 ≤ top) (hk : k ≤ top) : (2 : ℤ) ^ up k ≤ 2 ^ top :=
  pow_le_pow_right₀ (by norm_num) (up_le h16 hk)

/-- For top = 16 + w the multiplier of a high key is at most the number of rows of its table. -/
theorem two_pow_top_sub_le (k : ℕ) {top w : ℕ} (htop : top = 16 + w) :
    (2 : ℤ) ^ (top - up k) ≤ 2 ^ w :=
  pow_le_pow_right₀ (by norm_num) (by have := le_up k; omega)

/-- For k ≤ top, 16 ≤ top and Qb ≥ 0, the left side of the no-wrap condition of a low key, without
the digit's term, is at most 2^dn(k) Ab + 2^top + 2^top Qb: only the accumulator's bound is
multiplied by the weight 2^dn(k). -/
theorem scaled_le {k top : ℕ} (h16 : 16 ≤ top) (hk : k ≤ top) (Ab : ℤ) {Qb : ℤ} (hQ : 0 ≤ Qb) :
    2 ^ dn k * (Ab + 2 ^ (k - 1) + 2 ^ k * Qb) ≤ 2 ^ dn k * Ab + 2 ^ top + 2 ^ top * Qb := by
  have h1 : (2 : ℤ) ^ dn k * 2 ^ (k - 1) ≤ 2 ^ top := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by unfold dn; omega)
  have h2 : (2 : ℤ) ^ dn k * 2 ^ k * Qb ≤ 2 ^ top * Qb := by
    rw [two_pow_dn_mul]
    exact mul_le_mul_of_nonneg_right (two_pow_up_le h16 hk) hQ
  nlinarith

/-- Step L1 for a high digit, every shift: under the hypotheses below (among them k ≤ top = 16 + w,
where the table has 2^w rows), 0 ≤ rh < 2^(up(k)−16). -/
theorem shigh_sound {p : ℤ} {k top w : ℕ} (htop : top = 16 + w) (hk : k ≤ top) {rh Rb : ℤ}
    (hR : |rh| ≤ Rb) (hp : 2 ^ (top - up k) * Rb + 2 ^ w ≤ p)
    (h : ∃ t : ℤ, 0 ≤ t ∧ t < 2 ^ w ∧ shigh rh k top ≡ t [ZMOD p]) :
    0 ≤ rh ∧ rh < 2 ^ (up k - 16) := by
  rw [shigh_eq_high] at h
  exact high_sound htop (le_up k) (up_le (by omega) hk) hR hp h

/-- A bound on the low key from bounds on its parts: the left side of the implementation's condition
(W-name) (`SiteW`, Inst/Model/FF/ScalesDef.lean). -/
theorem abs_ssite_le {k : ℕ} {A q rh Ab Qb Rb : ℤ} (hA : |A| ≤ Ab)
    (hQ : |q| ≤ Qb) (hR : |rh| ≤ Rb) :
    |ssite A q rh k| ≤ 2 ^ dn k * (Ab + 2 ^ (k - 1) + 2 ^ k * Qb) + 2 ^ 16 * Rb := by
  have hA' := abs_le.mp hA
  have hQ' := abs_le.mp hQ
  have hR' := abs_le.mp hR
  have hk : (0 : ℤ) < 2 ^ k := by positivity
  have hk1 : (0 : ℤ) < 2 ^ (k - 1) := by positivity
  have hc : (0 : ℤ) < 2 ^ dn k := by positivity
  have h1 : 2 ^ k * q ≤ 2 ^ k * Qb := mul_le_mul_of_nonneg_left hQ'.2 hk.le
  have h2 : 2 ^ k * (-Qb) ≤ 2 ^ k * q := mul_le_mul_of_nonneg_left hQ'.1 hk.le
  have h3 : 2 ^ dn k * (A + 2 ^ (k - 1) - 2 ^ k * q) ≤ 2 ^ dn k * (Ab + 2 ^ (k - 1) + 2 ^ k * Qb) :=
    mul_le_mul_of_nonneg_left (by linarith) hc.le
  have h4 : 2 ^ dn k * (-(Ab + 2 ^ (k - 1) + 2 ^ k * Qb)) ≤
      2 ^ dn k * (A + 2 ^ (k - 1) - 2 ^ k * q) :=
    mul_le_mul_of_nonneg_left (by linarith) hc.le
  rw [ssite_eq, abs_le]
  constructor <;> linarith

/-- For every shift, over the integers: if the low key is an entry of R16 and 0 ≤ rh < 2^(up(k)−16),
then q = rhu(A, k). -/
theorem rhu_of_ssite {k : ℕ} {A q rh : ℤ} (hrh0 : 0 ≤ rh) (hrh1 : rh < 2 ^ (up k - 16))
    (h0 : 0 ≤ ssite A q rh k) (h1 : ssite A q rh k < 2 ^ 16) : q = rhu A k := by
  rw [ssite_eq] at h0 h1
  have hc : (0 : ℤ) < 2 ^ dn k := by positivity
  have hpos : (0 : ℤ) < 2 ^ k := by positivity
  have hU : (2 : ℤ) ^ dn k * 2 ^ k = 2 ^ 16 * 2 ^ (up k - 16) := by
    rw [two_pow_dn_mul, ← pow_add]
    congr 1
    have := le_up k
    omega
  have hd0 : (0 : ℤ) ≤ 2 ^ 16 * rh := mul_nonneg (by norm_num) hrh0
  have hd1 : (2 : ℤ) ^ 16 * (rh + 1) ≤ 2 ^ 16 * 2 ^ (up k - 16) :=
    mul_le_mul_of_nonneg_left (by omega) (by norm_num)
  have hr0 : 0 ≤ A + 2 ^ (k - 1) - 2 ^ k * q := nonneg_of_mul_nonneg_right (by linarith) hc
  have hr1 : A + 2 ^ (k - 1) - 2 ^ k * q < 2 ^ k :=
    lt_of_mul_lt_mul_left (by rw [hU]; linarith) hc.le
  have := (Int.ediv_emod_unique hpos).mpr
    ⟨(by ring : (A + 2 ^ (k - 1) - 2 ^ k * q) + 2 ^ k * q = A + 2 ^ (k - 1)), hr0, hr1⟩
  exact this.1.symm

/-- The low key of a rounding, every shift: with bounds on A, q, rh and no wrap-around (`hp`), with
0 ≤ rh < 2^(up(k)−16), and with the key congruent to an entry of R16: q = rhu(A, k), and the key is
an entry over the integers. -/
theorem ssite_sound {p : ℤ} {k : ℕ} {A q rh Ab Qb Rb : ℤ} (hA : |A| ≤ Ab) (hQ : |q| ≤ Qb)
    (hR : |rh| ≤ Rb) (hrh0 : 0 ≤ rh) (hrh1 : rh < 2 ^ (up k - 16))
    (hp : 2 ^ dn k * (Ab + 2 ^ (k - 1) + 2 ^ k * Qb) + 2 ^ 16 * Rb + 2 ^ 16 ≤ p)
    (h : ∃ t : ℤ, 0 ≤ t ∧ t < 2 ^ 16 ∧ ssite A q rh k ≡ t [ZMOD p]) :
    q = rhu A k ∧ 0 ≤ ssite A q rh k ∧ ssite A q rh k < 2 ^ 16 := by
  obtain ⟨h0, h1⟩ := range_of_key (abs_ssite_le hA hQ hR) hp h
  exact ⟨rhu_of_ssite hrh0 hrh1 h0 h1, h0, h1⟩

/-- A rounding with a high digit, every shift k ≤ top = 16 + w: both keys, with bounds on A, q, rh
and no wrap-around. top = 24 and w = 8 for a digit of one cell, top = 32 and w = 16 for a digit of
two cells. -/
theorem ssite_high {p : ℤ} {k top w : ℕ} (htop : top = 16 + w) (hk : k ≤ top) {A q rh Ab Qb Rb : ℤ}
    (hA : |A| ≤ Ab) (hQ : |q| ≤ Qb) (hR : |rh| ≤ Rb) (hpH : 2 ^ (top - up k) * Rb + 2 ^ w ≤ p)
    (hpL : 2 ^ dn k * (Ab + 2 ^ (k - 1) + 2 ^ k * Qb) + 2 ^ 16 * Rb + 2 ^ 16 ≤ p)
    (hH : ∃ t : ℤ, 0 ≤ t ∧ t < 2 ^ w ∧ shigh rh k top ≡ t [ZMOD p])
    (hL : ∃ t : ℤ, 0 ≤ t ∧ t < 2 ^ 16 ∧ ssite A q rh k ≡ t [ZMOD p]) :
    q = rhu A k ∧ 0 ≤ rh ∧ rh < 2 ^ (up k - 16) := by
  obtain ⟨h0, h1⟩ := shigh_sound htop hk hR hpH hH
  exact ⟨(ssite_sound hA hQ hR h0 h1 hpL hL).1, h0, h1⟩

/-- Up to 16 the range of the high digit is {0}. -/
theorem high_zero {k : ℕ} (hk : k ≤ 16) {rh : ℤ} (h0 : 0 ≤ rh) (h1 : rh < 2 ^ (up k - 16)) :
    rh = 0 := by
  rw [up_of_ge hk] at h1
  norm_num at h1
  omega

/-! ## 7. Every shift: the honest digits -/

/-- Up to 16 the honest high digit is 0. -/
theorem hd_of_le (A : ℤ) {k : ℕ} (hk : k ≤ 16) : hd A k = 0 := by
  obtain ⟨h0, h1⟩ := rem_bounds A k
  have : (2 : ℤ) ^ k ≤ 2 ^ 16 := pow_le_pow_right₀ (by norm_num) hk
  unfold hd
  exact Int.ediv_eq_zero_of_lt h0 (by linarith)

/-- The honest high digit is in [0, 2^(up(k)−16)). -/
theorem hd_bounds_up (A : ℤ) (k : ℕ) : 0 ≤ hd A k ∧ hd A k < 2 ^ (up k - 16) := by
  rcases le_total 16 k with h | h
  · rw [up_of_le h]
    exact hd_bounds A h
  · rw [hd_of_le A h]
    exact ⟨le_rfl, by positivity⟩

/-- The scaled remainder below 16 is an entry of R16. -/
theorem scaled_rem_bounds (A : ℤ) {k : ℕ} (hk : k ≤ 16) :
    0 ≤ 2 ^ dn k * rem A k ∧ 2 ^ dn k * rem A k < 2 ^ 16 := by
  obtain ⟨h0, h1⟩ := rem_bounds A k
  have hc : (0 : ℤ) < 2 ^ dn k := by positivity
  have e : (2 : ℤ) ^ dn k * 2 ^ k = 2 ^ 16 := by rw [two_pow_dn_mul, up_of_ge hk]
  exact ⟨mul_nonneg hc.le h0, by rw [← e]; exact mul_lt_mul_of_pos_left h1 hc⟩

/-- The honest low key is an entry of R16, every shift: it is the low digit of the scaled
remainder. -/
theorem ssite_hon (A : ℤ) (k : ℕ) :
    ssite A (rhu A k) (hd A k) k = (2 ^ dn k * rem A k) % 2 ^ 16 ∧
    0 ≤ ssite A (rhu A k) (hd A k) k ∧
    ssite A (rhu A k) (hd A k) k < 2 ^ 16 := by
  have e : ssite A (rhu A k) (hd A k) k = (2 ^ dn k * rem A k) % 2 ^ 16 := by
    rcases le_total 16 k with h | h
    · rw [ssite_of_le h, dn_of_le h, pow_zero, one_mul]
      exact (site_hon A k).1
    · obtain ⟨h0, h1⟩ := scaled_rem_bounds A h
      rw [Int.emod_eq_of_lt h0 h1, hd_of_le A h, ssite_eq]
      unfold rem
      ring
  rw [e]
  exact ⟨rfl, Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩

/-- The honest high key is an entry of its table, for every shift k ≤ top = 16 + w. -/
theorem shigh_hon (A : ℤ) {k top w : ℕ} (htop : top = 16 + w) (hk : k ≤ top) :
    0 ≤ shigh (hd A k) k top ∧ shigh (hd A k) k top < 2 ^ w := by
  rcases le_total 16 k with h | h
  · rw [shigh_of_le h]
    exact high_hon A htop h hk
  · rw [hd_of_le A h, shigh_eq, mul_zero]
    exact ⟨le_rfl, by positivity⟩

/-- The relation determines the high digit, every shift: if the low key is an entry of R16 over the
integers and q = rhu(A, k), then rh = hd(A, k). -/
theorem hd_unique_s {k : ℕ} {A rh : ℤ} (h0 : 0 ≤ ssite A (rhu A k) rh k)
    (h1 : ssite A (rhu A k) rh k < 2 ^ 16) : rh = hd A k := by
  rcases le_total 16 k with h | h
  · rw [ssite_of_le h] at h0 h1
    exact hd_unique h0 h1
  · obtain ⟨g0, g1⟩ := scaled_rem_bounds A h
    rw [hd_of_le A h]
    rw [ssite_eq] at h0 h1
    unfold rem at g0 g1
    omega

/-! ## 8. Every shift: the same two functions of affine forms -/

section FormsS
open Blocks
variable {N E : Type} [Fintype N] [Field E]

/-- SSITE(w, Q, k, RH) = 2^dn(k) (2^(k−1) w − 2^k Q) − 2^16 RH, for a public weight w and forms Q,
RH. -/
def SSITE (w : E) (Q : Form N E) (k : ℕ) (RH : Form N E) : Form N E :=
  if 16 ≤ k then SITE w Q k RH
  else (2 ^ dn k : E) • (Form.const (2 ^ (k - 1) * w) - (2 ^ k : E) • Q) - (2 ^ 16 : E) • RH

/-- SHIGH(RH, k, top) = 2^(top−up(k)) RH. -/
def SHIGH (RH : Form N E) (k top : ℕ) : Form N E := if 16 ≤ k then HIGH RH k top else HIGH RH 16 top

omit [Fintype N] in
theorem SSITE_of_le {k : ℕ} (h : 16 ≤ k) (w : E) (Q RH : Form N E) :
    SSITE w Q k RH = SITE w Q k RH := if_pos h

omit [Fintype N] in
theorem SHIGH_of_le {k : ℕ} (h : 16 ≤ k) (RH : Form N E) (top : ℕ) :
    SHIGH RH k top = HIGH RH k top := if_pos h

omit [Fintype N] in
/-- `SSITE` by the implementation's formula. -/
theorem SSITE_eq (w : E) (Q : Form N E) (k : ℕ) (RH : Form N E) :
    SSITE w Q k RH =
      (2 ^ dn k : E) • (Form.const (2 ^ (k - 1) * w) - (2 ^ k : E) • Q) - (2 ^ 16 : E) • RH := by
  unfold SSITE
  split_ifs with h
  · rw [dn_of_le h, pow_zero, one_smul]
    rfl
  · rfl

omit [Fintype N] in
/-- `SHIGH` by the implementation's formula. -/
theorem SHIGH_eq (RH : Form N E) (k top : ℕ) : SHIGH RH k top = (2 ^ (top - up k) : E) • RH := by
  unfold SHIGH
  split_ifs with h
  · rw [up_of_le h]
    rfl
  · rw [up_of_ge (by omega)]
    rfl

theorem val_SSITE (y : N → E) (w : E) (Q : Form N E) (k : ℕ) (RH : Form N E) :
    Form.val y (SSITE w Q k RH) =
      2 ^ dn k * (2 ^ (k - 1) * w - 2 ^ k * Form.val y Q) - 2 ^ 16 * Form.val y RH := by
  simp [SSITE_eq]

theorem val_SHIGH (y : N → E) (RH : Form N E) (k top : ℕ) :
    Form.val y (SHIGH RH k top) = shigh (Form.val y RH) k top := by
  simp [SHIGH_eq, shigh_eq]

/-- With the weight 1, SSITE is the low key without its accumulator, which enters multiplied by the
weight 2^dn(k). -/
theorem val_SSITE_one (y : N → E) (A : E) (Q : Form N E) (k : ℕ) (RH : Form N E) :
    scl k A + Form.val y (SSITE 1 Q k RH) = ssite A (Form.val y Q) (Form.val y RH) k := by
  rw [val_SSITE, ssite_eq, scl_eq]
  ring

/-! ## 9. Examples: at a fixed shift from 16 on the terms of Sections 5 and 8 unfold to those of
Sections 1 and 4 -/

example (A q rh : E) : ssite A q rh 17 = site A q rh 17 := rfl
example (rh : E) : shigh rh 17 24 = high rh 17 24 := rfl
example (x : E) : scl 17 x = x := rfl
example (w : E) (Q RH : Form N E) : SSITE w Q 17 RH = SITE w Q 17 RH := rfl
example (RH : Form N E) : SHIGH RH 17 24 = HIGH RH 17 24 := rfl
example : ssite (1000 : ℤ) 2 0 9 = 2 ^ 7 * (1000 + 2 ^ 8 - 2 ^ 9 * 2) := by norm_num [ssite, dn]
example : rhu 1000 9 = 2 ∧ hd 1000 9 = 0 := by decide

end FormsS

end Inst.Model.Site
