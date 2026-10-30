-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/GatedCl.lean: the verifier's claims on the end values of the two product layers of the
gated products, as forms on committed entries, and what they say on cells.

The check of a layers' sub-proof ends in linear claims. This file writes the four that tie the
hidden end values of the two product layers of the gated products to the tables of reads, as forms
(Blocks/Form.lean) on entries of two kinds: entries of the mask row, which hide what was shown, and
entries of the tables of reads, which are sent late. The forms are functions of what the verifier
has heard and drawn (the record GatedE) and of names for the entries (the record GatedNames). No
state of a program occurs.

Definitions.
 - GatedE: the two layers' points r5 and r6, the factors β5 and β6 of the masks of the end values,
   and the four values that were shown.
 - GatedNames J: the entries' names in a type J.
 - hid: a hidden value as a form: what was shown less the factor times the mask entry.
 - cEnd: one claim. gatedCl: the list of the four.
 - GatedTables: what the entries of the tables of reads are meant to be, on cells t.
 - GatedLast: what the claims say on cells: each hidden end value is the extension of the library's
   map (slV, upV, slV', upV' in Inst/Model/FF/Objects.lean) at the layer's point.

Main theorems. gated_last: on entries y with true tables, if every form of gatedCl is worth 0, then
GatedLast. first_sum, second_sum: the sums on which the two layers run, in the library's hhU: the
first is the extension of Hh1t; the second is, under the equality weights of its first coordinates,
the sum over the routed layers of the extensions of their gated products.

Limits. The two claims that the sumchecks themselves leave (rows on the hiding coefficients) are not
in the list. That the list is a program's is not said here. The numbers of hidden units are powers
of two. Identities alone: nothing on a distribution of a challenge and nothing on soundness.


-/
import Blocks.Form
import Inst.Model.FF.Objects
import Cb.Pv.Lay.End.Cube

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End.Gated

open Finset
open Inst.Model.FFSeg (Dim Cell Arr val hh hhU Hh1t slV upV slV' upV' lF lFe)
open Blocks (ext eqN Form)

/-! ## Numbers and extensions -/

/-- A number below 2^m, read as a block of 2^s and a place in the block. -/
theorem idx_blocks (s m Y first : ℕ) (h : s ≤ m) :
    Y / 2 ^ s / 2 ^ (m - s) = Y / 2 ^ m ∧
      (first + Y / 2 ^ s % 2 ^ (m - s)) * 2 ^ s + Y % 2 ^ s = first * 2 ^ s + Y % 2 ^ m := by
  have e : 2 ^ m = 2 ^ s * 2 ^ (m - s) := by
    rw [← pow_add]
    congr 1
    omega
  constructor
  · rw [Nat.div_div_eq_div_mul, ← e]
  · rw [e, Nat.mod_mul]
    ring

section Ext

variable {K : Type} [Field K]

/-- The extension of a negative. -/
theorem ext_neg (g : ℕ) (v p : ℕ → K) : ext g (fun X => -v X) p = -ext g v p := by
  unfold Blocks.ext
  rw [← sum_neg_distrib]
  exact sum_congr rfl fun X _ => by ring

/-- The extension over two-part indices (x | y), one part after the other. -/
theorem ext_nest (g g' : ℕ) (v p : ℕ → K) :
    ext (g + g') v p =
      ext g (fun x => ext g' (fun y => v (x * 2 ^ g' + y)) (fun j => p (g + j))) p := by
  rw [Blocks.ext_two]
  unfold Blocks.ext
  refine sum_congr rfl fun x _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun y _ => ?_
  rw [eqN_off g' g p y]
  ring

/-- The extension over three-part indices (x | q | i), with the two outer sums written out. -/
theorem ext_parts (g s l : ℕ) (V p : ℕ → K) :
    ext (g + s + l) V p = ∑ x ∈ range (2 ^ g), eqN g 0 p x *
      ∑ q ∈ range (2 ^ s), eqN s g p q *
        ext l (fun i => V ((x * 2 ^ s + q) * 2 ^ l + i)) (fun j => p (g + s + j)) := by
  rw [ext_nest (g + s) l, Blocks.ext_two]
  refine sum_congr rfl fun x _ => ?_
  rw [mul_sum]
  exact sum_congr rfl fun q _ => by ring

end Ext

/-! ## The forms -/

/-- What the claims on the end values read of what the verifier has heard and drawn. -/
structure GatedE (E : Type) where
  r5 : ℕ → E
  r6 : ℕ → E
  β5 : E
  β6 : E
  shL5 : E
  shR5 : E
  shL6 : E
  shR6 : E

/-- The names of the entries that the claims read. -/
structure GatedNames (J : Type) where
  /-- the mask entries of the four end values -/
  mL5 : J
  mR5 : J
  mL6 : J
  mR6 : J
  /-- the reads: limb l of block kh of layer lam, of the tensors s and u, at the last coordinates of
  the first layer's point and of the second's -/
  uS5 : ℕ → ℕ → ℕ → J
  uU5 : ℕ → ℕ → ℕ → J
  uS6 : ℕ → ℕ → ℕ → J
  uU6 : ℕ → ℕ → ℕ → J

section Forms

variable {E J : Type} [Field E] [DecidableEq J]

/-- A hidden value: what was shown less the factor times the mask entry. -/
def hid (sh β : E) (m : J) : Form J E := Form.const sh - β • Form.ent m

/-- One claim: the hidden end value plus the tensor's reads, each block under the equality weight of
its number at the first g coordinates of the layer's point. rows, blocks: the layers and the blocks
of a layer that are read; lamOf: the layer's number; first: the first block. -/
def cEnd (sh β : E) (m : J) (u : ℕ → ℕ → ℕ → J) (r : ℕ → E) (g rows blocks : ℕ) (lamOf : ℕ → ℕ)
    (first : ℕ) : Form J E :=
  hid sh β m + ∑ x ∈ range (rows * blocks), eqN g 0 r x •
    ∑ l ∈ range 2, (256 : E) ^ l • Form.ent (u l (lamOf (x / blocks)) (first + x % blocks))

/-- The four claims. s: the bits of a feature in its block. -/
def gatedCl (N : GatedNames J) (e : GatedE E) (D : Dim) (s : ℕ) : List (Form J E) :=
  [cEnd e.shL5 e.β5 N.mL5 N.uS5 e.r5 (D.lL + lF D - s) (2 ^ D.lL) (2 ^ (lF D - s)) id 0,
   cEnd e.shR5 e.β5 N.mR5 N.uU5 e.r5 (D.lL + lF D - s) (2 ^ D.lL) (2 ^ (lF D - s)) id 0,
   cEnd e.shL6 e.β6 N.mL6 N.uS6 e.r6 (D.lL - 1 + lFe D - s) (2 ^ (D.lL - 1)) (2 ^ (lFe D - s))
     (fun lm => 2 * lm + 1) (2 ^ (lFe D - s)),
   cEnd e.shR6 e.β6 N.mR6 N.uU6 e.r6 (D.lL - 1 + lFe D - s) (2 ^ (D.lL - 1)) (2 ^ (lFe D - s))
     (fun lm => 2 * lm + 1) (2 ^ (lFe D - s))]

end Forms

/-! ## What the forms say on cells -/

section Means

variable {E J : Type} [Field E] [Fintype J] [DecidableEq J]

/-- What the read of limb l of block kh of layer lam of the array A is meant to be, at the last
s + lT coordinates of a point r of g + s + lT coordinates. -/
def readAt (D : Dim) (t : Cell → E) (A : Arr) (r : ℕ → E) (g s l lam kh : ℕ) : E :=
  ∑ q ∈ range (2 ^ s), eqN s g r q *
    ext D.lT (fun p => t ⟨A, l, lam, kh * 2 ^ s + q, p⟩) (fun j => r (g + s + j))

/-- What the entries of the tables of reads that the four claims read are meant to be, on the cells
t. -/
structure GatedTables (N : GatedNames J) (e : GatedE E) (D : Dim) (t : Cell → E) (s : ℕ)
    (y : J → E) : Prop where
  s5 : ∀ l, l < 2 → ∀ i, i < 2 ^ D.lL → ∀ b, b < 2 ^ (lF D - s) →
    y (N.uS5 l i b) = readAt D t .sl e.r5 (D.lL + lF D - s) s l i b
  u5 : ∀ l, l < 2 → ∀ i, i < 2 ^ D.lL → ∀ b, b < 2 ^ (lF D - s) →
    y (N.uU5 l i b) = readAt D t .up e.r5 (D.lL + lF D - s) s l i b
  s6 : ∀ l, l < 2 → ∀ i, i < 2 ^ (D.lL - 1) → ∀ b, b < 2 ^ (lFe D - s) →
    y (N.uS6 l (2 * i + 1) (2 ^ (lFe D - s) + b)) =
      readAt D t .sl e.r6 (D.lL - 1 + lFe D - s) s l (2 * i + 1) (2 ^ (lFe D - s) + b)
  u6 : ∀ l, l < 2 → ∀ i, i < 2 ^ (D.lL - 1) → ∀ b, b < 2 ^ (lFe D - s) →
    y (N.uU6 l (2 * i + 1) (2 ^ (lFe D - s) + b)) =
      readAt D t .up e.r6 (D.lL - 1 + lFe D - s) s l (2 * i + 1) (2 ^ (lFe D - s) + b)

/-- What the four claims say on cells. -/
structure GatedLast (N : GatedNames J) (e : GatedE E) (D : Dim) (t : Cell → E) (y : J → E) :
    Prop where
  L5 : e.shL5 - e.β5 * y N.mL5 = ext (D.lL + lF D + D.lT) (slV D t) e.r5
  R5 : e.shR5 - e.β5 * y N.mR5 = ext (D.lL + lF D + D.lT) (upV D t) e.r5
  L6 : e.shL6 - e.β6 * y N.mL6 = ext (D.lL - 1 + lFe D + D.lT) (slV' D t) e.r6
  R6 : e.shR6 - e.β6 * y N.mR6 = ext (D.lL - 1 + lFe D + D.lT) (upV' D t) e.r6

omit [Fintype J] [DecidableEq J] in
/-- The two limbs' reads under the powers of 256 are the read of the array's value. -/
theorem limbs_read (D : Dim) (t : Cell → E) (A : Arr) (hn : A.nCell = 2) (ho : A.off = 0)
    (r : ℕ → E) (g s lam kh : ℕ) :
    ∑ l ∈ range 2, (256 : E) ^ l * readAt D t A r g s l lam kh =
      ∑ q ∈ range (2 ^ s), eqN s g r q *
        ext D.lT (fun p => val t A lam (kh * 2 ^ s + q) p) (fun j => r (g + s + j)) := by
  unfold readAt
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun q _ => ?_
  have e : (fun p => val t A lam (kh * 2 ^ s + q) p) =
      fun p => ∑ l ∈ range 2, (256 : E) ^ l * t ⟨A, l, lam, kh * 2 ^ s + q, p⟩ := by
    funext p
    unfold Inst.Model.FFSeg.val
    rw [hn, ho]
    simp
  rw [e, Blocks.ext_sum, mul_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [Blocks.ext_smul]
  ring

/-- What one claim is worth on entries with true reads. -/
theorem val_cEnd (D : Dim) (t : Cell → E) (A : Arr) (hn : A.nCell = 2) (ho : A.off = 0)
    (sh β : E) (m : J) (u : ℕ → ℕ → ℕ → J) (r : ℕ → E) {g s rows blocks : ℕ} (lamOf : ℕ → ℕ)
    (first : ℕ) (hg : rows * blocks = 2 ^ g) (y : J → E)
    (hT : ∀ l, l < 2 → ∀ i, i < rows → ∀ b, b < blocks →
      y (u l (lamOf i) (first + b)) = readAt D t A r g s l (lamOf i) (first + b)) :
    Form.val y (cEnd sh β m u r g rows blocks lamOf first) = sh - β * y m +
      ext (g + s + D.lT)
        (fun Z => val t A (lamOf (Z / 2 ^ D.lT / 2 ^ s / blocks))
          ((first + Z / 2 ^ D.lT / 2 ^ s % blocks) * 2 ^ s + Z / 2 ^ D.lT % 2 ^ s)
          (Z % 2 ^ D.lT)) r := by
  unfold cEnd hid
  rw [map_add, map_sub, map_smul, Form.val_const, Form.val_ent, smul_eq_mul, map_sum, hg,
    ext_parts]
  refine congrArg (sh - β * y m + ·) (sum_congr rfl fun x hx => ?_)
  have hx' : x < rows * blocks := by
    rw [hg]
    exact mem_range.mp hx
  have hb0 : 0 < blocks := by
    rcases Nat.eq_zero_or_pos blocks with e | h
    · rw [e, Nat.mul_zero] at hx'
      exact absurd hx' (Nat.not_lt_zero _)
    · exact h
  have hxr : x / blocks < rows := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hx')
  rw [map_smul, smul_eq_mul, map_sum]
  refine congrArg (eqN g 0 r x * ·) ?_
  have e1 : ∑ l ∈ range 2,
      Form.val y ((256 : E) ^ l • Form.ent (u l (lamOf (x / blocks)) (first + x % blocks))) =
      ∑ l ∈ range 2, (256 : E) ^ l *
        readAt D t A r g s l (lamOf (x / blocks)) (first + x % blocks) :=
    sum_congr rfl fun l hl => by
      rw [map_smul, smul_eq_mul, Form.val_ent,
        hT l (mem_range.mp hl) _ hxr _ (Nat.mod_lt _ hb0)]
  rw [e1, limbs_read D t A hn ho]
  refine sum_congr rfl fun q hq => ?_
  refine congrArg (eqN s g r q * ·) (Blocks.ext_congr (fun i hi => ?_) _)
  obtain ⟨a1, a2⟩ := div_mod_at (x * 2 ^ s + q) i (2 ^ D.lT) hi
  obtain ⟨a3, a4⟩ := div_mod_at x q (2 ^ s) (mem_range.mp hq)
  rw [a1, a2, a3, a4]

/-- On entries with true tables, the four claims say GatedLast. -/
theorem gated_last (N : GatedNames J) (e : GatedE E) (D : Dim) (t : Cell → E) (s : ℕ) (y : J → E)
    (h1 : s ≤ lF D) (h2 : s ≤ lFe D) (hfe : D.fe = 2 ^ lFe D) (T : GatedTables N e D t s y)
    (h : ∀ f ∈ gatedCl N e D s, Form.val y f = 0) : GatedLast N e D t y := by
  have hT : D.T = 2 ^ D.lT := rfl
  have g5 : 2 ^ D.lL * 2 ^ (lF D - s) = 2 ^ (D.lL + lF D - s) := by
    rw [← pow_add]
    congr 1
    omega
  have g6 : 2 ^ (D.lL - 1) * 2 ^ (lFe D - s) = 2 ^ (D.lL - 1 + lFe D - s) := by
    rw [← pow_add]
    congr 1
    omega
  have s5 : D.lL + lF D - s + s + D.lT = D.lL + lF D + D.lT := by omega
  have s6 : D.lL - 1 + lFe D - s + s + D.lT = D.lL - 1 + lFe D + D.lT := by omega
  have hfe2 : 2 ^ (lFe D - s) * 2 ^ s = D.fe := by
    rw [hfe, ← pow_add]
    congr 1
    omega
  have m1 := h _ (by simp [gatedCl] : cEnd e.shL5 e.β5 N.mL5 N.uS5 e.r5 (D.lL + lF D - s)
    (2 ^ D.lL) (2 ^ (lF D - s)) id 0 ∈ gatedCl N e D s)
  have m2 := h _ (by simp [gatedCl] : cEnd e.shR5 e.β5 N.mR5 N.uU5 e.r5 (D.lL + lF D - s)
    (2 ^ D.lL) (2 ^ (lF D - s)) id 0 ∈ gatedCl N e D s)
  have m3 := h _ (by simp [gatedCl] : cEnd e.shL6 e.β6 N.mL6 N.uS6 e.r6 (D.lL - 1 + lFe D - s)
    (2 ^ (D.lL - 1)) (2 ^ (lFe D - s)) (fun lm => 2 * lm + 1) (2 ^ (lFe D - s)) ∈
      gatedCl N e D s)
  have m4 := h _ (by simp [gatedCl] : cEnd e.shR6 e.β6 N.mR6 N.uU6 e.r6 (D.lL - 1 + lFe D - s)
    (2 ^ (D.lL - 1)) (2 ^ (lFe D - s)) (fun lm => 2 * lm + 1) (2 ^ (lFe D - s)) ∈
      gatedCl N e D s)
  rw [val_cEnd D t .sl rfl rfl _ _ _ _ _ _ _ g5 y (fun l hl i hi b hb => by
    rw [id_eq, Nat.zero_add]
    exact T.s5 l hl i hi b hb), s5] at m1
  rw [val_cEnd D t .up rfl rfl _ _ _ _ _ _ _ g5 y (fun l hl i hi b hb => by
    rw [id_eq, Nat.zero_add]
    exact T.u5 l hl i hi b hb), s5] at m2
  rw [val_cEnd D t .sl rfl rfl _ _ _ _ _ _ _ g6 y T.s6, s6] at m3
  rw [val_cEnd D t .up rfl rfl _ _ _ _ _ _ _ g6 y T.u6, s6] at m4
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Blocks.ext_congr (w := fun Z => -slV D t Z) (fun Z _ => by
      obtain ⟨i1, i2⟩ := idx_blocks s (lF D) (Z / 2 ^ D.lT) 0 h1
      unfold Inst.Model.FFSeg.slV
      rw [id_eq, i1, i2, hT, Nat.zero_mul, Nat.zero_add]
      simp only [neg_neg]), ext_neg] at m1
    linear_combination m1
  · rw [Blocks.ext_congr (w := fun Z => -upV D t Z) (fun Z _ => by
      obtain ⟨i1, i2⟩ := idx_blocks s (lF D) (Z / 2 ^ D.lT) 0 h1
      unfold Inst.Model.FFSeg.upV
      rw [id_eq, i1, i2, hT, Nat.zero_mul, Nat.zero_add]
      simp only [neg_neg]), ext_neg] at m2
    linear_combination m2
  · rw [Blocks.ext_congr (w := fun Z => -slV' D t Z) (fun Z _ => by
      obtain ⟨i1, i2⟩ := idx_blocks s (lFe D) (Z / 2 ^ D.lT) (2 ^ (lFe D - s)) h2
      unfold Inst.Model.FFSeg.slV'
      rw [i1, i2, hT, hfe2]
      simp only [neg_neg]), ext_neg] at m3
    linear_combination m3
  · rw [Blocks.ext_congr (w := fun Z => -upV' D t Z) (fun Z _ => by
      obtain ⟨i1, i2⟩ := idx_blocks s (lFe D) (Z / 2 ^ D.lT) (2 ^ (lFe D - s)) h2
      unfold Inst.Model.FFSeg.upV'
      rw [i1, i2, hT, hfe2]
      simp only [neg_neg]), ext_neg] at m4
    linear_combination m4

end Means

/-! ## The sums on which the two layers run -/

section Sums

variable {E : Type} [Field E]

/-- The first layer's sum is the extension of the library's Hh1t at the point's first coordinates,
with the point's last coordinates as the token point. -/
theorem first_sum (D : Dim) (t : Cell → E) (p : ℕ → E) :
    ext (D.lL + lF D + D.lT) (fun X => slV D t X * upV D t X) p =
      ext (D.lL + lF D) (Hh1t D t fun j => p (D.lL + lF D + j)) p := by
  have hT : D.T = 2 ^ D.lT := rfl
  rw [ext_nest]
  refine Blocks.ext_congr (fun x _ => ?_) _
  unfold Inst.Model.FFSeg.Hh1t Inst.Model.FFSeg.hhU
  refine Blocks.ext_congr (fun y hy => ?_) _
  obtain ⟨e1, e2⟩ := div_mod_at x y (2 ^ D.lT) hy
  unfold Inst.Model.FFSeg.slV Inst.Model.FFSeg.upV Inst.Model.FFSeg.hh
  rw [hT, e1, e2]
  ring

/-- The second layer's sum, by routed layer. -/
theorem second_sum (D : Dim) (t : Cell → E) (p : ℕ → E) :
    ext (D.lL - 1 + lFe D + D.lT) (fun X => slV' D t X * upV' D t X) p =
      ∑ lm ∈ range (2 ^ (D.lL - 1)), eqN (D.lL - 1) 0 p lm *
        ext (lFe D) (fun j => hhU D t (2 * lm + 1) (D.fe + j) fun i => p (D.lL - 1 + lFe D + i))
          (fun j => p (D.lL - 1 + j)) := by
  have hT : D.T = 2 ^ D.lT := rfl
  rw [ext_nest, ext_nest]
  refine sum_congr rfl fun lm _ => ?_
  refine congrArg (eqN (D.lL - 1) 0 p lm * ·) (Blocks.ext_congr (fun j hj => ?_) _)
  unfold Inst.Model.FFSeg.hhU
  refine Blocks.ext_congr (fun y hy => ?_) _
  obtain ⟨e1, e2⟩ := div_mod_at (lm * 2 ^ lFe D + j) y (2 ^ D.lT) hy
  obtain ⟨e3, e4⟩ := div_mod_at lm j (2 ^ lFe D) hj
  unfold Inst.Model.FFSeg.slV' Inst.Model.FFSeg.upV' Inst.Model.FFSeg.hh
  rw [hT, e1, e2, e3, e4]
  ring

end Sums

end Cb.Pv.Lay.End.Gated
