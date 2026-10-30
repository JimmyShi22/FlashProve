-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/End/Wit.lean: a value of the record of the late entries' names at which every premise on
names of the files beside it is met, for all sizes.

Definitions, statements and proofs. The theorems of Cb/Pv/Att/End/FirstOut.lean, Lin.lean and
LastOut.lean ask that the names which their forms read are names of late entries (Good8, LinGood and
so on). A record LateLay has finitely many late entries and tells good names apart, so a premise
that calls infinitely many names good cannot be met. This file shows that the premises as they stand
can be met: it gives one record, for every bound B, whose late entries are the names with all
indices at most B, and shows that all ten premises hold of it if B is large enough for the sizes.

Main names:
  RawC B: a cell's name with all indices at most B, as a finite type. enc, dec: from and to names.
  rawLe B r: all indices of the name r are at most B. dec_enc: on such names dec undoes enc.
  lateW B: the record. Its late entries are the pairs of a table's name and an element of RawC B.
  bd D ls lmS: a bound that is large enough.
  wit_lin, wit6b, wit6d, wit8, wit11, wit12, witM, wit16, wit18, witH: the ten premises hold of
    lateW B, if bd D ls lmS ≤ B.

Limits: the record is made for this purpose. It has more late entries than the programs' message
has, and nothing ties it to that message.


-/
import Cb.Pv.Att.End.LastOut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att.End
open Finset
open Inst.Model.AttSeg

/-! ### Names with bounded indices -/

/-- A number, cut at B. -/
def clip (B n : ℕ) : Fin (B + 1) := ⟨min n B, by omega⟩

theorem clip_val {B n : ℕ} (h : n ≤ B) : (clip B n).val = n := Nat.min_eq_left h

/-- A cell's name with all indices at most B: the kind of the name (eleven kinds: a cell of an entry
of either region counts as a kind) and five indices. A name of a kind with four indices has 0 as its
fifth. -/
abbrev RawC (B : ℕ) : Type :=
  Fin 11 × Fin (B + 1) × Fin (B + 1) × Fin (B + 1) × Fin (B + 1) × Fin (B + 1)

/-- From a name. -/
def enc (B : ℕ) : Raw → RawC B
  | .c .M jj b x => (0, clip B jj, clip B b, clip B x, clip B 0, clip B 0)
  | .c .D jj b x => (1, clip B jj, clip B b, clip B x, clip B 0, clip B 0)
  | .mx k b g i => (2, clip B k, clip B b, clip B g, clip B i, clip B 0)
  | .den k b g i => (3, clip B k, clip B b, clip B g, clip B i, clip B 0)
  | .ib k b g i => (4, clip B k, clip B b, clip B g, clip B i, clip B 0)
  | .qh b g i n => (5, clip B b, clip B g, clip B i, clip B n, clip B 0)
  | .qh' b g i n => (6, clip B b, clip B g, clip B i, clip B n, clip B 0)
  | .qry k b g i n => (7, clip B k, clip B b, clip B g, clip B i, clip B n)
  | .out k b g i n => (8, clip B k, clip B b, clip B g, clip B i, clip B n)
  | .key k lam g j n => (9, clip B k, clip B lam, clip B g, clip B j, clip B n)
  | .val k lam g j n => (10, clip B k, clip B lam, clip B g, clip B j, clip B n)

/-- To a name. -/
def dec (B : ℕ) : RawC B → Raw
  | (0, a, b, c, _, _) => .c .M a.val b.val c.val
  | (1, a, b, c, _, _) => .c .D a.val b.val c.val
  | (2, a, b, c, d, _) => .mx a.val b.val c.val d.val
  | (3, a, b, c, d, _) => .den a.val b.val c.val d.val
  | (4, a, b, c, d, _) => .ib a.val b.val c.val d.val
  | (5, a, b, c, d, _) => .qh a.val b.val c.val d.val
  | (6, a, b, c, d, _) => .qh' a.val b.val c.val d.val
  | (7, a, b, c, d, e) => .qry a.val b.val c.val d.val e.val
  | (8, a, b, c, d, e) => .out a.val b.val c.val d.val e.val
  | (9, a, b, c, d, e) => .key a.val b.val c.val d.val e.val
  | (_, a, b, c, d, e) => .val a.val b.val c.val d.val e.val

/-- All indices of a name are at most B. -/
def rawLe (B : ℕ) : Raw → Prop
  | .c _ jj b x => jj ≤ B ∧ b ≤ B ∧ x ≤ B
  | .mx k b g i => k ≤ B ∧ b ≤ B ∧ g ≤ B ∧ i ≤ B
  | .den k b g i => k ≤ B ∧ b ≤ B ∧ g ≤ B ∧ i ≤ B
  | .ib k b g i => k ≤ B ∧ b ≤ B ∧ g ≤ B ∧ i ≤ B
  | .qh b g i n => b ≤ B ∧ g ≤ B ∧ i ≤ B ∧ n ≤ B
  | .qh' b g i n => b ≤ B ∧ g ≤ B ∧ i ≤ B ∧ n ≤ B
  | .qry k b g i n => k ≤ B ∧ b ≤ B ∧ g ≤ B ∧ i ≤ B ∧ n ≤ B
  | .out k b g i n => k ≤ B ∧ b ≤ B ∧ g ≤ B ∧ i ≤ B ∧ n ≤ B
  | .key k lam g j n => k ≤ B ∧ lam ≤ B ∧ g ≤ B ∧ j ≤ B ∧ n ≤ B
  | .val k lam g j n => k ≤ B ∧ lam ≤ B ∧ g ≤ B ∧ j ≤ B ∧ n ≤ B

/-- On names with all indices at most B, dec undoes enc. -/
theorem dec_enc (B : ℕ) (r : Raw) (h : rawLe B r) : dec B (enc B r) = r := by
  cases r with
  | c ρ jj b x =>
    obtain ⟨h1, h2, h3⟩ := h
    cases ρ <;> simp only [enc, dec, clip_val h1, clip_val h2, clip_val h3]
  | mx k b g i =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp only [enc, dec, clip_val h1, clip_val h2, clip_val h3, clip_val h4]
  | den k b g i =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp only [enc, dec, clip_val h1, clip_val h2, clip_val h3, clip_val h4]
  | ib k b g i =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp only [enc, dec, clip_val h1, clip_val h2, clip_val h3, clip_val h4]
  | qh b g i n =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp only [enc, dec, clip_val h1, clip_val h2, clip_val h3, clip_val h4]
  | qh' b g i n =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp only [enc, dec, clip_val h1, clip_val h2, clip_val h3, clip_val h4]
  | qry k b g i n =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    simp only [enc, dec, clip_val h1, clip_val h2, clip_val h3, clip_val h4, clip_val h5]
  | out k b g i n =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    simp only [enc, dec, clip_val h1, clip_val h2, clip_val h3, clip_val h4, clip_val h5]
  | key k lam g j n =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    simp only [enc, dec, clip_val h1, clip_val h2, clip_val h3, clip_val h4, clip_val h5]
  | val k lam g j n =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    simp only [enc, dec, clip_val h1, clip_val h2, clip_val h3, clip_val h4, clip_val h5]

/-! ### The record -/

instance : Fintype AttTab :=
  ⟨{.tA, .tVM, .tVD, .tMm, .tQm, .tKm, .tMd, .tQd, .tKd, .hW, .hX, .hE, .hT, .hPi, .hR2, .tO, .qO,
    .qVM, .qVD, .qF, .qKx}, fun x => by cases x <;> simp⟩

/-- The record whose late entries are the names with all indices at most B. -/
def lateW (B : ℕ) : LateLay AttTab (AttTab × RawC B) where
  nm := fun j => (j.1, dec B j.2)
  at' := fun x => (x.1, enc B x.2)
  good := fun x => rawLe B x.2
  ok := fun x hx => by
    show (x.1, dec B (enc B x.2)) = x
    rw [dec_enc B x.2 hx]

/-! ### The premises on names -/

/-- A bound that is large enough for the sizes. -/
def bd (D : Dim) (ls lmS : ℕ) : ℕ :=
  5 + D.nb + D.nG + D.nl + D.lT + 2 ^ (D.lM + lmS) + 2 ^ (D.lD + lmS) + 2 ^ (D.ln + ls)

/-- The parts of the bound. -/
theorem bd_le (D : Dim) (ls lmS : ℕ) :
    5 + D.nb + D.nG + D.nl + D.lT ≤ bd D ls lmS ∧ 2 ^ (D.lM + lmS) ≤ bd D ls lmS ∧
      2 ^ (D.lD + lmS) ≤ bd D ls lmS ∧ 2 ^ (D.ln + ls) ≤ bd D ls lmS := by
  unfold bd
  generalize 2 ^ (D.lM + lmS) = a
  generalize 2 ^ (D.lD + lmS) = b
  generalize 2 ^ (D.ln + ls) = c
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- A multiple of a block's size below the size of the whole. -/
theorem blk_le {l s hi : ℕ} (h : hi < 2 ^ (l - s)) : 0 + hi * 2 ^ s ≤ 2 ^ (l + s) := by
  have h1 : 2 ^ (l - s) ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le l s)
  rw [Nat.zero_add, pow_add]
  exact Nat.mul_le_mul_right _ (Nat.le_of_lt (Nat.lt_of_lt_of_le h h1))

variable (D : Dim) (ls lmS : ℕ) {B : ℕ} (hB : bd D ls lmS ≤ B)
include hB

/-- The layer of a pair is at most B. -/
theorem lam_le {b : ℕ} (hb : b < D.nb) : D.lamOf b ≤ B := by
  have h1 : D.lamOf b ≤ b := Nat.div_le_self b D.na
  have h2 := (bd_le D ls lmS).1
  omega

/-- The first feature of a block of a head's features is at most B. -/
theorem feat_le {ch : ℕ} (hc : ch < 2 ^ (D.ln - ls)) : 0 + ch * 2 ^ ls ≤ B :=
  le_trans (blk_le hc) (le_trans (bd_le D ls lmS).2.2.2 hB)

/-- The names of a tensor's limbs, at the first feature of a block. -/
theorem long_le {k a g ch : ℕ} (hk : k < 2) (ha : a ≤ B) (hg : g < D.nG)
    (hc : ch < 2 ^ (D.ln - ls)) :
    k ≤ B ∧ a ≤ B ∧ g ≤ B ∧ 0 ≤ B ∧ 0 + ch * 2 ^ ls ≤ B := by
  have h2 := (bd_le D ls lmS).1
  exact ⟨by omega, ha, by omega, Nat.zero_le _, feat_le D ls lmS hB hc⟩

theorem nb_le {b : ℕ} (hb : b < D.nb) : b ≤ B := by
  have h2 := (bd_le D ls lmS).1
  omega

/-- The names of the limbs of a number a position. -/
theorem row_le {k b g : ℕ} (hk : k < 4) (hb : b < D.nb) (hg : g < D.nG) :
    k ≤ B ∧ b ≤ B ∧ g ≤ B ∧ 0 ≤ B := by
  have h2 := (bd_le D ls lmS).1
  exact ⟨by omega, by omega, by omega, Nat.zero_le _⟩

/-- The names of the bits of the index. -/
theorem bit_le {k b g : ℕ} (hk : k < D.lT) (hb : b < D.nb) (hg : g < D.nG) :
    k ≤ B ∧ b ≤ B ∧ g ≤ B ∧ 0 ≤ B := by
  have h2 := (bd_le D ls lmS).1
  exact ⟨by omega, by omega, by omega, Nat.zero_le _⟩

/-- The names of the cells of a region's entries. l: the bits of an entry of the region. -/
theorem col_le {l jj b hi : ℕ} (hl : 2 ^ (l + lmS) ≤ bd D ls lmS) (hj : jj < 5) (hb : b < D.nb)
    (hh : hi < 2 ^ (l - lmS)) : jj ≤ B ∧ b ≤ B ∧ 0 + hi * 2 ^ lmS ≤ B := by
  have h2 := (bd_le D ls lmS).1
  exact ⟨by omega, by omega, le_trans (blk_le hh) (le_trans hl hB)⟩

theorem wit8 : Good8 D ls (lateW B) where
  hE := fun _ hb _ hg _ hk => row_le D ls lmS hB hk hb hg
  qO := fun _ hb _ hg _ hc _ hk => long_le D ls lmS hB hk (nb_le D ls lmS hB hb) hg hc

theorem wit6d : Good6d D ls (lateW B) where
  tQ := fun _ hb _ hg _ hc _ hk => long_le D ls lmS hB hk (nb_le D ls lmS hB hb) hg hc
  tK := fun _ hb _ hg _ hc _ hk => long_le D ls lmS hB hk (lam_le D ls lmS hB hb) hg hc

theorem wit6b : Good6b D ls (lateW B) where
  tQ := fun _ hb _ hg _ hc _ hk => long_le D ls lmS hB hk (nb_le D ls lmS hB hb) hg hc
  tK := fun _ hb _ hg _ hc _ hk => long_le D ls lmS hB hk (lam_le D ls lmS hB hb) hg hc

theorem wit11 : Good11 D ls lmS (lateW B) where
  tVM := fun _ hb _ hj _ hh => col_le D ls lmS hB (bd_le D ls lmS).2.1 hj hb hh
  qVM := fun _ hb _ hg _ hc _ hk => long_le D ls lmS hB hk (lam_le D ls lmS hB hb) hg hc

theorem wit12 : Good12 D ls lmS (lateW B) where
  tVD := fun _ hb _ hj _ hh => col_le D ls lmS hB (bd_le D ls lmS).2.2.1 hj hb hh
  qVD := fun _ hb _ hg _ hc _ hk => long_le D ls lmS hB hk (lam_le D ls lmS hB hb) hg hc

theorem witM : GoodM D (lateW B) where
  hT := fun _ hb _ hg _ hk => row_le D ls lmS hB hk hb hg

theorem wit16 : Good16 D ls (lateW B) where
  qF := fun _ hb _ hg _ hc _ hk => long_le D ls lmS hB hk (nb_le D ls lmS hB hb) hg hc

theorem wit18 : Good18 D ls (lateW B) where
  qKx := fun lam hl _ hg _ hc _ hk => long_le D ls lmS hB hk
    (by have h2 := (bd_le D ls lmS).1; omega) hg hc
  hPi := fun _ hb _ hk _ hg => bit_le D ls lmS hB hk hb hg

theorem witH : GoodH D (lateW B) where
  hR2 := fun _ hb _ hk _ hg => bit_le D ls lmS hB hk hb hg

theorem wit_lin : LinGood D ls lmS (lateW B) where
  tA := fun u jj b hu hj hb hi hh => by
    have h2 : 2 ^ (u.l D + lmS) ≤ bd D ls lmS := by
      cases u with
      | m1 => exact (bd_le D ls lmS).2.1
      | m2 => exact (bd_le D ls lmS).2.1
      | d1 => exact (bd_le D ls lmS).2.2.1
      | d2 => exact (bd_le D ls lmS).2.2.1
      | w3 => exact hu.elim
      | x3 => exact hu.elim
      | f4 => exact hu.elim
    exact col_le D ls lmS hB h2 hj hb hh
  tMm := fun _ hb _ hg _ hk => row_le D ls lmS hB hk hb hg
  tMd := fun _ hb _ hg _ hk => row_le D ls lmS hB hk hb hg
  hW := fun _ hb _ hg _ hk => row_le D ls lmS hB hk hb hg
  hX := fun _ hk _ hb _ hg => bit_le D ls lmS hB hk hb hg
  tO := fun b hb g hg ch hc => by
    have h2 := (bd_le D ls lmS).1
    have e : b ≤ B ∧ g ≤ B ∧ 0 ≤ B ∧ 0 + ch * 2 ^ ls ≤ B :=
      ⟨by omega, by omega, Nat.zero_le _, feat_le D ls lmS hB hc⟩
    exact ⟨e, e⟩

end Cb.Pv.Att.End

#print axioms Cb.Pv.Att.End.dec_enc
#print axioms Cb.Pv.Att.End.wit_lin
#print axioms Cb.Pv.Att.End.wit12
#print axioms Cb.Pv.Att.End.wit18
