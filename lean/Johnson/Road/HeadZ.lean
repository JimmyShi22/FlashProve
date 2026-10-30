-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadZ.lean: from a family of matrices of the library's model back to matrices that are
named by the labels of the verifier's plans: a right inverse of the dictionary D5 on cells.

Johnson/Road/HeadDict.lean fills the library's family of matrices (segment, row, column) from
matrices Z that are named by labels (D5). This file goes the other way. From a family T it makes
matrices zOf T by labels, so that D5 at zOf T is T again at every place of an even segment that a
segment of the library's model may read. Its use: matrices of an honest run of the library's model
give matrices by labels, one family for all sub-proofs, so that a bundle of hypotheses on such
matrices can be shown to be met.

How. An own label is 256 (1 + g) + n for entry n of the list of group g, and 256 * 13 + n for entry
n of the head's list. So the quotient by 256 tells the sub-proof and the remainder the number in its
list. At the sizes for which the library's model is written the list of a group is af in three
parts, ad, ar, b, qa, the stream that goes out, the stream that comes in; a table of eight lines
(slotOf) turns the number into the library's slot. A borrowed matrix bears its owner's label, so
nothing is to be said of it.

Where D5 at zOf T is not T: slot 6 of the feed-forward segment of a later group. The list's entry
there, the stream that comes in, bears the lender's label, so D5 at zOf T has the lender's entries
in that slot. The library's model has no cell there (Name.Valid in Cm/SegLayout.lean: the array x0
is an own cell of group 0 alone), and no segment reads there (plFF_six). The like holds of slot 7 of
segment 24, the head's copy of the stream; the head's cells stand in the slots 0 to 5.

Main definitions: slotOf, zOf.
Main theorems.
 - zOf_own, zOf_head, zOf_slot, zOf_qa: zOf T at an own label, at all rows and columns.
 - zOf_small: all entries of zOf T are below a bound under which all entries of T are.
 - parts_ref, slotNo_ref: the numbers in a group's list, from the verifier's layout at the library's
   sizes.
 - D5_zOf_even, D5_zOf_24: D5 at zOf T is T, slot by slot.
 - mx_xin, plFF_six: a cell of a feed-forward segment that stands in slot 6 is a cell of x0.
 - D5_zOf_ff, D5_zOf_hf, D5_zOf_hd, D5_zOf_hr, D5_zOf_name, D5_zOf: at the place of every own cell
   of an even segment, so at every place of an even segment that a segment may read.

What is compared with what: D5 and zOf, definitions of these files, at the library's places; the
numbers of the verifier's list against the library's slots.

The hypotheses: twelve groups of layers; hf in four parts; af in three parts and ad in one
(parts_ref has these two from the verifier's layout at the library's sizes); the library's shape hd
of the head holds no more than the matrices (Hd.OK).

What is not claimed. Nothing on odd segments: there D5 is its letter At. Nothing on what T holds.
The program does not import this file.
-/
import Johnson.Road.HeadDict
import Cm.SegLayoutProofs

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Inst.Model.All (DF)
open Inst.Model.FFSeg (Arr Cell addr)
open OnBytes.Model.Layer (Lay matIx)
open Cm.Seg (at' reads plFF Name InShape)

/-! ## The definition -/

/-- The library's slot of the matrix with a number in the list of a layer sub-proof, at the sizes
for which the library's model is written. Number 5, the matrix b, has no slot. -/
def slotOf : ℕ → Option ℕ
  | 0 => some 0
  | 1 => some 1
  | 2 => some 2
  | 3 => some 3
  | 4 => some 4
  | 6 => some 5
  | 8 => some 6
  | 7 => some 7
  | _ => none

/-- Matrices by labels, from a family T of the library's matrices: the entry at (label, row, column)
is the entry of T in the owner's segment, at that row of the owner's slot and at that column. No
bound is asked of row and column: from row 65,536 on the entry is one of a later slot. 0 at a label
of a layer sub-proof's matrix that has no slot. -/
def zOf (T : ℕ → ℕ → ℕ → ℤ) : ℕ → ℕ → ℕ → ℤ := fun l r c =>
  if l / 256 = 13 then T 24 (l % 256 * 65536 + r) c
  else
    match slotOf (l % 256) with
    | some t => T (2 * (l / 256 - 1)) (t * 65536 + r) c
    | none => 0

/-- At an own label of group g. -/
theorem zOf_own (T : ℕ → ℕ → ℕ → ℤ) {g n t : ℕ} (hg : g < 12) (hn : n < 256)
    (hs : slotOf n = some t) (r c : ℕ) :
    zOf T ((1 + g) * 256 + n) r c = T (2 * g) (t * 65536 + r) c := by
  have e1 : ((1 + g) * 256 + n) / 256 = 1 + g := by omega
  have e2 : ((1 + g) * 256 + n) % 256 = n := by omega
  have h13 : ¬ 1 + g = 13 := by omega
  unfold zOf
  rw [e1, e2, if_neg h13, hs]
  show T (2 * (1 + g - 1)) (t * 65536 + r) c = _
  rw [show 1 + g - 1 = g by omega]

/-- At an own label of the head. -/
theorem zOf_head (T : ℕ → ℕ → ℕ → ℤ) {m : ℕ} (hm : m < 256) (r c : ℕ) :
    zOf T (13 * 256 + m) r c = T 24 (m * 65536 + r) c := by
  have e1 : (13 * 256 + m) / 256 = 13 := by omega
  have e2 : (13 * 256 + m) % 256 = m := by omega
  unfold zOf
  rw [e1, e2, if_pos rfl]

/-- **All entries are small**, if all entries of T are. -/
theorem zOf_small {T : ℕ → ℕ → ℕ → ℤ} {B : ℤ} (hT : ∀ s r c, |T s r c| < B) (hB : 0 < B) :
    ∀ l r c, |zOf T l r c| < B := by
  intro l r c
  unfold zOf
  by_cases h13 : l / 256 = 13
  · rw [if_pos h13]
    exact hT _ _ _
  · rw [if_neg h13]
    cases hs : slotOf (l % 256) with
    | none =>
      show |(0 : ℤ)| < B
      rw [abs_zero]
      exact hB
    | some t => exact hT _ _ _

/-! ## The numbers in a group's list -/

/-- At the library's sizes the verifier's layout has af in three parts and ad in one. -/
theorem parts_ref {hy : Model.Layer.Shape} {pc : List (List String)} {y : Lay}
    (hl : Model.Layer.layout hy pc = .ok y) (S : Switches hy) (Z2 : Sized2 hy DF) :
    y.parts.getD 0 0 = 3 ∧ y.parts.getD 1 0 = 1 := by
  obtain ⟨e, -⟩ := laid_of_layout hl S.p3
  subst e
  have L := laid2_of_layout hl
  have e3 : DF.parts = 3 := rfl
  refine ⟨?_, ?_⟩
  · rw [L.parts0, ← Z2.parts, e3]
  · rw [L.parts1, Z2.NAd]

/-- With af in three parts and ad in one: the number in the list of the matrix of a slot is below
256, slotOf leads back to the slot, and the number is that of the stream that comes in for slot 6
alone. -/
theorem slotNo_ref {y : Lay} (hp0 : y.parts.getD 0 0 = 3) (hp1 : y.parts.getD 1 0 = 1) {t : ℕ}
    (ht : t < 8) :
    slotNo y t < 256 ∧ slotOf (slotNo y t) = some t ∧ (slotNo y t = (matIx y).iXI → t = 6) := by
  have hx : (matIx y).iXI = 8 := by
    show y.parts.getD 0 0 + y.parts.getD 1 0 + 4 = 8
    rw [hp0, hp1]
  have v0 : slotNo y 0 = 0 := rfl
  have v1 : slotNo y 1 = 1 := rfl
  have v2 : slotNo y 2 = 2 := rfl
  have v3 : slotNo y 3 = 3 := hp0
  have v4 : slotNo y 4 = 4 := by
    show y.parts.getD 0 0 + y.parts.getD 1 0 = 4
    rw [hp0, hp1]
  have v5 : slotNo y 5 = 6 := by
    show y.parts.getD 0 0 + y.parts.getD 1 0 + 2 = 6
    rw [hp0, hp1]
  have v6 : slotNo y 6 = 8 := hx
  have v7 : slotNo y 7 = 7 := by
    show y.parts.getD 0 0 + y.parts.getD 1 0 + 3 = 7
    rw [hp0, hp1]
  have c : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 := by omega
  rw [hx]
  rcases c with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [v0]
    exact ⟨by norm_num, rfl, fun e => absurd e (by norm_num)⟩
  · rw [v1]
    exact ⟨by norm_num, rfl, fun e => absurd e (by norm_num)⟩
  · rw [v2]
    exact ⟨by norm_num, rfl, fun e => absurd e (by norm_num)⟩
  · rw [v3]
    exact ⟨by norm_num, rfl, fun e => absurd e (by norm_num)⟩
  · rw [v4]
    exact ⟨by norm_num, rfl, fun e => absurd e (by norm_num)⟩
  · rw [v5]
    exact ⟨by norm_num, rfl, fun e => absurd e (by norm_num)⟩
  · rw [v6]
    exact ⟨by norm_num, rfl, fun _ => rfl⟩
  · rw [v7]
    exact ⟨by norm_num, rfl, fun e => absurd e (by norm_num)⟩

/-! ## D5 at zOf T is T, slot by slot -/

/-- At the label of the matrix of slot t of group g, but for slot 6 of a later group: at all rows
and columns. -/
theorem zOf_slot {y : Lay} (hp0 : y.parts.getD 0 0 = 3) (hp1 : y.parts.getD 1 0 = 1)
    (T : ℕ → ℕ → ℕ → ℤ) {g t : ℕ} (hg : g < 12) (ht : t < 8) (h6 : t = 6 → g = 0) (r c : ℕ) :
    zOf T (labA y g (slotNo y t)) r c = T (2 * g) (t * 65536 + r) c := by
  obtain ⟨a1, a2, a3⟩ := slotNo_ref hp0 hp1 ht
  have el : labA y g (slotNo y t) = (1 + g) * 256 + slotNo y t :=
    if_neg fun k => k.2 (h6 (a3 k.1))
  rw [el, zOf_own T hg a1 a2]

/-- At the label of qa of group g. -/
theorem zOf_qa {y : Lay} (hp0 : y.parts.getD 0 0 = 3) (hp1 : y.parts.getD 1 0 = 1)
    (T : ℕ → ℕ → ℕ → ℤ) {g : ℕ} (hg : g < 12) (r c : ℕ) :
    zOf T (labA y g (matIx y).iQA) r c = T (2 * g) (5 * 65536 + r) c :=
  zOf_slot hp0 hp1 T hg (t := 5) (by norm_num) (fun e => absurd e (by norm_num)) r c

/-- In the feed-forward segment of group g, in the eight slots, but for slot 6 of a later group. -/
theorem D5_zOf_even (h : Model.Head.Shape) {y : Lay} (hp0 : y.parts.getD 0 0 = 3)
    (hp1 : y.parts.getD 1 0 = 1) (At T : ℕ → ℕ → ℕ → ℤ) {g r : ℕ} (hg : g < 12)
    (hr : r < 524288) (h6 : r / 65536 = 6 → g = 0) (c : ℕ) :
    D5 h y At (zOf T) (2 * g) r c = T (2 * g) r c := by
  have ht : r / 65536 < 8 := by omega
  rw [D5_even h y At (zOf T) (s := 2 * g) (by omega) (by omega), show 2 * g / 2 = g by omega,
    zOf_slot hp0 hp1 T hg ht h6, show r / 65536 * 65536 + r % 65536 = r by omega]

/-- In the first six slots of segment 24. -/
theorem D5_zOf_24 {h : Model.Head.Shape} {y : Lay} (h12 : y.NGr = 12) (hN : h.NHf = 4)
    (At T : ℕ → ℕ → ℕ → ℤ) {r : ℕ} (hr : r / 65536 < 6) (c : ℕ) :
    D5 h y At (zOf T) 24 r c = T 24 r c := by
  have el : labH h y (r / 65536) = 13 * 256 + r / 65536 := by
    have e : labH h y (r / 65536) = (1 + y.NGr) * 256 + r / 65536 := if_neg (by omega)
    rw [e]
    omega
  have h7 : r / 65536 < 256 := by omega
  rw [D5_24, el, zOf_head T h7, show r / 65536 * 65536 + r % 65536 = r by omega]

/-! ## No cell of a later group stands in slot 6 -/

/-- The one array in the matrix of the stream that comes in is x0. -/
theorem mx_xin (X : Arr) (h : X.mx = .xin) : X = .x0 := by
  cases X <;> first | rfl | exact absurd h (by decide)

/-- A cell of a feed-forward segment that stands in slot 6 is a cell of x0. -/
theorem plFF_six {c : Cell} (hc : c.Valid DF) (h6 : (plFF c).1 / 65536 = 6) : c.X = .x0 := by
  have h7 : ((Cm.Seg.slotFF (addr DF c).1 + (addr DF c).2.2 / Cm.Seg.colsFF) * Cm.Seg.hSlot +
      (addr DF c).2.1) / 65536 = 6 := h6
  rw [Cm.Seg.colsFF_eq, Cm.Seg.hSlot_eq] at h7
  have hμ : (addr DF c).1 = c.X.mx := rfl
  have B := Cm.Seg.ff_addr c hc
  generalize addr DF c = a at h7 hμ B
  obtain ⟨μ, row, col⟩ := a
  dsimp only at h7 hμ B
  rcases B with ⟨rfl, b1, b2⟩ | ⟨rfl, b1, b2⟩ | ⟨rfl, b1, b2⟩ | ⟨rfl, b1, b2⟩ | ⟨rfl, b1, b2⟩ |
    ⟨rfl, b1, b2⟩
  · have h8 : ((0 + col / 5990) * 65536 + row) / 65536 = 6 := h7
    omega
  · have h8 : ((3 + col / 5990) * 65536 + row) / 65536 = 6 := h7
    omega
  · have h8 : ((4 + col / 5990) * 65536 + row) / 65536 = 6 := h7
    omega
  · have h8 : ((5 + col / 5990) * 65536 + row) / 65536 = 6 := h7
    omega
  · exact mx_xin _ hμ.symm
  · have h8 : ((7 + col / 5990) * 65536 + row) / 65536 = 6 := h7
    omega

/-! ## At the places of cells -/

/-- A family of matrices at a place that is written out. -/
theorem at_mk (M : ℕ → ℕ → ℕ → ℤ) (s r c : ℕ) : at' M (s, r, c) = M s r c := rfl

section Names

variable {hd : Cm.Seg.Hd} {h : Model.Head.Shape} {y : Lay}

/-- At the place of a cell of a feed-forward segment. -/
theorem D5_zOf_ff (hp0 : y.parts.getD 0 0 = 3) (hp1 : y.parts.getD 1 0 = 1)
    (At T : ℕ → ℕ → ℕ → ℤ) {g : ℕ} {c : Cell} (hg : g < 12) (hc : c.Valid DF)
    (hx : c.X = .x0 → g = 0) :
    at' (D5 h y At (zOf T)) (Name.ff g c).place = at' T (Name.ff g c).place := by
  obtain ⟨b1, -⟩ := Cm.Seg.plFF_in c hc
  show D5 h y At (zOf T) (2 * g) (plFF c).1 (plFF c).2 = T (2 * g) (plFF c).1 (plFF c).2
  exact D5_zOf_even h hp0 hp1 At T hg b1 (fun k => hx (plFF_six hc k)) _

/-- At the place of a cell of hf. -/
theorem D5_zOf_hf (h12 : y.NGr = 12) (hN : h.NHf = 4) (At T : ℕ → ℕ → ℕ → ℤ) {φ i : ℕ}
    (hφ : φ < 1232768) (hi : i < 1024) :
    at' (D5 h y At (zOf T)) (Name.hf φ i).place = at' T (Name.hf φ i).place := by
  have e10 : (2 : ℕ) ^ 10 = 1024 := by norm_num
  have hrow : ((0 + φ / 64 / 4816) * 65536 + (φ % 64 * 2 ^ 10 + i)) / 65536 < 6 := by
    rw [e10]
    omega
  rw [place_hf, at_mk, at_mk]
  exact D5_zOf_24 h12 hN At T hrow _

/-- At the place of a cell of hd. -/
theorem D5_zOf_hd (h12 : y.NGr = 12) (hN : h.NHf = 4) (At T : ℕ → ℕ → ℕ → ℤ) {φ i : ℕ}
    (hφ : φ < 10240) (hi : i < 1024) :
    at' (D5 h y At (zOf T)) (Name.hd φ i).place = at' T (Name.hd φ i).place := by
  have e10 : (2 : ℕ) ^ 10 = 1024 := by norm_num
  have hrow : ((4 + φ / 16 / 4816) * 65536 + (φ % 16 * 2 ^ 10 + i)) / 65536 < 6 := by
    rw [e10]
    omega
  rw [place_hd, at_mk, at_mk]
  exact D5_zOf_24 h12 hN At T hrow _

/-- At the place of a cell of hr. -/
theorem D5_zOf_hr (h12 : y.NGr = 12) (hN : h.NHf = 4) (At T : ℕ → ℕ → ℕ → ℤ) {φ i : ℕ}
    (hφ : φ < 120) (hi : i < 1024) :
    at' (D5 h y At (zOf T)) (Name.hr φ i).place = at' T (Name.hr φ i).place := by
  have e10 : (2 : ℕ) ^ 10 = 1024 := by norm_num
  have hrow : ((5 + φ / 8 / 4816) * 65536 + (φ % 8 * 2 ^ 10 + i)) / 65536 < 6 := by
    rw [e10]
    omega
  rw [place_hr, at_mk, at_mk]
  exact D5_zOf_24 h12 hN At T hrow _

/-- **At the place of every own cell of an even segment D5 at zOf T is T.** -/
theorem D5_zOf_name (hOK : hd.OK) (h12 : y.NGr = 12) (hN : h.NHf = 4)
    (hp0 : y.parts.getD 0 0 = 3) (hp1 : y.parts.getD 1 0 = 1) (At T : ℕ → ℕ → ℕ → ℤ) (n : Name)
    (hn : n.Valid hd) (h2 : n.place.1 % 2 = 0) :
    at' (D5 h y At (zOf T)) n.place = at' T n.place := by
  obtain ⟨ok1, ok2⟩ := hOK
  rw [Cm.Seg.nFeat_hf] at ok1
  rw [Cm.Seg.nFeat_hr] at ok2
  cases n with
  | ff g c =>
    obtain ⟨hg, hc, hx⟩ := hn
    rw [Cm.Seg.nGr_eq] at hg
    exact D5_zOf_ff hp0 hp1 At T hg hc hx
  | att g c =>
    have k : (2 * g + 1) % 2 = 0 := h2
    omega
  | hf φ i =>
    obtain ⟨hφ, hi⟩ := hn
    rw [Cm.Seg.nT_eq] at hi
    exact D5_zOf_hf h12 hN At T (Nat.lt_of_lt_of_le hφ ok1) hi
  | hd φ i =>
    obtain ⟨hφ, hi⟩ := hn
    rw [Cm.Seg.nFeat_hd] at hφ
    rw [Cm.Seg.nT_eq] at hi
    exact D5_zOf_hd h12 hN At T hφ hi
  | hr φ i =>
    obtain ⟨hφ, hi⟩ := hn
    rw [Cm.Seg.nT_eq] at hi
    exact D5_zOf_hr h12 hN At T (Nat.lt_of_lt_of_le hφ ok2) hi

/-- **A right inverse of D5 on cells.** At every place q of an even segment that a segment k of the
library's model may read, D5 at zOf T is T. -/
theorem D5_zOf (hOK : hd.OK) (h12 : y.NGr = 12) (hN : h.NHf = 4) (hp0 : y.parts.getD 0 0 = 3)
    (hp1 : y.parts.getD 1 0 = 1) (At T : ℕ → ℕ → ℕ → ℤ) :
    ∀ k < Cm.Seg.nSeg, ∀ q ∈ reads hd k, q.1 % 2 = 0 →
      at' (D5 h y At (zOf T)) q = at' T q := by
  intro k _ q hq h2
  rcases hq with ⟨g, c, _, hg, hc, rfl⟩ | ⟨g, c, _, hg, hc, rfl⟩ |
    ⟨_, ⟨n, hn, _, rfl⟩ | ⟨φ, i, hφ, hi, rfl⟩⟩
  · exact D5_zOf_name hOK h12 hN hp0 hp1 At T _ ((Cm.lay_own_valid hd).1 g hg c hc) h2
  · exact D5_zOf_name hOK h12 hN hp0 hp1 At T _ ((Cm.lay_own_valid hd).2.1 g hg c hc) h2
  · exact D5_zOf_name hOK h12 hN hp0 hp1 At T n hn h2
  · exact D5_zOf_name hOK h12 hN hp0 hp1 At T _ ((Cm.lay_own_valid hd).2.2 φ hφ i hi) h2

end Names

#print axioms zOf_small
#print axioms zOf_slot
#print axioms zOf_qa
#print axioms parts_ref
#print axioms slotNo_ref
#print axioms D5_zOf_even
#print axioms D5_zOf_24
#print axioms plFF_six
#print axioms D5_zOf_ff
#print axioms D5_zOf_hf
#print axioms D5_zOf_hd
#print axioms D5_zOf_hr
#print axioms D5_zOf_name
#print axioms D5_zOf

end OnBytes.Road.Hd
