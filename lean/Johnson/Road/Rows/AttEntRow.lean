-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttEntRow.lean: the verifier's forms on the matrix ah of the attention sub-proof,
on the entries of the vector of tables as they were sent; they are the library-side reading forms.

Johnson/Road/Rows/AttReadRow.lean says what readMaximum, readDenominator and readIndexBit are worth
in a world in which every table is true of the matrices. This file stops one step earlier. In any
world the form that such a function returns is a public combination of entries of the vector of
tables. The reading form rdRow of Cb/Pv/Att/End/Tabs.lean is a public combination of late entries,
which have names. If the late entry of each name is the entry of the vector at the name's place, the
two are worth the same.

Main definitions.
 - AttPub: what is asked of the setting: the reading takes numerals to numbers; the shape is what
   the verifier's function returns. Nothing on tables.
 - placeRow S r: the place, within a table on ah, of the entry whose first cell has the name r.
 - LateAt W h K3 Y tabOf place u: the dictionary: the late entry named (T, r) is entry number
   tabOf T + place T r of the vector of tables.
Main theorems.
 - shV_ent, overG_ent: a number in limbs; the sum over the heads of keys and values. limbs_ent: a
   form on ah in limbs, on entries of the vector.
 - readMaximum_row, readDenominator_row, readIndexBit_row: under the dictionary they are worth what
   rdRow is worth, at the early entries m and the late entries u, whatever these are.

What is not claimed. That the dictionary holds of the programs' message: LateAt is a premise. Every
theorem on a form begins "if the routine returns". Nothing is said about probabilities or about
hiding. The program does not import this file.


-/
import Johnson.Road.Rows.AttReadRow
import Cb.Pv.Att.End.At
import Cb.Pv.Att.End.First

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open Finset
open OnBytes.Model (Reading World Aff Fork SubM eqTab)
open OnBytes.Attention (Heard)
open OnBytes.Road.Hd (Ok colsOf rdW)
open Inst.Model.AttSeg (Raw)
open Cb.Pv.Att.End (LateLay AttTab rdRow rdRow_at)

variable {K : Type} [Field K]

/-- What is asked of the setting. Nothing on tables. -/
structure AttPub (ρ : Reading K) (h : Heard) (lid : ℕ) (cf : Attention.Cfg)
    (fs : Model.Forest.Shape) : Prop where
  /-- the reading takes numerals to numbers -/
  num : Numerals ρ
  /-- the shape is what the verifier's function returns -/
  shape : Attention.shapeHid lid cf = .ok (h.S, fs)

/-- The setting of a claim gives it. -/
theorem AttAt.pub {ρ : Reading K} {W : World K} {tl : Model.HTailF2} {K3 : ℕ} {M : Mats K}
    {h : Heard} {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}
    (A : AttAt ρ W tl K3 M h lid cf fs) : AttPub ρ h lid cf fs := ⟨A.num, A.shape⟩

/-! ## The forms on entries of the vector of tables -/

section Ent
variable {ρ : Reading K} (W : World K) {K3 : ℕ} {h : Heard} {lid : ℕ} {cf : Attention.Cfg}
  {fs : Model.Forest.Shape}

/-- A number in nl limbs, on the entries of the table that begins at t. -/
theorem shV_ent (N : Numerals ρ) {F : Fork} (hc : Cols F h K3) {t off nl J lam j : ℕ} {C : Ctx}
    {q : Aff} {G : Fork} {D : Ctx} (hh : Ok (Attention.shV h t off nl J lam j) F C q G D) :
    G = F ∧ D = C ∧ q.value ρ W = ∑ l ∈ range nl, 256 ^ l *
      rdW W h.iU3 K3 (t + (off + (l * h.S.Lam + lam) * J + j)) := by
  obtain ⟨e1, e2, -, e4⟩ := weighted_value ρ W nl (Attention.limbWeights nl)
    (fun l => Attention.u3at h t (off + (l * h.S.Lam + lam) * J + j))
    (fun l => rdW W h.iU3 K3 (t + (off + (l * h.S.Lam + lam) * J + j)))
    (fun _ => True)
    (by
      intro l _ x G1 D1 hx
      obtain ⟨a1, a2, -, a4⟩ := u3at_value ρ W hx
      refine ⟨a1, a2, trivial, ?_⟩
      have hc' : colsOf F h.iU3 = K3 := hc
      rw [a4, hc'])
    hh
  refine ⟨e1, e2, ?_⟩
  rw [e4]
  exact sum_congr rfl fun l hl => by rw [rowLimb_value N (mem_range.mp hl)]

/-- The sum over the heads of keys and values. -/
theorem overG_ent (A : AttPub ρ h lid cf fs) {F : Fork} {C : Ctx} {zg : Array E}
    (hz : h.S.cf.lgk ≤ zg.size) (f : ℕ → SubM Aff) (v : ℕ → K)
    (hf : ∀ g < h.S.G, ∀ x G D, Ok (f g) F C x G D → G = F ∧ D = C ∧ x.value ρ W = v g)
    {q : Aff} {G : Fork} {D : Ctx} (hh : Ok (Attention.overG h zg f) F C q G D) :
    G = F ∧ D = C ∧
      q.value ρ W =
        ∑ g ∈ range (2 ^ h.S.cf.lgk), Blocks.eqN h.S.cf.lgk 0 (pt ρ zg) g * v g := by
  have hG := (shapedG_of_hid A.shape).G
  obtain ⟨e1, e2, -, e4⟩ := weighted_value ρ W h.S.G (eqTab (zg.extract 0 h.S.cf.lgk)) f v
    (fun _ => True)
    (fun g hg x G1 D1 hx => by
      obtain ⟨a1, a2, a3⟩ := hf g hg x G1 D1 hx
      exact ⟨a1, a2, trivial, a3⟩)
    hh
  refine ⟨e1, e2, ?_⟩
  have hs : (zg.extract 0 h.S.cf.lgk).size = h.S.cf.lgk := by
    rw [Array.size_extract]
    omega
  rw [e4, hG]
  refine sum_congr rfl fun g hg => ?_
  have hg' : g < 2 ^ (zg.extract 0 h.S.cf.lgk).size := by rw [hs]; exact mem_range.mp hg
  rw [eqTab_value ρ _ g hg', hs]
  congr 1
  unfold Blocks.eqN
  refine prod_congr rfl fun k hk => ?_
  have hk' : k < h.S.cf.lgk := mem_range.mp hk
  have e : pt ρ (zg.extract 0 h.S.cf.lgk) (0 + k) = pt ρ zg (0 + k) := by
    unfold pt
    rw [Nat.zero_add, getD_extract zg hz (by omega), Nat.zero_add]
  rw [e]

/-- A form on ah, summed over the heads of keys and values, on entries of the vector. -/
theorem limbs_ent (A : AttPub ρ h lid cf fs) {F : Fork} (hc : Cols F h K3) {t : ℕ}
    {zg : Array E} (hz : h.S.cf.lgk ≤ zg.size) {off nl J lam : ℕ} (jOf : ℕ → ℕ) {C : Ctx}
    {q : Aff} {G : Fork} {D : Ctx}
    (hh : Ok (Attention.overG h zg fun g => Attention.shV h t off nl J lam (jOf g)) F C q G D) :
    G = F ∧ D = C ∧ q.value ρ W =
      ∑ g ∈ range (2 ^ h.S.cf.lgk), Blocks.eqN h.S.cf.lgk 0 (pt ρ zg) g *
        ∑ l ∈ range nl, 256 ^ l *
          rdW W h.iU3 K3 (t + (off + (l * h.S.Lam + lam) * J + jOf g)) :=
  overG_ent W A hz _ _ (fun _ _ _ _ _ hx => shV_ent W A.num hc hx) hh

end Ent

/-! ## Places and names -/

/-- The place, within a table on ah, of the entry whose first cell has the name r. -/
def placeRow (S : Attention.Shape) : Raw → ℕ
  | .mx k b g _ => S.oMr + (k * S.Lam + b / S.HA) * S.cf.H + (g * S.HA + b % S.HA)
  | .den k b g _ => S.oZr + (k * S.Lam + b / S.HA) * S.cf.H + (g * S.HA + b % S.HA)
  | .ib k b g _ =>
    S.oIb + (0 * S.Lam + b / S.HA) * (S.cf.lt * S.cf.H) + (k * S.cf.H + g * S.HA + b % S.HA)
  | _ => 0

/-- The dictionary: the late entry named (T, r) is entry number tabOf T + place T r of the vector of
tables. -/
def LateAt {J₂ : Type} (W : World K) (h : Heard) (K3 : ℕ) (Y : LateLay AttTab J₂)
    (tabOf : AttTab → ℕ) (place : AttTab → Raw → ℕ) (u : J₂ → K) : Prop :=
  ∀ T r, Y.good (T, r) → u (Y.at' (T, r)) = rdW W h.iU3 K3 (tabOf T + place T r)

/-! ## The verifier's forms are the reading forms -/

section Row
variable {ρ : Reading K} {W : World K} {K3 : ℕ} {h : Heard} {lid : ℕ} {cf : Attention.Cfg}
  {fs : Model.Forest.Shape} {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂] [DecidableEq J₁]
  [DecidableEq J₂] {Y : LateLay AttTab J₂} {tabOf : AttTab → ℕ} {place : AttTab → Raw → ℕ}
  {u : J₂ → K} (m : J₁ → K) {F : Fork} {zg : Array E} {lam a : ℕ} {C : Ctx} {q : Aff} {G : Fork}
  {D : Ctx}

/-- A form on ah in nl limbs is worth what rdRow is worth. base: the names of the limbs. -/
theorem limbs_row (A : AttPub ρ h lid cf fs) (hc : Cols F h K3)
    (L : LateAt W h K3 Y tabOf place u) (T : AttTab) (hz : h.S.cf.lgk ≤ zg.size)
    {off nl J : ℕ} (jOf : ℕ → ℕ) (base : ℕ → ℕ → Raw)
    (hg : ∀ g < 2 ^ h.S.cf.lgk, ∀ l < nl, Y.good (T, base l g))
    (hp : ∀ g, ∀ l < nl, place T (base l g) = off + (l * h.S.Lam + lam) * J + jOf g)
    (hh : Ok (Attention.overG h zg fun g => Attention.shV h (tabOf T) off nl J lam (jOf g))
      F C q G D) :
    q.value ρ W = (rdRow (J₁ := J₁) (L5.dimOf h.S) Y T (pt ρ zg) nl base).val (Sum.elim m u) := by
  obtain ⟨-, -, e⟩ := limbs_ent W A hc hz jOf hh
  rw [e, rdRow_at]
  refine sum_congr rfl fun g hg' => ?_
  congr 1
  refine sum_congr rfl fun l hl => ?_
  show _ = _ * u (Y.at' (T, base l g))
  rw [L T _ (hg g (mem_range.mp hg') l (mem_range.mp hl)), hp g l (mem_range.mp hl)]

/-- The row maximum. -/
theorem readMaximum_row (A : AttPub ρ h lid cf fs) (hc : Cols F h K3)
    (L : LateAt W h K3 Y tabOf place u) (T : AttTab) (hT : place T = placeRow h.S)
    (hz : h.S.cf.lgk ≤ zg.size) (ha : a < h.S.HA)
    (hg : ∀ g < 2 ^ h.S.cf.lgk, ∀ l < 4, Y.good (T, .mx l (lam * h.S.HA + a) g 0))
    (hh : Ok (Attention.readMaximum h (tabOf T) zg lam a) F C q G D) :
    q.value ρ W = (rdRow (J₁ := J₁) (L5.dimOf h.S) Y T (pt ρ zg) 4
      fun k g => .mx k (lam * h.S.HA + a) g 0).val (Sum.elim m u) := by
  have hb := pair_parts (lam := lam) ha
  refine limbs_row m A hc L T hz (fun g => g * h.S.HA + a) _ hg (fun g l _ => ?_) hh
  rw [hT]
  show h.S.oMr + (l * h.S.Lam + (lam * h.S.HA + a) / h.S.HA) * h.S.cf.H +
    (g * h.S.HA + (lam * h.S.HA + a) % h.S.HA) = _
  rw [hb.1, hb.2]

/-- The denominator. -/
theorem readDenominator_row (A : AttPub ρ h lid cf fs) (hc : Cols F h K3)
    (L : LateAt W h K3 Y tabOf place u) (T : AttTab) (hT : place T = placeRow h.S)
    (hz : h.S.cf.lgk ≤ zg.size) (ha : a < h.S.HA)
    (hg : ∀ g < 2 ^ h.S.cf.lgk, ∀ l < 4, Y.good (T, .den l (lam * h.S.HA + a) g 0))
    (hh : Ok (Attention.readDenominator h (tabOf T) zg lam a) F C q G D) :
    q.value ρ W = (rdRow (J₁ := J₁) (L5.dimOf h.S) Y T (pt ρ zg) 4
      fun k g => .den k (lam * h.S.HA + a) g 0).val (Sum.elim m u) := by
  have hb := pair_parts (lam := lam) ha
  refine limbs_row m A hc L T hz (fun g => g * h.S.HA + a) _ hg (fun g l _ => ?_) hh
  rw [hT]
  show h.S.oZr + (l * h.S.Lam + (lam * h.S.HA + a) / h.S.HA) * h.S.cf.H +
    (g * h.S.HA + (lam * h.S.HA + a) % h.S.HA) = _
  rw [hb.1, hb.2]

/-- A bit of the index. -/
theorem readIndexBit_row (A : AttPub ρ h lid cf fs) (hc : Cols F h K3)
    (L : LateAt W h K3 Y tabOf place u) (T : AttTab) (hT : place T = placeRow h.S)
    (hz : h.S.cf.lgk ≤ zg.size) (ha : a < h.S.HA) {k : ℕ}
    (hg : ∀ g < 2 ^ h.S.cf.lgk, Y.good (T, .ib k (lam * h.S.HA + a) g 0))
    (hh : Ok (Attention.readIndexBit h (tabOf T) zg lam a k) F C q G D) :
    q.value ρ W = (rdRow (J₁ := J₁) (L5.dimOf h.S) Y T (pt ρ zg) 1
      fun _ g => .ib k (lam * h.S.HA + a) g 0).val (Sum.elim m u) := by
  have hb := pair_parts (lam := lam) ha
  refine limbs_row m A hc L T hz (fun g => k * h.S.cf.H + g * h.S.HA + a) _
    (fun g hg' _ _ => hg g hg') (fun g l hl => ?_) hh
  have hl0 : l = 0 := by omega
  rw [hT, hl0]
  show h.S.oIb + (0 * h.S.Lam + (lam * h.S.HA + a) / h.S.HA) * (h.S.cf.lt * h.S.cf.H) +
    (k * h.S.cf.H + g * h.S.HA + (lam * h.S.HA + a) % h.S.HA) = _
  rw [hb.1, hb.2]

end Row

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.readMaximum_row
#print axioms OnBytes.Road.Rows.readDenominator_row
#print axioms OnBytes.Road.Rows.readIndexBit_row
