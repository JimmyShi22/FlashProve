-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/PortRow.lean: kind K5: the readers on "ah" are the library-side
reading forms (Cb/Pv/Att/End/Tabs.lean: rdRow), for the written forms, at any values of the late
entries. Twins of shV_ent, overG_ent, limbs_ent, limbs_row, readMaximum_row, readDenominator_row and
readIndexBit_row (Johnson/Road/Rows/AttEntRow.lean), which speak of a run of a routine in a context
("if the routine returns"). No table is taken to be true: what ties the two sides is the dictionary
LateAt W h K3 Y tabOf place u (Johnson/Road/Rows/AttEntRow.lean): the late entry named (T, r) is
entry number tabOf T + place T r of the vector of tables. The proofs' pure parts follow those proofs
line for line.

Main names:
  `shVF_ent`, `overGF_ent`, `limbsF_ent`: the written forms on entries of the vector
    (Johnson/Desc/First/Att/Claims/Worth.lean, the weights read as eqN and powers of 256).
  `limbsF_row`, `readMaximumF_row`, `readDenominatorF_row`, `readIndexBitF_row`: ‹written
    form›.value ρ W = (rdRow …).val (Sum.elim m u).
Used of OnBytes, Johnson/Road and Cb: plain records, pure functions and lemmas on them alone; no
routine in a context and no theorem on a run: AttPub, LateAt, placeRow, rdW, pt, eqTab_value,
getD_extract, rowLimb_value, shapedG_of_hid, pair_parts; the library's LateLay, AttTab, rdRow,
rdRow_at.
Not claimed: that the dictionary holds of a message.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Road.Rows.AttEntRow
import Johnson.Desc.First.Att.Claims.MeanRd

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open Finset
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open OnBytes.Road.Hd (rdW)
open Inst.Model.AttSeg (Raw)
open Cb.Pv.Att.End (LateLay AttTab rdRow rdRow_at)

variable {Kf : Type} [Field Kf]

section Ent
variable {ρ : Reading Kf} (W : World Kf) {K3 : ℕ} {h : Attention.Heard} {lid : ℕ} {cf : Attention.Cfg}
  {fs : Model.Forest.Shape}

theorem shVF_ent (N : Numerals ρ) {t off nl J lam j : ℕ} :
    (Fo.shVF h K3 t off nl J lam j).value ρ W = ∑ l ∈ range nl, 256 ^ l *
      rdW W h.iU3 K3 (t + (off + (l * h.S.Lam + lam) * J + j)) := by
  rw [shVF_value, list_sum_range]
  refine sum_congr rfl fun l hl => ?_
  rw [rowLimb_value N (mem_range.mp hl)]
  rfl

theorem overGF_ent (A : AttPub ρ h lid cf fs) {zg : Array E} (hz : h.S.cf.lgk ≤ zg.size) (fv : ℕ → Aff) :
    (Fo.overGF h zg fv).value ρ W =
      ∑ g ∈ range (2 ^ h.S.cf.lgk), Blocks.eqN h.S.cf.lgk 0 (pt ρ zg) g * (fv g).value ρ W := by
  have hG := (shapedG_of_hid A.shape).G
  have hs : (zg.extract 0 h.S.cf.lgk).size = h.S.cf.lgk := by
    rw [Array.size_extract]
    omega
  rw [overGF_value, list_sum_range, hG]
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

theorem limbsF_ent (A : AttPub ρ h lid cf fs) {t : ℕ} {zg : Array E} (hz : h.S.cf.lgk ≤ zg.size)
    {off nl J lam : ℕ} (jOf : ℕ → ℕ) :
    (Fo.overGF h zg fun g => Fo.shVF h K3 t off nl J lam (jOf g)).value ρ W =
      ∑ g ∈ range (2 ^ h.S.cf.lgk), Blocks.eqN h.S.cf.lgk 0 (pt ρ zg) g *
        ∑ l ∈ range nl, 256 ^ l *
          rdW W h.iU3 K3 (t + (off + (l * h.S.Lam + lam) * J + jOf g)) := by
  rw [overGF_ent W A hz]
  exact sum_congr rfl fun g _ => by rw [shVF_ent W A.num]

end Ent

section Row
variable {ρ : Reading Kf} {W : World Kf} {K3 : ℕ} {h : Attention.Heard} {lid : ℕ} {cf : Attention.Cfg}
  {fs : Model.Forest.Shape} {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂] [DecidableEq J₁]
  [DecidableEq J₂] {Y : LateLay AttTab J₂} {tabOf : AttTab → ℕ} {place : AttTab → Raw → ℕ}
  {u : J₂ → Kf} (m : J₁ → Kf) {zg : Array E} {lam a : ℕ}

/-- A written form on ah in nl limbs is worth what rdRow is worth. base: the names of the limbs. -/
theorem limbsF_row (A : AttPub ρ h lid cf fs)
    (L : LateAt W h K3 Y tabOf place u) (T : AttTab) (hz : h.S.cf.lgk ≤ zg.size)
    {off nl J : ℕ} (jOf : ℕ → ℕ) (base : ℕ → ℕ → Raw)
    (hg : ∀ g < 2 ^ h.S.cf.lgk, ∀ l < nl, Y.good (T, base l g))
    (hp : ∀ g, ∀ l < nl, place T (base l g) = off + (l * h.S.Lam + lam) * J + jOf g) :
    (Fo.overGF h zg fun g => Fo.shVF h K3 (tabOf T) off nl J lam (jOf g)).value ρ W =
      (rdRow (J₁ := J₁) (L5.dimOf h.S) Y T (pt ρ zg) nl base).val (Sum.elim m u) := by
  rw [limbsF_ent W A hz jOf, rdRow_at]
  refine sum_congr rfl fun g hg' => ?_
  congr 1
  refine sum_congr rfl fun l hl => ?_
  show _ = _ * u (Y.at' (T, base l g))
  rw [L T _ (hg g (mem_range.mp hg') l (mem_range.mp hl)), hp g l (mem_range.mp hl)]

/-- The row maximum. -/
theorem readMaximumF_row (A : AttPub ρ h lid cf fs)
    (L : LateAt W h K3 Y tabOf place u) (T : AttTab) (hT : place T = placeRow h.S)
    (hz : h.S.cf.lgk ≤ zg.size) (ha : a < h.S.HA)
    (hg : ∀ g < 2 ^ h.S.cf.lgk, ∀ l < 4, Y.good (T, .mx l (lam * h.S.HA + a) g 0)) :
    (Fo.readMaximumF h K3 (tabOf T) zg lam a).value ρ W = (rdRow (J₁ := J₁) (L5.dimOf h.S) Y T (pt ρ zg) 4
      fun k g => .mx k (lam * h.S.HA + a) g 0).val (Sum.elim m u) := by
  have hb := pair_parts (lam := lam) ha
  refine limbsF_row m A L T hz (fun g => g * h.S.HA + a) _ hg (fun g l _ => ?_)
  rw [hT]
  show h.S.oMr + (l * h.S.Lam + (lam * h.S.HA + a) / h.S.HA) * h.S.cf.H +
    (g * h.S.HA + (lam * h.S.HA + a) % h.S.HA) = _
  rw [hb.1, hb.2]

/-- The denominator. -/
theorem readDenominatorF_row (A : AttPub ρ h lid cf fs)
    (L : LateAt W h K3 Y tabOf place u) (T : AttTab) (hT : place T = placeRow h.S)
    (hz : h.S.cf.lgk ≤ zg.size) (ha : a < h.S.HA)
    (hg : ∀ g < 2 ^ h.S.cf.lgk, ∀ l < 4, Y.good (T, .den l (lam * h.S.HA + a) g 0)) :
    (Fo.readDenominatorF h K3 (tabOf T) zg lam a).value ρ W =
      (rdRow (J₁ := J₁) (L5.dimOf h.S) Y T (pt ρ zg) 4
        fun k g => .den k (lam * h.S.HA + a) g 0).val (Sum.elim m u) := by
  have hb := pair_parts (lam := lam) ha
  refine limbsF_row m A L T hz (fun g => g * h.S.HA + a) _ hg (fun g l _ => ?_)
  rw [hT]
  show h.S.oZr + (l * h.S.Lam + (lam * h.S.HA + a) / h.S.HA) * h.S.cf.H +
    (g * h.S.HA + (lam * h.S.HA + a) % h.S.HA) = _
  rw [hb.1, hb.2]

/-- A bit of the index. -/
theorem readIndexBitF_row (A : AttPub ρ h lid cf fs)
    (L : LateAt W h K3 Y tabOf place u) (T : AttTab) (hT : place T = placeRow h.S)
    (hz : h.S.cf.lgk ≤ zg.size) (ha : a < h.S.HA) {k : ℕ}
    (hg : ∀ g < 2 ^ h.S.cf.lgk, Y.good (T, .ib k (lam * h.S.HA + a) g 0)) :
    (Fo.readIndexBitF h K3 (tabOf T) zg lam a k).value ρ W =
      (rdRow (J₁ := J₁) (L5.dimOf h.S) Y T (pt ρ zg) 1
        fun _ g => .ib k (lam * h.S.HA + a) g 0).val (Sum.elim m u) := by
  have hb := pair_parts (lam := lam) ha
  refine limbsF_row m A L T hz (fun g => k * h.S.cf.H + g * h.S.HA + a) _
    (fun g hg' _ _ => hg g hg') (fun g l hl => ?_)
  have hl0 : l = 0 := by omega
  rw [hT, hl0]
  show h.S.oIb + (0 * h.S.Lam + (lam * h.S.HA + a) / h.S.HA) * (h.S.cf.lt * h.S.cf.H) +
    (k * h.S.cf.H + g * h.S.HA + (lam * h.S.HA + a) % h.S.HA) = _
  rw [hb.1, hb.2]

end Row

end K5Law
