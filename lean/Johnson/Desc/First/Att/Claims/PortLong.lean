-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/PortLong.lean: kind K5: the readers on tensors and on planes are the
library-side reading forms (Cb/Pv/Att/End/Tabs.lean: rdLong, rdCol), for the written forms, at any
values of the late entries. Twins of xl_ent, head_ent, plane_ent, head_long and plane_col
(Johnson/Road/Rows/AttEntLong.lean), which speak of a run of a routine in a context ("if the routine
returns"). No table is taken to be true; the tie is the dictionary LateAt. The proofs' pure parts
follow those proofs line for line.

Main names:
  `xlT_ent`, `headF_ent`, `planeF_ent`: the written forms on entries of the vector
    (Johnson/Desc/First/Att/Claims/Worth.lean).
  `headF_long`, `planeF_col`: ‹written form›.value ρ W = (rdLong or rdCol …).val (Sum.elim m u).
One premise more than in Johnson/Road/Rows, which takes it from the run's return: the heads'
features are lawful (headFeat … = .ok). No bound on the indices is wanted here: nothing is said of
what an entry means.
Used: as Johnson/Desc/First/Att/Claims/PortRow.lean, and hiOf, hiOf_size, hiOf_value, limb_value,
Rows.planeFirst, sizeCut, ptCut, eqTab_at, OnBytes.Road.eqTab_size, Sizes, sizes_of_hid; the
library's rdLong, rdLong_at, rdCol, rdCol_at, Raw.addN, Raw.addX.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Road.Rows.AttEntLong
import Johnson.Desc.First.Att.Claims.PortRow

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open Finset
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open OnBytes.Road.Hd (rdW)
open Inst.Model.AttSeg (Raw Reg)
open Cb.Pv.Att.End (LateLay AttTab rdLong rdLong_at rdCol rdCol_at)

variable {Kf : Type} [Field Kf]

section Ent
variable {ρ : Reading Kf} (W : World Kf) {K3 : ℕ} {h : Attention.Heard} {lid : ℕ} {cf : Attention.Cfg}
  {fs : Model.Forest.Shape}

/-- The written form of xl, on the entries of the table that begins at t. -/
theorem xlT_ent (N : Numerals ρ) {t : ℕ} {X : TenAt} {lam hd : ℕ} {zc : Array E}
    (hcut : h.S.ls ≤ (zc.extract 0 h.S.cf.ldh).size) (hfeat : headFeat X hd h.S.dh = .ok (hd * h.S.dh)) :
    (Fo.xlT h K3 t X lam hd zc).value ρ W =
      ∑ ch ∈ range (hiOf h.S zc).size, ρ.val ((hiOf h.S zc).getD ch zeroE) *
        ∑ l ∈ range X.nl, (256 : Kf) ^ l *
          rdW W h.iU3 K3 (t + (tenCell X l lam (hd * h.S.dh) / 2 ^ h.S.ls + ch)) := by
  have hc : cutLast (zc.extract 0 h.S.cf.ldh) h.S.ls =
      .ok ((zc.extract 0 h.S.cf.ldh).extract 0 ((zc.extract 0 h.S.cf.ldh).size - h.S.ls),
        (zc.extract 0 h.S.cf.ldh).extract ((zc.extract 0 h.S.cf.ldh).size - h.S.ls)
          (zc.extract 0 h.S.cf.ldh).size) := by
    unfold cutLast
    rw [if_neg (by omega)]
  rw [xlT_value ρ W h K3 t X lam hd zc _ _ hc hfeat, list_sum_range]
  refine sum_congr rfl fun ch _ => ?_
  congr 1
  rw [list_sum_range]
  refine sum_congr rfl fun l hl => ?_
  rw [limb_value N (mem_range.mp hl)]
  rfl

/-- A tensor, summed over the heads of keys and values, on entries of the vector. -/
theorem headF_ent (A : AttPub ρ h lid cf fs) {t : ℕ} {X : TenAt} {zg zc : Array E} {lam : ℕ}
    (hdOf : ℕ → ℕ) (hzg : h.S.cf.lgk ≤ zg.size) (hzc : zc.size = h.S.cf.ldh)
    (hfeat : ∀ g < 2 ^ h.S.cf.lgk, headFeat X (hdOf g) h.S.dh = .ok (hdOf g * h.S.dh)) :
    (Fo.overGF h zg fun g => Fo.xlT h K3 t X lam (hdOf g) zc).value ρ W =
      ∑ g ∈ range (2 ^ h.S.cf.lgk), Blocks.eqN h.S.cf.lgk 0 (pt ρ zg) g *
        ∑ ch ∈ range (2 ^ (h.S.cf.ldh - h.S.ls)),
          Blocks.eqN (h.S.cf.ldh - h.S.ls) 0 (pt ρ zc) ch *
            ∑ l ∈ range X.nl, (256 : Kf) ^ l *
              rdW W h.iU3 K3 (t + (tenCell X l lam (hdOf g * h.S.dh) / 2 ^ h.S.ls + ch)) := by
  have Z := sizes_of_hid A.shape
  have hcut : h.S.ls ≤ (zc.extract 0 h.S.cf.ldh).size := by
    rw [Array.size_extract]
    have := Z.ls
    omega
  rw [overGF_ent W A hzg]
  refine sum_congr rfl fun g hg => ?_
  congr 1
  rw [xlT_ent W A.num hcut (hfeat g (mem_range.mp hg)), hiOf_size h.S hzc]
  exact sum_congr rfl fun ch hch => by rw [hiOf_value ρ h.S hzc (mem_range.mp hch)]

/-- The written form of plane, on the entries of the table that begins at t. -/
theorem planeF_ent {t x lam a : ℕ} {z : Array E} {isD : Bool} :
    (Fo.planeF h K3 t x lam a z isD).value ρ W =
      ∑ hi ∈ range
          (eqTab (z.extract 0 ((if isD then h.S.nD else h.S.nM) - h.S.cf.lmS))).size,
        ρ.val ((eqTab (z.extract 0 ((if isD then h.S.nD else h.S.nM) - h.S.cf.lmS))).getD hi
          zeroE) *
          rdW W h.iU3 K3 (t + (Rows.planeFirst h.S x lam a isD >>> h.S.cf.lmS + hi)) := by
  rw [planeF_value, list_sum_range]
  rfl

end Ent

section Forms
variable {ρ : Reading Kf} {W : World Kf} {K3 : ℕ} {h : Attention.Heard} {lid : ℕ} {cf : Attention.Cfg}
  {fs : Model.Forest.Shape} {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂] [DecidableEq J₁]
  [DecidableEq J₂] {Y : LateLay AttTab J₂} {tabOf : AttTab → ℕ} {place : AttTab → Raw → ℕ}
  {u : J₂ → Kf} (m : J₁ → Kf)

/-- A tensor, summed over the heads of keys and values, is worth what rdLong is worth. base: the names of the limbs' first cells. -/
theorem headF_long (A : AttPub ρ h lid cf fs)
    (L : LateAt W h K3 Y tabOf place u) (T : AttTab) {X : TenAt} {zg zc : Array E} {lam : ℕ}
    (hdOf : ℕ → ℕ) (hzg : h.S.cf.lgk ≤ zg.size) (hzc : zc.size = h.S.cf.ldh)
    (base : ℕ → ℕ → Raw)
    (hg : ∀ g < 2 ^ h.S.cf.lgk, ∀ ch < 2 ^ (h.S.cf.ldh - h.S.ls), ∀ l < X.nl,
      Y.good (T, (base l g).addN (ch * 2 ^ h.S.ls)))
    (hp : ∀ g ch, ∀ l < X.nl, place T ((base l g).addN (ch * 2 ^ h.S.ls)) =
      tenCell X l lam (hdOf g * h.S.dh) / 2 ^ h.S.ls + ch)
    (hfeat : ∀ g < 2 ^ h.S.cf.lgk, headFeat X (hdOf g) h.S.dh = .ok (hdOf g * h.S.dh)) :
    (Fo.overGF h zg fun g => Fo.xlT h K3 (tabOf T) X lam (hdOf g) zc).value ρ W =
      (rdLong (J₁ := J₁) (L5.dimOf h.S) h.S.ls Y T (pt ρ zg) (pt ρ zc) X.nl base).val
        (Sum.elim m u) := by
  rw [headF_ent W A hdOf hzg hzc hfeat, rdLong_at]
  refine sum_congr rfl fun g hg' => ?_
  congr 1
  refine sum_congr rfl fun ch hch => ?_
  congr 1
  refine sum_congr rfl fun l hl => ?_
  show _ = _ * u (Y.at' (T, (base l g).addN (ch * 2 ^ h.S.ls)))
  rw [L T _ (hg g (mem_range.mp hg') ch (mem_range.mp hch) l (mem_range.mp hl)),
    hp g ch l (mem_range.mp hl)]

/-- A plane is worth what rdCol is worth. nb: the number of bits of a place of the region; r: the name of the plane's first cell. -/
theorem planeF_col (L : LateAt W h K3 Y tabOf place u) (T : AttTab)
    {x lam a : ℕ} {z : Array E} {isD : Bool} {nb : ℕ}
    (hnb : (if isD then h.S.nD else h.S.nM) = nb) (hz : z.size = nb) (r : Raw)
    (hg : ∀ hi < 2 ^ (nb - h.S.cf.lmS), Y.good (T, r.addX (hi * 2 ^ h.S.cf.lmS)))
    (hp : ∀ hi, place T (r.addX (hi * 2 ^ h.S.cf.lmS)) =
      Rows.planeFirst h.S x lam a isD >>> h.S.cf.lmS + hi) :
    (Fo.planeF h K3 (tabOf T) x lam a z isD).value ρ W =
      (rdCol (J₁ := J₁) h.S.cf.lmS Y T nb (pt ρ z) r).val (Sum.elim m u) := by
  have e := planeF_ent (ρ := ρ) W (K3 := K3) (h := h) (t := tabOf T) (x := x) (lam := lam) (a := a)
    (z := z) (isD := isD)
  rw [hnb] at e
  have s1 : (z.extract 0 (nb - h.S.cf.lmS)).size = nb - h.S.cf.lmS := by
    rw [sizeCut _ (by omega)]
    omega
  rw [e, OnBytes.Road.eqTab_size, s1, rdCol_at]
  refine sum_congr rfl fun hi hhi => ?_
  have w1 : ρ.val ((eqTab (z.extract 0 (nb - h.S.cf.lmS))).getD hi zeroE) =
      Blocks.eqN (nb - h.S.cf.lmS) 0 (pt ρ z) hi :=
    eqTab_at ρ s1 (fun j hj => by
      rw [ptCut ρ z (by omega) (by omega), Nat.zero_add]) (mem_range.mp hhi)
  show _ = _ * u (Y.at' (T, r.addX (hi * 2 ^ h.S.cf.lmS)))
  rw [w1, L T _ (hg hi (mem_range.mp hhi)), hp]

end Forms

end K5Law
