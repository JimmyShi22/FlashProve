-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttEntLong.lean: the verifier's forms on tensors and on planes of the attention
sub-proof, on the entries of the vector of tables as they were sent; they are the library-side
reading forms.

As Johnson/Road/Rows/AttEntRow.lean, for the other two kinds of tables. readHead and readGroup read
a tensor in a table on blocks of features (xl in OnBytes/Model/AttentionClaimsA.lean). plane reads a
plane of the matrix as in a table on neighbouring places. In any world the form that such a function
returns is a public combination of entries of the vector of tables. Under the dictionary LateAt it
is worth what the reading form rdLong or rdCol of Cb/Pv/Att/End/Tabs.lean is worth.

Main definitions.
 - placeTen S X l lam hd n: the place, within a table on blocks of features, of the entry that holds
   feature n of head hd, in limb l and layer lam of the tensor X.
 - placeCol S r: the place, within a table on the matrix as, of the entry whose first cell has the
   name r.
Main theorems.
 - xl_ent, head_ent: the forms on entries of the vector. head_long: they are worth what rdLong is.
 - plane_ent: the form on entries of the vector. plane_col: it is worth what rdCol is.

What is not claimed. That the dictionary holds of the programs' message. Every theorem on a form
begins "if the routine returns". Nothing is said about probabilities or about hiding. The program
does not import this file.


-/
import Johnson.Road.Rows.AttEntRow
import Johnson.Road.Rows.AttReadHead
import Johnson.Road.Rows.AttEnds14Tiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open Finset
open OnBytes.Model (Reading World Aff Fork SubM TenAt tenCell eqTab)
open OnBytes.Attention (Heard)
open OnBytes.Road.Hd (Ok colsOf rdW)
open Inst.Model.AttSeg (Raw Reg)
open Cb.Pv.Att.End (LateLay AttTab rdLong rdLong_at rdCol rdCol_at)

variable {K : Type} [Field K]

/-! ## Tensors -/

section Ent
variable {ρ : Reading K} (W : World K) {K3 : ℕ} {h : Heard} {lid : ℕ} {cf : Attention.Cfg}
  {fs : Model.Forest.Shape}

/-- The form xl, on the entries of the table that begins at t. -/
theorem xl_ent (N : Numerals ρ) {F : Fork} (hc : Cols F h K3) {t : ℕ} {X : TenAt} {lam hd : ℕ}
    {zc : Array E} {q : Aff} {G : Fork} {C D : Ctx}
    (hq : Ok (Attention.xl h t X lam hd zc) F C q G D) :
    G = F ∧ D = C ∧ q.value ρ W =
      ∑ ch ∈ range (hiOf h.S zc).size, ρ.val ((hiOf h.S zc).getD ch zeroE) *
        ∑ l ∈ range X.nl, (256 : K) ^ l *
          rdW W h.iU3 K3 (t + (tenCell X l lam (hd * h.S.dh) / 2 ^ h.S.ls + ch)) := by
  unfold Attention.xl at hq
  dsimp only at hq
  split at hq
  · rename_i cut hcut
    obtain ⟨-, ecut⟩ := cutLast_ok hcut
    split at hq
    · rename_i j0 hj0
      have ej := headFeat_ok hj0
      rw [ecut, ej] at hq
      obtain ⟨e1, e2, -, e3⟩ := weighted_value ρ W _ _ _
        (fun ch => ∑ l ∈ range X.nl, (256 : K) ^ l *
          rdW W h.iU3 K3 (t + (tenCell X l lam (hd * h.S.dh) / 2 ^ h.S.ls + ch)))
        (fun _ => True)
        (by
          intro ch _ x G1 D1 hx
          obtain ⟨a1, a2, -, a3⟩ := weighted_value ρ W _ _ _
            (fun l => rdW W h.iU3 K3 (t + (tenCell X l lam (hd * h.S.dh) / 2 ^ h.S.ls + ch)))
            (fun _ => True)
            (by
              intro l _ y G2 D2 hy
              obtain ⟨b1, b2, -, b4⟩ := u3at_value ρ W hy
              refine ⟨b1, b2, trivial, ?_⟩
              have hc' : colsOf F h.iU3 = K3 := hc
              rw [b4, hc']) hx
          refine ⟨a1, a2, trivial, ?_⟩
          rw [a3]
          exact sum_congr rfl fun l hl => by rw [limb_value N (mem_range.mp hl)]) hq
      exact ⟨e1, e2, e3⟩
    · exact absurd hq (refuse_not_ok _ _ _ _ _ _)
  · exact absurd hq (refuse_not_ok _ _ _ _ _ _)

/-- A tensor, summed over the heads of keys and values, on entries of the vector. hdOf g: the
tensor's head at the head g of keys and values. -/
theorem head_ent (A : AttPub ρ h lid cf fs) {F : Fork} (hc : Cols F h K3) {t : ℕ} {X : TenAt}
    {zg zc : Array E} {lam : ℕ} (hdOf : ℕ → ℕ) (hzg : h.S.cf.lgk ≤ zg.size)
    (hzc : zc.size = h.S.cf.ldh) {C : Ctx} {q : Aff} {G : Fork} {D : Ctx}
    (hq : Ok (Attention.overG h zg fun g => Attention.xl h t X lam (hdOf g) zc) F C q G D) :
    G = F ∧ D = C ∧ q.value ρ W =
      ∑ g ∈ range (2 ^ h.S.cf.lgk), Blocks.eqN h.S.cf.lgk 0 (pt ρ zg) g *
        ∑ ch ∈ range (2 ^ (h.S.cf.ldh - h.S.ls)),
          Blocks.eqN (h.S.cf.ldh - h.S.ls) 0 (pt ρ zc) ch *
            ∑ l ∈ range X.nl, (256 : K) ^ l *
              rdW W h.iU3 K3 (t + (tenCell X l lam (hdOf g * h.S.dh) / 2 ^ h.S.ls + ch)) := by
  obtain ⟨e1, e2, e⟩ := overG_ent W A hzg _ _ (fun _ _ _ _ _ hx => xl_ent W A.num hc hx) hq
  refine ⟨e1, e2, ?_⟩
  rw [e]
  refine sum_congr rfl fun g _ => ?_
  congr 1
  rw [hiOf_size h.S hzc]
  exact sum_congr rfl fun ch hch => by rw [hiOf_value ρ h.S hzc (mem_range.mp hch)]

/-- The form plane, on the entries of the table that begins at t. -/
theorem plane_ent {F : Fork} (hc : Cols F h K3) {t x lam a : ℕ} {z : Array E} {isD : Bool}
    {q : Aff} {G : Fork} {C D : Ctx} (hq : Ok (Attention.plane h t x lam a z isD) F C q G D) :
    G = F ∧ D = C ∧ q.value ρ W =
      ∑ hi ∈ range
          (eqTab (z.extract 0 ((if isD then h.S.nD else h.S.nM) - h.S.cf.lmS))).size,
        ρ.val ((eqTab (z.extract 0 ((if isD then h.S.nD else h.S.nM) - h.S.cf.lmS))).getD hi
          zeroE) *
          rdW W h.iU3 K3 (t + (planeFirst h.S x lam a isD >>> h.S.cf.lmS + hi)) := by
  unfold Attention.plane at hq
  dsimp only at hq
  obtain ⟨e1, e2, -, e3⟩ := weighted_value ρ W _ _ _
    (fun hi => rdW W h.iU3 K3 (t + (planeFirst h.S x lam a isD >>> h.S.cf.lmS + hi)))
    (fun _ => True)
    (by
      intro hi _ y G2 D2 hy
      obtain ⟨b1, b2, -, b4⟩ := u3at_value ρ W hy
      refine ⟨b1, b2, trivial, ?_⟩
      have hc' : colsOf F h.iU3 = K3 := hc
      rw [b4, hc']
      rfl) hq
  exact ⟨e1, e2, e3⟩

end Ent

/-! ## Places -/

/-- The place, within a table on blocks of features, of the entry that holds feature n of head hd,
in limb l and layer lam of the tensor X. -/
def placeTen (S : Attention.Shape) (X : TenAt) (l lam hd n : ℕ) : ℕ :=
  tenCell X l lam (hd * S.dh) / 2 ^ S.ls + n / 2 ^ S.ls

/-- The place, within a table on the matrix as, of the entry whose first cell has the name r. -/
def placeCol (S : Attention.Shape) : Raw → ℕ
  | .c .M x b y => planeFirst S x (b / S.HA) (b % S.HA) false >>> S.cf.lmS + y / 2 ^ S.cf.lmS
  | .c .D x b y => planeFirst S x (b / S.HA) (b % S.HA) true >>> S.cf.lmS + y / 2 ^ S.cf.lmS
  | _ => 0

/-- A multiple of a power of 2, divided by it. -/
theorem blk_div (s c : ℕ) : (0 + c * 2 ^ s) / 2 ^ s = c := by
  rw [Nat.zero_add]
  exact Nat.mul_div_cancel _ (Nat.two_pow_pos s)

/-! ## The verifier's forms are the reading forms -/

section Forms
variable {ρ : Reading K} {W : World K} {K3 : ℕ} {h : Heard} {lid : ℕ} {cf : Attention.Cfg}
  {fs : Model.Forest.Shape} {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂] [DecidableEq J₁]
  [DecidableEq J₂] {Y : LateLay AttTab J₂} {tabOf : AttTab → ℕ} {place : AttTab → Raw → ℕ}
  {u : J₂ → K} (m : J₁ → K) {F : Fork} {C : Ctx} {q : Aff} {G : Fork} {D : Ctx}

/-- A tensor, summed over the heads of keys and values, is worth what rdLong is worth. base: the
names of the limbs' first cells. -/
theorem head_long (A : AttPub ρ h lid cf fs) (hc : Cols F h K3)
    (L : LateAt W h K3 Y tabOf place u) (T : AttTab) {X : TenAt} {zg zc : Array E} {lam : ℕ}
    (hdOf : ℕ → ℕ) (hzg : h.S.cf.lgk ≤ zg.size) (hzc : zc.size = h.S.cf.ldh)
    (base : ℕ → ℕ → Raw)
    (hg : ∀ g < 2 ^ h.S.cf.lgk, ∀ ch < 2 ^ (h.S.cf.ldh - h.S.ls), ∀ l < X.nl,
      Y.good (T, (base l g).addN (ch * 2 ^ h.S.ls)))
    (hp : ∀ g ch, ∀ l < X.nl, place T ((base l g).addN (ch * 2 ^ h.S.ls)) =
      tenCell X l lam (hdOf g * h.S.dh) / 2 ^ h.S.ls + ch)
    (hq : Ok (Attention.overG h zg fun g => Attention.xl h (tabOf T) X lam (hdOf g) zc)
      F C q G D) :
    q.value ρ W = (rdLong (J₁ := J₁) (L5.dimOf h.S) h.S.ls Y T (pt ρ zg) (pt ρ zc) X.nl base).val
      (Sum.elim m u) := by
  rw [(head_ent W A hc hdOf hzg hzc hq).2.2, rdLong_at]
  refine sum_congr rfl fun g hg' => ?_
  congr 1
  refine sum_congr rfl fun ch hch => ?_
  congr 1
  refine sum_congr rfl fun l hl => ?_
  show _ = _ * u (Y.at' (T, (base l g).addN (ch * 2 ^ h.S.ls)))
  rw [L T _ (hg g (mem_range.mp hg') ch (mem_range.mp hch) l (mem_range.mp hl)),
    hp g ch l (mem_range.mp hl)]

/-- A plane is worth what rdCol is worth. nb: the number of bits of a place of the region; r: the
name of the plane's first cell. -/
theorem plane_col (hc : Cols F h K3) (L : LateAt W h K3 Y tabOf place u) (T : AttTab)
    {x lam a : ℕ} {z : Array E} {isD : Bool} {nb : ℕ}
    (hnb : (if isD then h.S.nD else h.S.nM) = nb) (hz : z.size = nb) (r : Raw)
    (hg : ∀ hi < 2 ^ (nb - h.S.cf.lmS), Y.good (T, r.addX (hi * 2 ^ h.S.cf.lmS)))
    (hp : ∀ hi, place T (r.addX (hi * 2 ^ h.S.cf.lmS)) =
      planeFirst h.S x lam a isD >>> h.S.cf.lmS + hi)
    (hq : Ok (Attention.plane h (tabOf T) x lam a z isD) F C q G D) :
    q.value ρ W =
      (rdCol (J₁ := J₁) h.S.cf.lmS Y T nb (pt ρ z) r).val (Sum.elim m u) := by
  obtain ⟨-, -, e⟩ := plane_ent W hc hq
  rw [hnb] at e
  have s1 : (z.extract 0 (nb - h.S.cf.lmS)).size = nb - h.S.cf.lmS := by
    rw [sizeCut _ (by omega)]
    omega
  rw [e, eqTab_size, s1, rdCol_at]
  refine sum_congr rfl fun hi hhi => ?_
  have w1 : ρ.val ((eqTab (z.extract 0 (nb - h.S.cf.lmS))).getD hi zeroE) =
      Blocks.eqN (nb - h.S.cf.lmS) 0 (pt ρ z) hi :=
    eqTab_at ρ s1 (fun j hj => by
      rw [ptCut ρ z (by omega) (by omega), Nat.zero_add]) (mem_range.mp hhi)
  show _ = _ * u (Y.at' (T, r.addX (hi * 2 ^ h.S.cf.lmS)))
  rw [w1, L T _ (hg hi (mem_range.mp hhi)), hp]

end Forms

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.head_long
#print axioms OnBytes.Road.Rows.plane_col
