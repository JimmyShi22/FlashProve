-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttReadHead.lean: a form overG of xl of the attention sub-proof, as the library's
read rd3; with tools on sums and weights.

Johnson/Road/Rows/AttReadLong.lean values the form xl as a sum of entries of its matrix under the
verifier's own weights. This file brings that sum, summed over the heads by overG, into the
library's read rd3 (Inst/Model/Att/Sums.lean), with the equality weights eqN (Blocks/Basic.lean).

Main theorems.
 - sum_perm4, reorder4: sums in another order.
 - hiOf_size, hiOf_value, lowOf_size, lowOf_value: the weights on the features of a head are
   equality weights of the point on the features.
 - head_rd3: a form overG of xl is rd3 of the array that the tensor's limbs spell.
 - rd3_congr: a read depends on its points and weights only as far as it reads them.
The four tensors of the matrix qa (readHead, readGroup) are treated in
Johnson/Road/Rows/AttEnds14Proofs.lean, a plane below the diagonal in
Johnson/Road/Rows/AttEnds14Below.lean.

Every theorem on a form begins "if the routine returns". Nothing is said about probabilities or
about hiding. The program does not import this file.


-/
import Johnson.Road.Rows.AttReadLong
import Johnson.Road.Rows.AttReadRow
import Cb.Pv.Att.Mean.Reads

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open Cb.Pv.Att

open Finset
open OnBytes.Model (Reading World Aff Fork SubM HFun HTailF2 TenAt tenCell eqTab blockRows)
open OnBytes.Attention (Shape Heard)
open OnBytes.Road.Hd (Ok colsOf rdW)
open Inst.Model.AttSeg (rd3 qryV outV keyV valV)

variable {K : Type} [Field K]

/-! ## Sums in another order -/

/-- A fourfold sum with the last index first and the middle two exchanged. -/
theorem sum_perm4 (A B C D : Finset ℕ) (g : ℕ → ℕ → ℕ → ℕ → K) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, g a b c d =
      ∑ d ∈ D, ∑ a ∈ A, ∑ c ∈ C, ∑ b ∈ B, g a b c d := by
  calc ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, g a b c d
      = ∑ a ∈ A, ∑ c ∈ C, ∑ b ∈ B, ∑ d ∈ D, g a b c d := sum_congr rfl fun a _ => sum_comm
    _ = ∑ a ∈ A, ∑ c ∈ C, ∑ d ∈ D, ∑ b ∈ B, g a b c d :=
        sum_congr rfl fun a _ => sum_congr rfl fun c _ => sum_comm
    _ = ∑ a ∈ A, ∑ d ∈ D, ∑ c ∈ C, ∑ b ∈ B, g a b c d := sum_congr rfl fun a _ => sum_comm
    _ = ∑ d ∈ D, ∑ a ∈ A, ∑ c ∈ C, ∑ b ∈ B, g a b c d := sum_comm

/-- The sum that xl gives, in the order of a read. -/
theorem reorder4 (A B C D : Finset ℕ) (H cl L T : ℕ → K) (f : ℕ → ℕ → ℕ → ℕ → K) :
    ∑ ch ∈ A, H ch * ∑ l ∈ B, cl l * ∑ c ∈ C, ∑ i ∈ D, L c * T i * f l ch c i =
      ∑ i ∈ D, ∑ ch ∈ A, ∑ c ∈ C, T i * (H ch * L c) * ∑ l ∈ B, cl l * f l ch c i := by
  simp only [mul_sum]
  rw [sum_perm4]
  exact sum_congr rfl fun i _ => sum_congr rfl fun ch _ => sum_congr rfl fun c _ =>
    sum_congr rfl fun l _ => by ring

/-! ## The weights on the features of a head -/

section Feat
variable (ρ : Reading K) (S : Shape) {zc : Array E}

/-- There is a weight for each block of a head's features. -/
theorem hiOf_size (hz : zc.size = S.cf.ldh) : (hiOf S zc).size = 2 ^ (S.cf.ldh - S.ls) := by
  unfold hiOf
  rw [eqTab_size]
  congr 1
  simp only [Array.size_extract]
  omega

/-- The weight of a block of a head's features. -/
theorem hiOf_value (hz : zc.size = S.cf.ldh) {ch : ℕ} (h : ch < 2 ^ (S.cf.ldh - S.ls)) :
    ρ.val ((hiOf S zc).getD ch zeroE) = Blocks.eqN (S.cf.ldh - S.ls) 0 (pt ρ zc) ch := by
  have s1 : (zc.extract 0 S.cf.ldh).size = S.cf.ldh := by
    rw [Array.size_extract]
    omega
  have s2 : ((zc.extract 0 S.cf.ldh).extract 0 ((zc.extract 0 S.cf.ldh).size - S.ls)).size =
      S.cf.ldh - S.ls := by
    rw [Array.size_extract, s1]
    omega
  unfold hiOf
  rw [eqTab_value ρ _ ch (by rw [s2]; exact h), s2]
  refine eqN_congr' _ _ (fun j hj => ?_) ch
  unfold pt
  rw [getD_extract _ (by rw [s1]; omega) (by rw [s1]; omega),
    getD_extract _ (by omega) (by omega)]
  simp only [Nat.zero_add]

/-- There is a weight for each feature of a block. -/
theorem lowOf_size (hz : zc.size = S.cf.ldh) (hls : S.ls ≤ S.cf.ldh) :
    (lowOf S zc).size = 2 ^ S.ls := by
  unfold lowOf
  rw [eqTab_size]
  congr 1
  rw [Array.size_extract]
  omega

/-- The weight of a feature of a block. -/
theorem lowOf_value (hz : zc.size = S.cf.ldh) (hls : S.ls ≤ S.cf.ldh) {c : ℕ}
    (h : c < 2 ^ S.ls) :
    ρ.val ((lowOf S zc).getD c zeroE) = Blocks.eqN S.ls (S.cf.ldh - S.ls) (pt ρ zc) c := by
  have s1 : (zc.extract (zc.size - S.ls) zc.size).size = S.ls := by
    rw [Array.size_extract]
    omega
  unfold lowOf
  rw [eqTab_value ρ _ c (by rw [s1]; exact h), s1, ← eqN_shift' S.ls (S.cf.ldh - S.ls)]
  refine eqN_congr' _ _ (fun j hj => ?_) c
  unfold pt
  rw [getD_extract _ (Nat.le_refl _) (by omega), hz]

end Feat

/-! ## A read depends on what it reads -/

/-- Two reads agree if their points agree on the coordinates that are read and their weights on the
positions. -/
theorem rd3_congr (D : Inst.Model.AttSeg.Dim) {vg vg' Ψ Ψ' vn vn' : ℕ → K}
    (hg : ∀ j < D.lg, vg j = vg' j) (hΨ : ∀ i < D.T, Ψ i = Ψ' i) (hn : ∀ j < D.ln, vn j = vn' j)
    (a : ℕ → ℕ → ℕ → K) : rd3 D vg Ψ vn a = rd3 D vg' Ψ' vn' a := by
  unfold rd3
  refine sum_congr rfl fun g _ => sum_congr rfl fun i hi => sum_congr rfl fun n _ => ?_
  rw [hΨ i (mem_range.mp hi),
    eqN_agree (a := vg) (a' := vg') (off := 0) (off' := 0)
      (fun k hk => by rw [Nat.zero_add]; exact hg k hk) g,
    eqN_agree (a := vn) (a' := vn') (off := 0) (off' := 0)
      (fun k hk => by rw [Nat.zero_add]; exact hn k hk) n]

section Forms

variable {ρ : Reading K} {W : World K} {tl : HTailF2} {K3 : ℕ} {M : Mats K} {h : Heard}
  {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}

/-! ## overG of xl -/

/-- A form on a table on blocks of features, summed over the heads of keys and values, is the
library's read of the array that the tensor's limbs spell. hdOf g: the tensor's head at g. -/
theorem head_rd3 (A : AttAt ρ W tl K3 M h lid cf fs) {F : Fork} (hc : Cols F h K3)
    {t mat wc : ℕ} {X : TenAt} {zg zc tok : Array E} {lam : ℕ} (hdOf : ℕ → ℕ)
    (Tb : TabAt tl h t mat (2 ^ h.S.cf.la) (blockRows (lowOf h.S zc) tok))
    (hm : mat < tl.NM) (hM : (tl.mats.getD mat {}).m = wc * h.S.T) (hwc : wc % 2 ^ h.S.ls = 0)
    (htok : tok.size = h.S.T) (hzg : h.S.cf.lgk ≤ zg.size) (hzc : zc.size = h.S.cf.ldh)
    (hX : ∀ g l, 2 ^ h.S.ls ∣ tenCell X l lam (hdOf g * h.S.dh))
    (arr : ℕ → ℕ → ℕ → K)
    (harr : ∀ g i n, arr g i n = ∑ l ∈ range X.nl, 256 ^ l *
      mAt M (L5.featCell h.S mat wc (tenCell X l lam (hdOf g * h.S.dh) + n) i))
    {C : Ctx} {q : Aff} {G : Fork} {D : Ctx}
    (hq : Ok (Attention.overG h zg fun g => Attention.xl h t X lam (hdOf g) zc) F C q G D) :
    q.value ρ W =
      rd3 (L5.dimOf h.S) (pt ρ zg) (fun i => ρ.val (tok.getD i zeroE)) (pt ρ zc) arr := by
  have Z := sizes_of_hid A.shape
  obtain ⟨-, -, e⟩ := rowOverG_value A hzg _
    (fun g => ∑ ch ∈ range (hiOf h.S zc).size, ρ.val ((hiOf h.S zc).getD ch zeroE) *
      ∑ l ∈ range X.nl, (256 : K) ^ l *
        ∑ c ∈ range (2 ^ h.S.ls), ∑ i ∈ range h.S.T,
          ρ.val ((lowOf h.S zc).getD c zeroE) * ρ.val (tok.getD i zeroE) *
            mAt M (L5.featCell h.S mat wc
              (tenCell X l lam (hdOf g * h.S.dh) + (ch * 2 ^ h.S.ls + c)) i))
    (fun g _ x G1 D1 hx =>
      xl_value A Z hc Tb hm hM hwc (lowOf_size h.S hzc Z.ls) htok (hX g) hx) hq
  rw [e]
  unfold rd3
  rw [dim_T A]
  refine sum_congr rfl fun g _ => ?_
  have hch : (L5.dimOf h.S).ch = 2 ^ (h.S.cf.ldh - h.S.ls) * 2 ^ h.S.ls := by
    show 2 ^ h.S.cf.ldh = _
    rw [← pow_add]
    congr 1
    have := Z.ls
    omega
  rw [reorder4, hiOf_size h.S hzc, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [hch, Alg.sum_range_mul_add, mul_sum]
  refine sum_congr rfl fun ch hch' => ?_
  rw [mul_sum]
  refine sum_congr rfl fun c hc' => ?_
  have e1 := Blocks.eqN_append' (h.S.cf.ldh - h.S.ls) h.S.ls 0 (pt ρ zc) ch (mem_range.mp hc')
  have e2 : h.S.cf.ldh - h.S.ls + h.S.ls = h.S.cf.ldh := by
    have := Z.ls
    omega
  rw [e2, Nat.zero_add] at e1
  show _ = Blocks.eqN h.S.cf.lgk 0 (pt ρ zg) g * _ *
    Blocks.eqN h.S.cf.ldh 0 (pt ρ zc) (ch * 2 ^ h.S.ls + c) * _
  rw [e1, harr, hiOf_value ρ h.S hzc (mem_range.mp hch'),
    lowOf_value ρ h.S hzc Z.ls (mem_range.mp hc')]
  ring

end Forms

end OnBytes.Road.Rows
