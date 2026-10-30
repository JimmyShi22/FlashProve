-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/MeanRd3.lean: kind K5: the readers on the long tables are the
library's own reads of the cells (Inst/Model/Att/Sums.lean: rd3), for the written forms. Twins of
xl_value (Johnson/Road/Rows/AttReadLong.lean) and head_rd3 (Johnson/Road/Rows/AttReadHead.lean),
which speak of a run of a routine in a context. The written forms stand in the run's place
(Johnson/Desc/First/Att/Claims/Worth.lean); the pure lemmas are used as they stand; the proofs' pure
parts follow those proofs line for line.

Main names:
  `xlT_rd`: the written form of xl, as the fourfold sum over blocks, limbs, features of a block and
    tokens.
  `headF_rd3`: (Fo.overGF h zg fun g => Fo.xlT h K3 t X lam (hdOf g) zc).value ρ W = rd3 (L5.dimOf
    h.S) (pt ρ zg) (the table's token weights, read) (pt ρ zc) arr, arr the array that the tensor's
    limbs spell.
Premises beyond those of Johnson/Road/Rows, which takes them from the run's return: the head's
features are lawful (headFeat … = .ok); the indices read lie in the table.
Johnson/Desc/First/Att/Claims/InRunAll.lean draws both out of the kind's runs' return.
Used: as Johnson/Desc/First/Att/Claims/MeanRd.lean, and Sizes, sizes_of_hid, long_read, limb_value,
hiOf, lowOf, hiOf_size, hiOf_value, lowOf_size, lowOf_value, reorder4, Alg.sum_range_mul_add,
Blocks.eqN_append'; the library's rd3.
Not claimed: that a table is true.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Road.Rows.AttReadHead
import Johnson.Desc.First.Att.Claims.MeanRd

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open Finset
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open OnBytes.Road.Hd (rdW)
open Inst.Model.AttSeg (rd3)

variable {Kf : Type} [Field Kf] {ρ : Reading Kf} {W : World Kf} {tl : HTailF2} {K3 : ℕ} {M : Mats Kf}
  {h : Attention.Heard} {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}

/-- **The written form of xl**: a sum over the blocks ch of a head's features, the limbs l, the features c of a block and the tokens i. -/
theorem xlT_rd (A : AttAt ρ W tl K3 M h lid cf fs) (Z : Sizes h.S) {t mat wc : ℕ} {X : TenAt}
    {lam hd : ℕ} {zc low tok : Array E}
    (Tb : TabAt tl h t mat (2 ^ h.S.cf.la) (blockRows low tok))
    (hm : mat < tl.NM) (hM : (tl.mats.getD mat {}).m = wc * h.S.T) (hwc : wc % 2 ^ h.S.ls = 0)
    (hlow : low.size = 2 ^ h.S.ls) (htok : tok.size = h.S.T)
    (hX : ∀ l, 2 ^ h.S.ls ∣ tenCell X l lam (hd * h.S.dh))
    (hcut : h.S.ls ≤ (zc.extract 0 h.S.cf.ldh).size) (hfeat : headFeat X hd h.S.dh = .ok (hd * h.S.dh))
    (hin : ∀ ch < (hiOf h.S zc).size, ∀ l < X.nl,
      tenCell X l lam (hd * h.S.dh) / 2 ^ h.S.ls + ch < (h.t.tabLen.lookup t).getD 0) :
    (Fo.xlT h K3 t X lam hd zc).value ρ W =
      ∑ ch ∈ range (hiOf h.S zc).size, ρ.val ((hiOf h.S zc).getD ch zeroE) *
        ∑ l ∈ range X.nl, (256 : Kf) ^ l *
          ∑ c ∈ range (2 ^ h.S.ls), ∑ i ∈ range h.S.T,
            ρ.val (low.getD c zeroE) * ρ.val (tok.getD i zeroE) *
              mAt M (L5.featCell h.S mat wc
                (tenCell X l lam (hd * h.S.dh) + (ch * 2 ^ h.S.ls + c)) i) := by
  have hc : cutLast (zc.extract 0 h.S.cf.ldh) h.S.ls =
      .ok ((zc.extract 0 h.S.cf.ldh).extract 0 ((zc.extract 0 h.S.cf.ldh).size - h.S.ls),
        (zc.extract 0 h.S.cf.ldh).extract ((zc.extract 0 h.S.cf.ldh).size - h.S.ls)
          (zc.extract 0 h.S.cf.ldh).size) := by
    unfold cutLast
    rw [if_neg (by omega)]
  rw [xlT_value ρ W h K3 t X lam hd zc _ _ hc hfeat, list_sum_range]
  refine sum_congr rfl fun ch hch => ?_
  congr 1
  rw [list_sum_range]
  refine sum_congr rfl fun l hl => ?_
  rw [limb_value A.num (mem_range.mp hl)]
  congr 1
  show rdW W h.iU3 K3 _ = _
  rw [long_read A Z Tb hm hM hwc hlow htok (hin ch (mem_range.mp hch) l (mem_range.mp hl))]
  refine sum_congr rfl fun c _ => sum_congr rfl fun i _ => ?_
  obtain ⟨u, hu⟩ := hX l
  have e : (tenCell X l lam (hd * h.S.dh) / 2 ^ h.S.ls + ch) * 2 ^ h.S.ls + c =
      tenCell X l lam (hd * h.S.dh) + (ch * 2 ^ h.S.ls + c) := by
    rw [hu, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]
    ring
  rw [e]

/-- **A written form on a table on blocks of features, summed over the heads, is the library's read of the array that the tensor's limbs spell.** -/
theorem headF_rd3 (A : AttAt ρ W tl K3 M h lid cf fs) {t mat wc : ℕ} {X : TenAt}
    {zg zc tok : Array E} {lam : ℕ} (hdOf : ℕ → ℕ)
    (Tb : TabAt tl h t mat (2 ^ h.S.cf.la) (blockRows (lowOf h.S zc) tok))
    (hm : mat < tl.NM) (hM : (tl.mats.getD mat {}).m = wc * h.S.T) (hwc : wc % 2 ^ h.S.ls = 0)
    (htok : tok.size = h.S.T) (hzg : h.S.cf.lgk ≤ zg.size) (hzc : zc.size = h.S.cf.ldh)
    (hX : ∀ g l, 2 ^ h.S.ls ∣ tenCell X l lam (hdOf g * h.S.dh))
    (arr : ℕ → ℕ → ℕ → Kf)
    (harr : ∀ g i n, arr g i n = ∑ l ∈ range X.nl, 256 ^ l *
      mAt M (L5.featCell h.S mat wc (tenCell X l lam (hdOf g * h.S.dh) + n) i))
    (hfeat : ∀ g < 2 ^ h.S.cf.lgk, headFeat X (hdOf g) h.S.dh = .ok (hdOf g * h.S.dh))
    (hin : ∀ g < 2 ^ h.S.cf.lgk, ∀ ch < (hiOf h.S zc).size, ∀ l < X.nl,
      tenCell X l lam (hdOf g * h.S.dh) / 2 ^ h.S.ls + ch < (h.t.tabLen.lookup t).getD 0) :
    (Fo.overGF h zg fun g => Fo.xlT h K3 t X lam (hdOf g) zc).value ρ W =
      rd3 (L5.dimOf h.S) (pt ρ zg) (fun i => ρ.val (tok.getD i zeroE)) (pt ρ zc) arr := by
  have Z := sizes_of_hid A.shape
  have hcut : h.S.ls ≤ (zc.extract 0 h.S.cf.ldh).size := by
    rw [Array.size_extract]
    have := Z.ls
    omega
  rw [overGF_rd A hzg]
  unfold rd3
  rw [dim_T A]
  refine sum_congr rfl fun g hg => ?_
  rw [xlT_rd A Z Tb hm hM hwc (lowOf_size h.S hzc Z.ls) htok (hX g) hcut (hfeat g (mem_range.mp hg))
    (hin g (mem_range.mp hg))]
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

end K5Law
