-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5AttD5.lean

The attention link's own dictionary against the one dictionary by labels: at every place that
segment 2 g + 1 of the library's model may read, "attMx S g Zg" (Johnson/Road/Lane5AttMx.lean) holds
what "D5" (Johnson/Road/HeadDict.lean) holds, if

  hAt: the letter At of D5, which stands for attention's own segments, is attMx's segment 2 g + 1;
  hqa: the matrices Zl that are named by labels hold, at the label that the layers' formula labA
       gives the matrix qa of group g, the link's copy of qa (number NAs + 3 of its list).

Who reads it: "linkOK_congr" (Johnson/Road/Lane5Congr.lean) carries "link 2 g + 1 is in order" from
attMx to D5 over it, at the twelve odd links.

What is compared with what: two definitions of these files. Not claimed: that the copy of qa bears
that label in the verifier's plan of the attention sub-proof: that is group_label_qa of
Johnson/Road/Lane5AttLabel.lean.
-/
import Johnson.Road.Lane5AttMx
import Johnson.Road.HeadDict

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open OnBytes.Model.Layer (Lay matIx)
open Cm.Seg (at' reads plFF plAtt)

/-- attMx in slot 5 of segment 2 g. -/
theorem attMx_five (S : Attention.Shape) (g : ℕ) (Z : Zs) {r : ℕ} (hr : r / 65536 = 5) (c : ℕ) :
    attMx S g Z (2 * g) r c = Z (S.cf.NAs + 3) (r % 65536) c := by
  unfold attMx
  rw [if_neg (show ¬ 2 * g = 2 * g + 1 by omega),
    if_pos (show 2 * g = 2 * g ∧ r / 65536 = 5 from ⟨rfl, hr⟩)]

/-- D5 in an odd segment is its letter At. -/
theorem D5_odd (h : Model.Head.Shape) (y : Lay) (At Zl : ℕ → ℕ → ℕ → ℤ) (g r c : ℕ) :
    Hd.D5 h y At Zl (2 * g + 1) r c = At g r c := by
  show (if 2 * g + 1 = 24 then Hd.mzH h y Zl (r / 65536) (r % 65536) c
      else if (2 * g + 1) % 2 = 0 then
        mzA y Zl ((2 * g + 1) / 2) (Hd.slotNo y (r / 65536)) (r % 65536) c
      else At ((2 * g + 1) / 2) r c) = _
  rw [if_neg (show ¬ 2 * g + 1 = 24 by omega), if_neg (show ¬ (2 * g + 1) % 2 = 0 by omega),
    show (2 * g + 1) / 2 = g by omega]

/-- **At every place that segment 2 g + 1 may read, attMx is D5.** -/
theorem attMx_D5 (hd : Cm.Seg.Hd) (h : Model.Head.Shape) (y : Lay) (S : Attention.Shape) {g : ℕ}
    (hg : g < 12) (Zg : Zs) (At Zl : ℕ → ℕ → ℕ → ℤ)
    (hAt : ∀ r c, At g r c = attMx S g Zg (2 * g + 1) r c)
    (hqa : ∀ r c, Zl (labA y g (matIx y).iQA) r c = Zg (S.cf.NAs + 3) r c) :
    ∀ q ∈ reads hd (2 * g + 1), at' (attMx S g Zg) q = at' (Hd.D5 h y At Zl) q := by
  intro q hq
  rcases hq with ⟨g', c, e, hg', hc, rfl⟩ | ⟨g', c, e, hg', hc, rfl⟩ | ⟨e, _⟩
  · omega
  · obtain rfl : g = g' := by omega
    rcases Cm.Seg.ownAtt_cases g c with e1 | ⟨c', e1, hm⟩
    · rw [e1]
      show attMx S g Zg (2 * g + 1) (plAtt c).1 (plAtt c).2 =
        Hd.D5 h y At Zl (2 * g + 1) (plAtt c).1 (plAtt c).2
      rw [D5_odd, hAt]
    · have hv := Cm.Seg.ownAtt_valid hd hg' hc
      rw [e1] at hv ⊢
      show attMx S g Zg (2 * g) (plFF c').1 (plFF c').2 =
        Hd.D5 h y At Zl (2 * g) (plFF c').1 (plFF c').2
      have hr5 : (plFF c').1 / 65536 = 5 := by
        have hr := Cm.Seg.plFF_row _ hv.2.1
        rw [Cm.Seg.plFF_row_qa _ hv.2.1 hm]
        rw [Cm.Seg.hSlot_eq] at hr ⊢
        omega
      rw [attMx_five S g Zg hr5, Hd.D5_even h y At Zl (s := 2 * g) (by omega) (by omega), hr5,
        show 2 * g / 2 = g by omega]
      exact (hqa _ _).symm
  · omega

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.attMx_D5
