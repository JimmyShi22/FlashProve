-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Thin/Kinds/Fold.lean.
A KNOW-ONLY LEMMA FOR EACH KIND OF MOVE. THE KIND «fold» (LdFoldD, Cb/Req1/LdSegKit.lean:250-350).
D4 LdFoldD.HypK: the four of l AT THE JOINTS OF Hyp.good (D.S.over D.src.A, NOT «.cf», to
D.mid.rels), and word. NOT IN IT: good's other six; wit; laws.
Laws is read by nobody in this move's proof AND IS OWED AT THE LOCATIONS (the library makes
loc's laws out of fold's:
Cb/Req1/LdSegFit.lean:161-165). The four of l are a PREMISE: whoever builds «bridge,
arrangement, fold» owes them.
K4a LdFoldD.stepK: the re-bracketing is a plain step from the middle joint WITH Tw BESIDE ITS
CONDITION (the library's Rels.and): no premise.
Its lines are the library's (Cb/Req1/LdSegProofsFold.lean:109-114, :137-154), re-seated. K4
LdFoldD.goodK.
NO THIN DEFINITION OR PREMISE names a bundle, an honest side, a joint's exact relation or core. THE
CONTROLS AND EXAMPLES DO.

-/
import Cb.Thin.Kinds.Rules
import Cb.Req1.LdSegProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Ood IOR IOR.Chain

/-- D4. -/
structure LdFoldD.HypK {E Kc : Type} [Field E] [Fintype E] (D : LdFoldD E Kc)
    (l : IOR.Link Kc D.src.J D.mid) : Prop where
  good : IOR.GoodK₀ l.R (D.S.over D.src.A) D.mid.rels l.ext l.P.err
  word : ∀ a τ b, l.R.red.out a τ = some b → D.Tw b

/-- K4a: NO PREMISE. -/
theorem LdFoldD.stepK {E Kc : Type} [Field E] [Fintype E] (D : LdFoldD E Kc) :
    IOR.StepK (fun x => some (D.pX x)) D.pE (fun _ w => D.pB w)
      (D.mid.rels.and (fun _ _ _ => True) (fun _ _ => True) D.Tw) (D.S₂.over D.tgt.A) where
  isLocal := D.pE_isLocal
  onOut := by
    rintro x y x' ⟨hon, hT⟩ hf
    rw [← Option.some.inj hf]
    refine ⟨fun i => hon.2.1 i.1, fun k => ?_, hon.2.2⟩
    have h3 : ¬ (D.S.om k.1.1).ClashW ((D.S.om k.1.1).upW (y.2.2 k.1)) (x.2.2 k.1).1 := hon.2.1 k.1
    have hT' : D.sW k y.1 = (D.S.om k.1.1).upW (y.2.2 k.1) := hT k
    rw [← hT'] at h3
    exact h3
  know := by
    rintro x y x' w ⟨-, hT⟩ hf hw
    rw [← Option.some.inj hf] at hw
    obtain ⟨hd, hc, hk, hA₀⟩ := hw
    refine ⟨⟨hc, fun i => ?_, ?_⟩, trivial⟩
    · by_cases hi : D.cl i
      · have : (D.S.om i.1).decW (D.sW ⟨i, hi⟩ y.1) (x.2.2 i) =
            some (D.held.msg w.2.1.1 ⟨i, hi⟩) := hk ⟨i, hi⟩
        have hT' : D.sW ⟨i, hi⟩ y.1 = (D.S.om i.1).upW (y.2.2 i) := hT ⟨i, hi⟩
        rw [hT'] at this
        show (D.S.om i.1).dec _ _ = some ((D.pB w).2.1 i).1
        simp only [LdFoldD.pB, dif_pos hi]
        exact this
      · have := hd ⟨i, hi⟩
        show (D.S.om i.1).dec _ _ = some ((D.pB w).2.1 i).1
        simp only [LdFoldD.pB, dif_neg hi]
        exact this
    · show D.A₀.relR _ (D.S₁.msgs (D.pB w).2.1, w.2.2)
      rw [D.rd_pB]
      exact hA₀

/-- K4. -/
theorem LdFoldD.goodK {E Kc : Type} [Field E] [Fintype E] (D : LdFoldD E Kc)
    (l : IOR.Link Kc D.src.J D.mid) (h : D.HypK l) : (D.link l).GoodK :=
  (goodK_iff (D.link l)).2
    (goodK₀_cf _ (D.S.over D.src.A) (D.S₂.over D.tgt.A) _ _
      (goodK₀_post l.R (D.S.over D.src.A)
        (D.mid.rels.and (fun _ _ _ => True) (fun _ _ => True) D.Tw) (D.S₂.over D.tgt.A) l.ext
        (D.link l).ext l.P.err (fun x => some (D.pX x)) D.pE (fun _ w => D.pB w)
        ⟨h.good.point, h.good.isLocal,
          fun a τ b ha hb => ⟨h.good.onOut a τ b ha hb, h.word a τ b hb⟩,
          h.good.know.conseq (fun _ ha => ha) (fun _ _ _ hw => hw) fun _ _ hw => hw.1⟩
        D.stepK fun _ _ _ _ _ => rfl))

/-! ## The controls -/

/-- C6: (c1). -/
theorem LdFoldD.hypK_of_hyp {E Kc : Type} [Field E] [Fintype E] (D : LdFoldD E Kc)
    (l : IOR.Link Kc D.src.J D.mid) (h : D.Hyp l) : D.HypK l :=
  ⟨goodK₀_of_goodT h.good, h.word⟩

/-- (c2). -/
example {E Kc : Type} [Field E] [Fintype E] (D : LdFoldD E Kc) (l : IOR.Link Kc D.src.J D.mid)
    (h : D.Hyp l) :
    (ldSeg_fold_goodT D l h).know = (D.goodK l (D.hypK_of_hyp l h)).know := rfl
example {E Kc : Type} [Field E] [Fintype E] (D : LdFoldD E Kc) (l : IOR.Link Kc D.src.J D.mid)
    (h : D.Hyp l) :
    (ldSeg_fold_goodT D l h).onOut = (D.goodK l (D.hypK_of_hyp l h)).onOut := rfl
example {E Kc : Type} [Field E] [Fintype E] (D : LdFoldD E Kc) (l : IOR.Link Kc D.src.J D.mid)
    (h : D.Hyp l) :
    (ldSeg_fold_goodT D l h).isLocal = (D.goodK l (D.hypK_of_hyp l h)).isLocal := rfl
example {E Kc : Type} [Field E] [Fintype E] (D : LdFoldD E Kc) (l : IOR.Link Kc D.src.J D.mid)
    (h : D.Hyp l) :
    (ldSeg_fold_goodT D l h).point = (D.goodK l (D.hypK_of_hyp l h)).point := rfl

end Cb

#check @Cb.LdFoldD.stepK
#check @Cb.LdFoldD.goodK
#print Cb.LdFoldD.HypK
