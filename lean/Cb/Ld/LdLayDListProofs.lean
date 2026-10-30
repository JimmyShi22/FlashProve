-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLayDListProofs.lean: the proofs of the statements of Cb/Ld/LdLayDList.lean. `ldLayD_new`,
`ldLayD_cross`: one segment (laid by the one sending; crosses); `LdRefL.laidJ_closed`: the set of
laid facts is closed (under `MaskFact.JCl`); then one induction along the list for each statement.
What is said and what is not: the head of Cb/Ld/LdLayDList.lean.

Main names:
  `ldLayD_laid`: see its statement in Cb/Ld/LdLayDList.lean.
  `ldLayD_segs`: see its statement in Cb/Ld/LdLayDList.lean.
-/
import Cb.Ld.LdLayDList
import Cb.Ld.LdLayDKitProofs
import Cb.Ld.LdLayDBodyProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain

/-- the set of laid facts is closed (under `MaskFact.JCl`) -/
theorem LdRefL.laidJ_closed {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E}
    {a b : LdStage E Kc} (L : LdRefL E Kc I a b) (base : MaskFact a.J.W → Prop)
    (f : MaskFact b.J.W) (h : MaskFact.JCl (L.LaidJ base) f) : L.LaidJ base f := by
  cases L with
  | nil => simp only [LdRefL.LaidJ] at h ⊢; exact MaskFact.jcl_idem f h
  | snoc L S => simp only [LdRefL.LaidJ] at h ⊢; exact MaskFact.jcl_idem f h

section
variable {E Kc : Type} [Field E] [Fintype E]

/-- Laid by the one sending: under `hQ`, `hc`, `h`, `S.New` of the block's fact. -/
theorem ldLayD_new {I : LdRefIx E} {a : LdStage E Kc} (S : LdRefS E Kc I a) (β : LdPend S.d)
    (Q : LdLayQ E) (hQ : Q.Sound) (hc : S.CutD β.Rd β.own) (h : S.NewD Q β) : S.New β.fact := by
  obtain ⟨β₀, hl, rfl⟩ := h
  refine ⟨ldLayD_lays _ S.Qc.snd β₀ Q hQ hl, fun w w' M hk => ?_⟩
  have hA := (segWide_alike S.Qc.loc.tgt β₀.Rd β₀.Rr β₀.own β₀.Mk β₀.val w w' M hk).1
  exact hc _ _ fun n h1 h2 => hA ⟨.inr n.1, n.2⟩ h1 h2

/-- Crosses the segment: under the hypotheses below, some g' of G with `S.Carries g'` of the
block's fact. -/
theorem ldLayD_cross (pp : ℕ) [CharP E pp] (I : LdRefIx E) [Nonempty I.C.E0.Str]
    (a : LdStage E Kc) (S : LdRefS E Kc I a) (Q : LdLayQ E) (hQ : Q.Sound)
    (G : MaskFact a.J.W → Prop) (hG : ∀ f, MaskFact.JCl G f → G f) (hA : S.A.OK pp)
    (hg : S.K.R.c1.fold.Reads S.l) (β' : LdPend a) (β : LdPend S.d) (hβ' : G β'.fact)
    (hc : S.CutD β.Rd β.own) (h : S.CrossD Q pp β' β) :
    ∃ g', G g' ∧ S.Carries g' β.fact := by
  obtain ⟨W, own, Mk, _, _, val, RdN, RrN, hs, hW, rfl⟩ := h
  obtain ⟨g', hg', hE⟩ := ldLayD_step S.f S.g S.m S.back G hG β' _ hβ' hs
  obtain ⟨Fr, κ, hGh, hF, hQu⟩ := hW.out.front
  obtain ⟨c1, c2⟩ := hg
  obtain ⟨c4, c5⟩ := ldLayD_one _ S.Qc.snd _ _ _ Q hQ hW.one
  have n1 := ldLayD_noLook _ _ _ _ _ _ hW.out.send1
  have n3 := ldLayD_noLook _ _ _ _ _ _ hW.out.send3
  exact ⟨g', hg',
    ldReqRefLay_cross E Kc pp I a S W Fr κ own Mk val RdN RrN g' hA hGh hF ⟨hQu, n1, n3⟩
      hW.out.maskL hW.out.apartL hW.out.ownT hW.out.apartT c1 c2 hW.whole c4 c5
      (fun m m' h => hc m m' fun n h1 _ => h n h1) hE⟩

end

theorem ldLayD_laid : Spec.ldLayD_laid := by
  intro E Kc _ _ pp _ I _ a b L Q P₀ base hQ
  induction L with
  | nil =>
      intro _ _ h0 β hβ
      simp only [LdRefL.PendD] at hβ
      simp only [LdRefL.LaidJ]
      exact ldLayD_jd P₀ base h0 β hβ
  | snoc L S ih =>
      intro hM hP h0 β hβ
      rw [LdRefL.OK] at hM
      rw [LdRefL.Reads] at hP
      simp only [LdRefL.PendD] at hβ
      simp only [LdRefL.LaidJ]
      refine ldLayD_jd _ _ (fun β hx => ?_) β hβ
      obtain ⟨hc, hn | ⟨β', hβ', hx⟩⟩ := hx
      · exact .base _ (Or.inl (ldLayD_new S β Q hQ hc hn))
      · obtain ⟨g', hg', hC⟩ := ldLayD_cross pp I _ S Q hQ (L.LaidJ base) (L.laidJ_closed base)
          hM.2.body hP.2 β' β (ih hM.1 hP.1 h0 β' hβ') hc hx
        exact .base _ (Or.inr ⟨g', hg', hC⟩)

theorem ldLayD_segs : Spec.ldLayD_segs := by
  intro E Kc _ _ pp _ I a b L Q P₀ base hQ
  induction L with
  | nil => intro _ _ _ _; simp only [LdRefL.LayJ]
  | snoc L S ih =>
      intro hM hP h0 hZ
      rw [LdRefL.OK] at hM
      rw [LdRefL.Reads] at hP
      simp only [LdRefL.LayD] at hZ
      simp only [LdRefL.LayJ]
      haveI : Nonempty I.C.E0.Str := hZ.2.1
      exact ⟨ih hM.1 hP.1 h0 hZ.1,
        ldLayD_enter E Kc I S.A Q pp _ S.f S.g S.m S.back (L.LaidJ base) (L.PendD Q pp P₀)
          (L.laidJ_closed base) (ldLayD_laid E Kc pp I _ _ L Q P₀ base hQ hM.1 hP.1 h0) hZ.2⟩

end Cb
