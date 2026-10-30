-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefDigProofs.lean: the statements of Cb/Req1/LdSegRefDig.lean, proved.

The two steps follow by the rule for a change of the base joint (Cb/Ld/LdBatPeelProofs.lean), the
shift by Cb/Ld/LdLkpShiftProofs.lean, the sums by Cb/Req1/LdSegProofs.lean.
What each statement says, and the limits: the head of Cb/Req1/LdSegRefDig.lean.
-/
import Cb.Req1.LdSegRefDig
import Cb.Req1.LdSegRefRngProofs
import Cb.Ld.LdLkpShiftProofs
import Cb.Ld.LdZeroAt

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Rng Cb.RngPk Cb.Lkp Cb.LdLkp IOR IOR.Chain
open scoped ENNReal

namespace RngPk

theorem H_pos {p : RngPar} (h : p.OK) : 0 < p.H := by
  rcases Nat.eq_zero_or_pos p.H with h0 | h0
  · have h1 := h.qH
    have h2 := h.B1
    have h3 := h.BD
    rw [h0] at h1
    simp at h1
    omega
  · exact h0

end RngPk

theorem ldSegRef_dg_allIn : Spec.ldSegRef_dg_allIn := by
  intro E Kc E₀ Wp _ Q x m h hq hH hK
  have k0 := ldRng_keys E Q.D.p Q.K Q.e Q.v Q.d Q.D.p.q (Q.dg m).1 h.q0 hq hK
  have k1 := ldRng_keys E Q.D.p Q.K Q.e Q.v Q.d Q.D.p.H (Q.dg m).2 (H_pos h) hH hK
  constructor
  · intro hA
    have a0 : InTable Q.v Q.d (rngKeys Q.D.p Q.e (Q.dg m).1) (tabMod Q.D.p.q) :=
      hA 0 (show 0 < 2 ^ 1 by norm_num)
    have a1 : InTable Q.v Q.d (rngKeys Q.D.p Q.e (Q.dg m).2) (tabMod Q.D.p.H) :=
      hA 1 (show 1 < 2 ^ 1 by norm_num)
    exact ⟨k0.1 a0, k1.1 a1⟩
  · rintro ⟨h0, h1⟩ f hf
    have hf2 : f < 2 ^ 1 := hf
    norm_num at hf2
    interval_cases f
    · exact k0.2 h0
    · exact k1.2 h1

namespace LdDgP
variable {E Kc : Type} [Field E] [Fintype E] {E₀ : ExtSpec} {Wp : Type} (Q : LdDgP E Kc E₀ Wp)

theorem stepA_hyp (h : Q.D.p.OK) (hP : Q.Places) (hq : Q.D.p.q ≤ 2 ^ Q.d)
    (hH : Q.D.p.H ≤ 2 ^ Q.d) (hK : Q.K ≤ 2 ^ Q.v) : Q.stepA.Hyp :=
  ldSeg_step E Kc Q.D.s4 Q.u0 _ _ _ _
    (ldPeel_base E Kc _ _ _ _ Q.T E₀ E₀ Q.D.s4.A Q.u0.A id (ExtMap.id E₀) (fun _ w => w.2)
      (fun _ w => w.2) (extMap_isLocal.1 _)
    (fun st y w hw => by
      have hw' : (Out Q.D.p.D Q.D.p.rdx Q.D.p.q Q.D.p.H (Q.D.r.W st.1) st.2 (Q.D.r.pk (Q.old w.1))
              (Q.D.r.rd (Q.old w.1)) (Q.dg w.1) ∧
            Q.D.A₁.rel st.1 y (Q.old w.1, w.2)) ∧
          Q.vv w.1 = Q.D.mkV (Q.dg w.1) := by
        rw [← hP w.1]
        exact hw
      exact ⟨⟨hw'.1.1.2, hw'.1.2, hw'.2, hw'.1.1.1⟩, (ldSegRef_dg_allIn E Kc _ _ Q st w.1 h hq hH hK).2 hw'.1.1.1⟩) (fun _ _ hh => hh) (fun _ _ => rfl)
    (fun st y w _ hw => by
      have g : Out Q.D.p.D Q.D.p.rdx Q.D.p.q Q.D.p.H (Q.D.r.W st.1) st.2 (Q.D.r.pk (Q.old w.1))
            (Q.D.r.rd (Q.old w.1)) (Q.dg w.1) ∧
          Q.D.A₁.relR (st.1, y) (Q.old w.1, w.2) :=
        ⟨⟨(ldSegRef_dg_allIn E Kc _ _ Q st w.1 h hq hH hK).1 hw.2, hw.1.1⟩, hw.1.2⟩
      rw [← hP w.1] at g
      exact g))

omit [Fintype E] in
theorem tagInj (ht : Q.tag 0 ≠ Q.tag 1) : TagInj Q.sh.g Q.sh.tag := by
  intro f hf f' hf' he
  have h2 : f < 2 ^ 1 := hf
  have h2' : f' < 2 ^ 1 := hf'
  norm_num at h2 h2'
  have he' : Q.tag f = Q.tag f' := he
  interval_cases f <;> interval_cases f'
  · rfl
  · exact absurd he' ht
  · exact absurd he'.symm ht
  · rfl

theorem shift_goodT (ht : Q.tag 0 ≠ Q.tag 1) : Q.shift.GoodT :=
  (ldSeg_lift E Kc Q.u0 _ _ _ (Q.sh.jOut Q.R0) _ _ _ _
      (ldLkpShift_goodAt E Q.X₄ Q.T.Msg Wp Kc E₀ Q.sh Q.R0 (Q.tagInj ht))).2
    (draw_exact_any E₀ _ E Prod.mk _)

omit [Fintype E] in
/-- the claim after the shift is the one lookup claim -/
theorem outC_iff (x : Q.X₄ × E) (y : E₀.Str) (m : Q.T.Msg) :
    Q.sh.outC x m ↔ InTable Q.L.v Q.L.d (Q.L.key x (y, m)) (Q.L.tab x) := by
  show InTable (1 + Q.v) (1 + Q.d) (shKey Q.v (Q.sh.key x.1 m) Q.tag x.2)
      (shTab Q.d (Q.sh.tab x.1) Q.tag x.2) ↔
    InTable (Q.v + 1) (1 + Q.d) (shKey Q.v (Q.sh.key x.1 m) Q.tag x.2)
      (shTab Q.d (Q.sh.tab x.1) Q.tag x.2)
  rw [Nat.add_comm 1 Q.v]

theorem stepB_hyp (mult : Q.X₄ × E → Ms Q.T E₀ → Prop) (hM : Q.Mult mult) : (Q.stepB mult).Hyp :=
  ldSeg_step E Kc Q.u1 (Q.lkS mult) _ _ _ _
    (ldPeel_base E Kc _ _ _ _ Q.T E₀ E₀ Q.u1.A (Q.lkS mult).A id (ExtMap.id E₀) (fun _ w => w.2)
      (fun _ w => w.2) (extMap_isLocal.1 _)
      (fun st y w hw =>
        ⟨hw.1, ⟨(Q.outC_iff st y w.1).1 hw.2, trivial⟩, hM st y w.1 hw.1.2.2.2 hw.1.2.2.1⟩)
      (fun _ _ hh => hh) (fun _ _ => rfl)
      (fun st y w _ hw => ⟨hw.1, (Q.outC_iff st y w.1).2 hw.2.1⟩))

end LdDgP

theorem ldSegRef_dg_hyp : Spec.ldSegRef_dg_hyp := by
  intro E Kc E₀ Wp _ _ Q mult ent n lk h hP hq hH hK ht hM hl
  unfold LdDgP.prog LdDgP.pre
  rw [LdProg.hyp_snoc, LdProg.hyp_snoc, LdProg.hyp_snoc, LdProg.hyp_snoc]
  refine ⟨⟨⟨⟨?_, Q.stepA_hyp h hP hq hH hK⟩, ?_⟩, Q.stepB_hyp mult hM⟩, hl⟩
  · rw [LdProg.Hyp]
    trivial
  · exact (allB_one Q.shift).2 (goodB_of_goodT' (Q.shift_goodT ht))

theorem ldSegRef_dg_kinds : Spec.ldSegRef_dg_kinds := by
  intro E Kc E₀ Wp _ _ Q mult ent n lk
  unfold LdDgP.prog LdDgP.pre
  rw [LdProg.all_snoc, LdProg.all_snoc, LdProg.all_snoc, LdProg.all_snoc]
  refine ⟨⟨⟨⟨?_, Or.inr (Or.inr rfl)⟩, Or.inr (Or.inl rfl)⟩, Or.inr (Or.inr rfl)⟩,
    Or.inr (Or.inl rfl)⟩
  rw [LdProg.All]
  trivial

theorem ldSegRef_dg_zk : Spec.ldSegRef_dg_zk := by
  intro E Kc E₀ Wp _ _ Q mult ent n lk base ht hl
  unfold LdDgP.prog
  rw [LdProg.zk_snoc]
  refine ⟨?_, hl⟩
  unfold LdDgP.pre
  rw [LdProg.zk_snoc, LdProg.zk_snoc, LdProg.zk_snoc]
  refine ⟨⟨⟨(LdProg.zk_nil _ _).2 trivial, ?_⟩,
      okGiven_of_allT Kc _ _ _ _ ((allT_one Q.shift).2 (Q.shift_goodT ht))⟩,
    ?_⟩
  · unfold LdDgP.stepA
    rw [LdMv.Zk]
    trivial
  · unfold LdDgP.stepB
    rw [LdMv.Zk]
    trivial

theorem ldSegRef_dg_sub : Spec.ldSegRef_dg_sub := by
  intro E Kc E₀ Wp _ _ Q mult ent n B hB hn
  have g : IOR.GoodB B.R B.H (Q.T.over (Q.lkS mult).A) (Q.T.over (Q.lkT ent n).A) B.ext B.P :=
    { hB with
      acc := fun x y w c ρ hR hρ =>
          ⟨(hB.acc x y w c ρ hR hρ).1,
            (hB.acc x y w c ρ hR hρ).2.1,
            (hB.acc x y w c ρ hR hρ).2.2.1,
            (hB.acc x y w c ρ hR hρ).2.2.2.1,
            (hB.acc x y w c ρ hR hρ).2.2.2.2,
            hn x y _ _ (hB.acc x y w c ρ hR hρ).1⟩ }
  exact goodB_cf _ _ _ _ _ _ _ _ _ _ _ _ _ g

theorem ldSegRef_dg_nums : Spec.ldSegRef_dg_nums := by
  intro E Kc E₀ Wp _ _ Q mult ent n lk
  obtain ⟨_, _, _, _, _, hp⟩ := ldSeg_rounds E Kc
  have a1 := hp Q.D.s4 Q.u0 (sideF Q.T id) (sideG Q.T (ExtMap.id E₀))
    (sideM Q.T id fun _ w => w.2) (sideB Q.T fun _ w => w.2)
  have a3 := hp Q.u1 (Q.lkS mult) (sideF Q.T id) (sideG Q.T (ExtMap.id E₀))
    (sideM Q.T id fun _ w => w.2) (sideB Q.T fun _ w => w.2)
  have c2 : (LdMv.sub Q.u0 Q.u1 (.one Q.shift)).chain = .one Q.shift := by rw [LdMv.chain]
  have c4 : (LdMv.sub (Q.lkS mult) (Q.lkT ent n) lk).chain = lk := by rw [LdMv.chain]
  unfold LdDgP.prog LdDgP.pre LdDgP.stepA LdDgP.stepB
  refine ⟨?_, ?_, ?_⟩
  · rw [LdProg.nAll_snoc, LdProg.nAll_snoc, LdProg.nAll_snoc, LdProg.nAll_snoc, LdProg.nAll_nil,
      a1.1, a3.1, c2, c4, nAll_one]
    show 0 + 0 + 1 + 0 + lk.nAll = 1 + lk.nAll
    omega
  · rw [LdProg.pBad_snoc, LdProg.pBad_snoc, LdProg.pBad_snoc, LdProg.pBad_snoc, LdProg.pBad_nil,
      a1.2.2.1, a3.2.2.1, c2, c4, pBad_one]
    show (0 : ℝ≥0∞) + 0 + 0 + 0 + lk.pBad = lk.pBad
    simp
  · rw [LdProg.pHid_snoc, LdProg.pHid_snoc, LdProg.pHid_snoc, LdProg.pHid_snoc, LdProg.pHid_nil,
      a1.2.2.2, a3.2.2.2, c2, c4, pHid_one]
    show (0 : ℝ≥0∞) + 0 + 0 + 0 + lk.pHid = lk.pHid
    simp

end Cb
