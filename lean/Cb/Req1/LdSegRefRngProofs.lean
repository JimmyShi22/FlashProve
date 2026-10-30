-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefRngProofs.lean: the statements of Cb/Req1/LdSegRefRng.lean, proved.

The proofs use Cb/Ld/LdReadProofs.lean, Cb/Ld/LdRngProofs.lean (the blocks) and
Cb/Req1/LdSegStep.lean, Cb/Req1/LdSegProofs.lean, Cb/Req1/LdReqProofs.lean (how a step and a link
enter a list of moves; the sums).
What each statement says, and the limits: the head of Cb/Req1/LdSegRefRng.lean.
-/
import Cb.Req1.LdSegRefRng
import Cb.Ld.LdReadProofs
import Cb.Req1.LdSegStep

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Rng Cb.RngPk IOR IOR.Chain
open scoped ENNReal

theorem ldSegRef_rr_s2 : Spec.ldSegRef_rr_s2 := fun _ _ _ _ _ _ => rfl

theorem ldSegRef_rr_s4 : Spec.ldSegRef_rr_s4 := fun _ _ _ _ _ _ =>
  ⟨fun _ _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩

namespace LdRrD
variable {E Kc : Type} [Field E] [Fintype E] {E₀ : ExtSpec} {Wp : Type} (D : LdRrD E Kc E₀ Wp)

omit [Fintype E] in
/-- under `h`, the draw has the whole bundle between the joints over the oracle messages -/
theorem draw_goodT (h : D.p.OK) :
    IOR.GoodT D.draw.R D.draw.H (D.s2.S.over D.s2.A) (D.s3.S.over D.s3.A) D.draw.ext D.draw.P :=
  ldRng_draw E D.St Kc Wp E₀ D.p (D.S.sum D.N) D.r D.A₁ h

/-- the step in which v is derived -/
theorem derive_hyp : D.derive.Hyp :=
  ldSeg_step E Kc D.s3 D.s3v _ _ _ _
    (ldPeel_base E Kc _ _ _ _ (D.S.sum D.N) E₀ E₀ D.s3.A D.s3v.A id (ExtMap.id E₀)
      (fun _ w => (w.2, D.mkV w.2.2)) (fun _ w => w.2.1) (extMap_isLocal.1 _)
      (fun _ _ _ h => ⟨h, rfl⟩) (fun _ _ h => h) (fun _ _ => rfl) (fun _ _ _ _ h => h))

end LdRrD

theorem ldSegRef_rr_hyp : Spec.ldSegRef_rr_hyp := by
  intro E Kc E₀ Wp _ _ pp _ D h hU h1 h3
  unfold LdRrD.prog
  rw [LdProg.hyp_snoc, LdProg.hyp_snoc, LdProg.hyp_snoc, LdProg.hyp_snoc, LdProg.hyp_snoc]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, h1⟩, ?_⟩, D.derive_hyp⟩, h3⟩
  · rw [LdProg.Hyp]
    trivial
  · exact ldSeg_step E Kc D.s0 D.s1 _ _ _ _
      (ldRead_step E D.St Kc Wp D.J pp E₀ D.p D.S D.c D.cl D.A₀ h hU)
  · exact (ldSeg_one E Kc D.s2 D.s3 D.draw (D.draw_goodT h)).1

theorem ldSegRef_rr_kinds : Spec.ldSegRef_rr_kinds := by
  intro E Kc E₀ Wp _ _ D
  unfold LdRrD.prog
  rw [LdProg.all_snoc, LdProg.all_snoc, LdProg.all_snoc, LdProg.all_snoc, LdProg.all_snoc]
  refine ⟨⟨⟨⟨⟨?_, Or.inr (Or.inr rfl)⟩, Or.inl rfl⟩, Or.inr (Or.inl rfl)⟩, Or.inr (Or.inr rfl)⟩,
    Or.inl rfl⟩
  rw [LdProg.All]
  trivial

theorem ldSegRef_rr_zk : Spec.ldSegRef_rr_zk := by
  intro E Kc E₀ Wp _ _ D base h
  unfold LdRrD.prog
  rw [LdProg.zk_snoc, LdProg.zk_snoc, LdProg.zk_snoc, LdProg.zk_snoc, LdProg.zk_snoc]
  refine ⟨⟨⟨⟨⟨(LdProg.zk_nil _ _).2 trivial, ?_⟩, ?_⟩,
        (ldSeg_one E Kc D.s2 D.s3 D.draw (D.draw_goodT h)).2 _⟩,
      ?_⟩,
    ?_⟩
  · rw [LdMv.Zk]
    trivial
  · rw [LdMv.Zk]
    trivial
  · unfold LdRrD.derive
    rw [LdMv.Zk]
    trivial
  · rw [LdMv.Zk]
    trivial

theorem ldSegRef_rr_nums : Spec.ldSegRef_rr_nums := by
  intro E Kc E₀ Wp _ _ D
  obtain ⟨hs, _, _, _, _, hp⟩ := ldSeg_rounds E Kc
  have a1 := hp D.s0 D.s1 (fun x => some x) (ExtMap.id D.s0.Ex)
    (readM D.p D.S D.c D.A₀) fun _ w => (w.1, w.2.1)
  have a2 := hs D.s1 D.d1
  have a4 := hs D.s3v D.d3
  have a5 := hp D.s3 D.s3v (sideF (D.S.sum D.N) id) (sideG (D.S.sum D.N) (ExtMap.id E₀))
    (sideM (D.S.sum D.N) id fun _ w => (w.2, D.mkV w.2.2)) (sideB (D.S.sum D.N) fun _ w => w.2.1)
  have c2 : (LdMv.send D.s1 D.d1).chain = .one D.d1.link := by rw [LdMv.chain]
  have c3 : (LdMv.sub D.s2 D.s3 (.one D.draw)).chain = .one D.draw := by rw [LdMv.chain]
  have c4 : (LdMv.send D.s3v D.d3).chain = .one D.d3.link := by rw [LdMv.chain]
  unfold LdRrD.prog LdRrD.derive
  refine ⟨?_, ?_, ?_⟩
  · rw [LdProg.nAll_snoc, LdProg.nAll_snoc, LdProg.nAll_snoc, LdProg.nAll_snoc, LdProg.nAll_snoc,
      LdProg.nAll_nil, a1.1, a5.1, c2, c3, c4, nAll_one, nAll_one, nAll_one, a2.1, a4.1]
    rfl
  · rw [LdProg.pBad_snoc, LdProg.pBad_snoc, LdProg.pBad_snoc, LdProg.pBad_snoc,
      LdProg.pBad_snoc, LdProg.pBad_nil, a1.2.2.1, a5.2.2.1, c2, c3, c4, pBad_one, pBad_one,
      pBad_one, a2.2.2.1, a4.2.2.1]
    show (0 : ℝ≥0∞) + 0 + 0 + 0 + 0 + 0 = 0
    simp
  · rw [LdProg.pHid_snoc, LdProg.pHid_snoc, LdProg.pHid_snoc, LdProg.pHid_snoc,
      LdProg.pHid_snoc, LdProg.pHid_nil, a1.2.2.2, a5.2.2.2, c2, c3, c4, pHid_one, pHid_one,
      pHid_one, a2.2.2.2, a4.2.2.2]
    show (0 : ℝ≥0∞) + 0 + 0 + D.p.pWin + 0 + 0 = D.p.pWin
    simp

end Cb
