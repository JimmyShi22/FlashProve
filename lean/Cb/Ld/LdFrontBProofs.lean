-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdFrontBProofs.lean: the proofs of the statements of Cb/Ld/LdFrontB.lean.

Main names (statements and hypotheses: Cb/Ld/LdFrontB.lean):
  `frontB_forget`: the links of `p.cA sh` are the front's: `(p.cA sh).forget = LdTc.frontC p`.
  `frontB_coh`: its annotations are coherent.
  `frontB_kb`: the moves' own hypotheses and `p.Keys sh N kx ky` (at a batching: its annotated link
    is knowledge sound between the keys at its two ends (some key at every stage between): asked,
    not derived) ⇒ `(p.cA sh).KB N kx ky`: knowledge sound for the vectors with one key (limits: the
    head of Cb/Ld/LdFrontB.lean).
The switch sh: batchings and splittings in every slot (sh = false), or once by the shared part (sh =
true).

Limits: what the head of Cb/Ld/LdFrontB.lean lists as not said is not said here either.
-/
import Cb.Ld.LdFrontB
import Cb.Ld.LdSplitVProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace Front
variable {E : Type} [Field E] [Fintype E] {S : Sig E} {E₀ : ExtSpec}
  {Wp : Type} {x y : FSt S E₀ Wp Unit}

theorem md_l {A B : Joint Unit} (sh : Bool) (l : Link Unit A B) : (md sh l).l = l := by
  cases sh <;> rfl

theorem md_coh {A B : Joint Unit} (sh : Bool) (l : Link Unit A B) : (md sh l).ann.Coherent := by
  cases sh
  · exact RoundSplits.const_coherent (f := RAnn.allLocal) (fun r => RAnn.ofSlot_coherent .lo r) _
  · exact RoundSplits.const_coherent (fun r => RAnn.ofShared_coherent .sh r) _

theorem lo_coh {A B : Joint Unit} (l : Link Unit A B) : l.lo.ann.Coherent :=
  RoundSplits.const_coherent (f := RAnn.allLocal) (fun r => RAnn.ofSlot_coherent .lo r) _

theorem cA_nil (sh : Bool) (x : FSt S E₀ Wp Unit) :
    (Front.nil x).cA sh = .one x.stage.idLink.lo := by rw [cA]
theorem cA_step (sh : Bool) (p : Front x y) (z : FSt S E₀ Wp Unit) f g m back :
    (p.step z f g m back).cA sh = (p.cA sh).snoc (stepL y z f g m back).lo := by rw [cA]
theorem cA_bat (sh : Bool) (B iB Sb sl Z St₀)
    (A₀ : IOR.Rels Unit St₀ E₀ (S.Msg × Wp)) (p : Front x _) :
    (Front.bat B iB Sb sl Z St₀ A₀ p).cA sh =
      (p.cA sh).snoc (md sh (batD B iB Sb sl Z St₀ A₀).link) := by rw [cA]
theorem cA_split (sh : Bool) (G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀) (A₀ : IOR.Rels Unit St₀ E₀ (S.Msg × Wp))
    (Rs dRs) (p : Front x _) :
    (Front.split G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs p).cA sh =
      (p.cA sh).snoc (md sh (splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs).link) := by rw [cA]

end Front

open Front

theorem frontB_forget : Spec.frontB_forget := by
  intro E _ _ S E₀ Wp x y p sh
  unfold LdTc.frontC
  induction p with
  | nil => rw [cA_nil, ChainA.forget_one, prog_nil, LdProg.onto_nil]; rfl
  | step p z f g m back ih =>
      rw [cA_step, ChainA.forget_snoc, ih, prog_step, LdProg.onto_snoc]
      exact (Chain.append_one _ _).symm
  | bat B iB Sb sl Z St₀ A₀ p ih =>
      rw [cA_bat, ChainA.forget_snoc, ih, prog_bat, LdProg.onto_snoc, md_l]
      exact (Chain.append_one _ _).symm
  | split G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs p ih =>
      rw [cA_split, ChainA.forget_snoc, ih, prog_split, LdProg.onto_snoc, md_l]
      exact (Chain.append_one _ _).symm

theorem frontB_coh : Spec.frontB_coh := by
  intro E _ _ S E₀ Wp x y p sh
  induction p with
  | nil => rw [cA_nil]; exact (ChainA.coh_one _).2 (lo_coh _)
  | step p z f g m back ih => rw [cA_step]; exact (ChainA.coh_snoc _ _).2 ⟨ih, lo_coh _⟩
  | bat B iB Sb sl Z St₀ A₀ p ih => rw [cA_bat]; exact (ChainA.coh_snoc _ _).2 ⟨ih, md_coh sh _⟩
  | split G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs p ih => rw [cA_split]; exact (ChainA.coh_snoc _ _).2 ⟨ih, md_coh sh _⟩

theorem frontB_kb : Spec.frontB_kb := by
  intro E _ _ S E₀ Wp x y p sh N kx
  induction p with
  | nil =>
      intro ky _ hk
      rw [Keys] at hk
      obtain ⟨F, hF⟩ := hk
      rw [cA_nil]
      refine (ChainA.kb_one _ N kx ky).2
        (link_lo_kb Unit _ _ _ N kx ky F (LdStage.idLink_goodT _).know (fun _ => trivial) ?_)
      rintro a τ b hb
      obtain rfl := Option.some.inj hb
      exact hF _
  | step p z f g m back ih =>
      intro kz hH hk
      rw [prog_step, LdProg.hyp_snoc] at hH
      rw [Keys] at hk
      obtain ⟨ky, h1, F, hF⟩ := hk
      rw [cA_step]
      have hT := (Chain.allT_one _).1
        (ldSeg_mvT E Unit _ _ (LdMv.step _ z.stage f g m back) hH.2
          (by intro e; cases e) (by intro e; cases e))
      exact (ChainA.kb_snoc _ _ N kx kz).2
        ⟨ky, ih ky hH.1 h1, link_lo_kb Unit _ _ _ N ky kz F hT.know (fun _ => trivial) hF⟩
  | bat B iB Sb sl Z St₀ A₀ p ih =>
      intro kz hH hk
      rw [prog_bat, LdProg.hyp_snoc] at hH
      rw [Keys] at hk
      obtain ⟨ky, h1, h2⟩ := hk
      rw [cA_bat]
      exact (ChainA.kb_snoc _ _ N kx kz).2 ⟨ky, ih ky hH.1 h1, h2⟩
  | split G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs p ih =>
      intro kz hH hk
      rw [prog_split, LdProg.hyp_snoc] at hH
      rw [Keys] at hk
      obtain ⟨ky, h1, F, hc, hF⟩ := hk
      rw [cA_split]
      refine (ChainA.kb_snoc _ _ N kx kz).2 ⟨ky, ih ky hH.1 h1, ?_⟩
      cases sh with
      | false =>
          refine ldSplV_lo_kb E Unit (splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs) N ky kz
            (fun κ' => F κ' (((), 0), (), ())) hH.2 fun a τ b hb => ?_
          rw [hF a τ b hb]
          exact hc rfl _ _ _
      | true =>
        exact ldSplV_sh_kb E Unit (splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs) N ky kz F hH.2 hF

end Cb
