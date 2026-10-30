-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/LkN/KnowAtProofs.lean: the proofs of the statements of Cb/LkN/KnowAt.lean: rules for
`TWhole.KnowAt`.

Proofs only. Two in a row: `know_seq` (Ior/SeqProofs.lean) for each tuple of messages, then
`know_ext_congr` (Ior/KnowColl.lean), which puts `idX` in the composed extractor's place. The round
in which the verifier draws: `piece_draw` (Ior/Draw.lean) at joints whose exact relations are empty,
so that its clauses on an honest prover hold for want of a case. Over a signature: `sigLift_know`
(Cb/Ld/LdSigLiftProofs.lean).
Main names: those of Cb/LkN/KnowAt.lean without `Spec.`.
Limits: those of Cb/LkN/KnowAt.lean.

-/
import Cb.LkN.KnowAt
import Ior.KnowCollRulesFrameProofs
import Cb.Ld.LdSigLiftProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop TWhole IOR Cb.LkN

theorem knowAt_seq : Spec.knowAt_seq := by
  intro K M X₁ X₂ X₃ Wp E₁ E₂ E₃ R₁ R₂ A B C ε₁ ε₂ h₁ h₂
  refine ⟨h₁.point.elim fun p₁ => h₂.point.elim fun p₂ => ⟨Shape.IsPoint.append p₁ p₂⟩,
    h₁.isLocal.seq h₂.isLocal, ?_, fun m => ?_⟩
  · intro a τ c ha hc
    obtain ⟨b, hb, hc'⟩ := Option.bind_eq_some_iff.1 ((IOR.red_seq_out R₁ R₂ a τ).symm.trans hc)
    exact h₂.onOut b _ c (h₁.onOut a _ b ha hb) hc'
  · by_cases hW : Nonempty Wp
    · obtain ⟨d⟩ := hW
      refine know_ext_congr _ _ _ _ _ _ _ _ _ _ _ ?_
        (know_seq _ _ _ _ _ _ R₁ R₂ _ _ _ A.on B.on _ _ _ (idX m) (idX m) ε₁ ε₂ d (h₁.know m)
          (h₂.know m) h₁.onOut)
      intro a τ c w _ hc _
      obtain ⟨b, hb, _⟩ := Option.bind_eq_some_iff.1 ((IOR.red_seq_out R₁ R₂ a τ).symm.trans hc)
      obtain ⟨hx, _⟩ := red_out_eq_some.1 hb
      have e := IOR.extSeq_app R₁ R₂ (idX m) (idX m) d a (Tr.fst τ) (Tr.snd τ) b.1 w hx
      rw [Tr.app_fst_snd] at e
      exact e.symm
    · intro a _
      exact Doomed.of_forall _ _ fun _ _ w _ _ => (hW ⟨w⟩).elim

theorem knowAt_conseq : Spec.knowAt_conseq := by
  intro K K' M Xi Xo Wp Ei Eo R A B A' B' ε h ho hA hB hoB
  exact ⟨h.point, h.isLocal, fun a τ b ha hb => hoB b (h.onOut a τ b (ho a ha) hb),
    fun m => (h.know m).conseq ho (fun a w ha hw => hA a (m, w) ha hw) fun b w hw => hB b (m, w) hw⟩

theorem knowAt_post : Spec.knowAt_post := by
  intro K M Xi Xo Xo' Wp Ei Eo R φ A B C ε h hon hrel
  refine ⟨h.point, h.isLocal.post _ _ (extMap_isLocal.1 _), ?_, fun m a ha => ?_⟩
  · intro a τ b ha hb
    obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
    obtain ⟨xo, hxo, hf⟩ := Option.bind_eq_some_iff.1 h1
    have h0 := h.onOut a τ (xo, R.imp a.2 τ) ha (red_out_eq_some.2 ⟨hxo, rfl⟩)
    rw [show b = (φ xo, R.imp a.2 τ) from Prod.ext (Option.some.inj hf).symm h2]
    exact hon _ _ h0
  · refine Doomed.mono _ _ ?_ (h.know m a ha)
    intro τ hτ b w hb hw
    obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
    obtain ⟨xo, hxo, hf⟩ := Option.bind_eq_some_iff.1 h1
    have hb0 : R.red.out a τ = some (xo, R.imp a.2 τ) := red_out_eq_some.2 ⟨hxo, rfl⟩
    rw [show b = (φ xo, R.imp a.2 τ) from Prod.ext (Option.some.inj hf).symm h2] at hw
    exact hτ _ w hb0 (hrel _ _ _ (h.onOut a τ _ ha hb0) hw)

theorem knowAt_pre : Spec.knowAt_pre := by
  intro K M Xi Xi' Xo Wp Ei Eo R φ A' A B ε h hon hrel
  refine ⟨h.point, h.isLocal.pre _ _ (extMap_isLocal.1 _), ?_, fun m a ha => ?_⟩
  · intro a τ b ha hb
    obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
    exact h.onOut (φ a.1, a.2) τ b (hon _ _ ha) (red_out_eq_some.2 ⟨h1, h2⟩)
  · refine Doomed.mono _ _ ?_ (h.know m (φ a.1, a.2) (hon _ _ ha))
    intro τ hτ b w hb hw
    obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
    exact hrel _ _ _ ha (hτ b w (red_out_eq_some.2 ⟨h1, h2⟩) hw)

theorem knowAt_draw : Spec.knowAt_draw := by
  intro K M X X' Ex Wp D _ _ nx A A' err hon hcnt
  have g := (piece_draw Unit X X' Ex Empty D nx
    ⟨fun _ _ _ => False, fun _ _ => False, A.on, fun _ => ()⟩
    ⟨fun _ _ _ => False, fun _ _ => False, A'.on, fun _ => ()⟩ (Fintype.card D) (fun _ => True)
    (fun _ _ _ _ h => h) hon (fun _ => rfl) fun _ _ _ => cnt_le_card _).good
  exact ⟨g.point, g.isLocal, g.onOut, fun m =>
    (piece_draw Unit X X' Ex Wp D nx
      ⟨fun _ _ _ => False, fun a wp => A.relR a (m, wp), A.on, fun _ => ()⟩
      ⟨fun _ _ _ => False, fun a wp => A'.relR a (m, wp), A'.on, fun _ => ()⟩ err (fun _ => True)
      (fun _ _ _ _ h => h) hon (fun _ => rfl) fun x y h => hcnt x y m h).good.know⟩

theorem knowAt_chain : Spec.knowAt_chain := by
  intro K M Wp Ex X R ε A n
  induction n with
  | zero => exact fun h => h 0 (le_refl _)
  | succ n ih =>
      intro h
      exact knowAt_seq K M _ _ _ Wp Ex Ex Ex _ _ (A 0) (A (n + 1)) (A (n + 1 + 1)) _ _
        (ih fun l hl => h l (Nat.le_succ_of_le hl)) (h (n + 1) (le_refl _))

theorem knowAt_sig : Spec.knowAt_sig := by
  intro E _ S Kc St St' Wp E₀ E₀' R A B ε h
  refine ⟨sigLift_know E S Kc St St' Wp Wp E₀ E₀' R A B idX ε h.know, ?_⟩
  intro a τ b ha hb
  obtain ⟨h1, h2, h3⟩ := keep_red_out R S.Smp S.ext a τ b hb
  refine ⟨?_, h.onOut (a.1.1, a.2.1) τ (b.1.1, b.2.1) ha.2 h3⟩
  rw [h1, h2]
  exact ha.1

theorem knowAt_andW : Spec.knowAt_andW := fun _ _ _ _ _ _ _ _ _ _ _ _ h =>
  ⟨h.point, h.isLocal, h.onOut, fun m a ha =>
    Doomed.mono _ _ (fun _ hτ b w hb hw => ⟨hτ b w hb hw.1, hw.2⟩) (h.know m a ha)⟩

theorem knowAt_of_good : Spec.knowAt_of_good := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ g =>
  ⟨g.point, g.isLocal, g.onOut, g.know⟩

end Cb
