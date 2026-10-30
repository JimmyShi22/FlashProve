-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/PullCProofs.lean: the proofs of the statements of Ior/PullC.lean: knowledge soundness of a
reduction behind maps of messages.

`know_pullC` is `Carry.doomed` (Iop/CarryProofs.lean) at the goal of `Reduction.Know`: a transcript
without an image is rejected, so the goal holds of it; a transcript with an image has the image's
output and extracted witness. `know_pullC_seq`: `Know.seq` (Ior/Know.lean), then `know_pullC` with
the fibres and errors of `F.app G`.

Main names: one theorem for each statement, of the same name.

Limits: those in the head of Ior/PullC.lean.

Terms: lean/GLOSSARY.md.

-/
import Ior.PullC
import Iop.CarryProofs

set_option autoImplicit false

namespace Iop
open Prob Reduction

theorem know_pullC : Spec.know_pullC := by
  intro A B WA WB K s F ws on RA RB ext ε d hK hF a ha
  refine Carry.doomed (F a) ws (hF a ha) ε _
    (fun τ' => ∀ b w, K.out a τ' = some b → RB b w → RA a (ext a τ' w)) ?_ ?_ (hK a ha)
  · intro τ hτ b w hb _
    have hb' : ((F a).tr τ).bind (K.out a) = some b := hb
    rw [hτ] at hb'
    cases hb'
  · intro τ τ' hτ h b w hb hw
    have hb' : ((F a).tr τ).bind (K.out a) = some b := hb
    rw [hτ] at hb'
    have he : K.extC s F ext d a τ w = ext a τ' w := by
      unfold Reduction.extC
      rw [hτ]
    rw [he]
    exact h b w hb' hw

theorem know_pullC_seq : Spec.know_pullC_seq := by
  intro A B C WA WB WC K₁ K₂ s₁ s₂ F G ws₁ ws₂ on₁ on₂ RA RB RC e₁ e₂ ε₁ ε₂ d h₁ h₂ hon hF hG
  have h := know_pullC A C WA WC (K₁.seq K₂) (s₁ ++ s₂) (fun a => (F a).app (G a))
    (Err.app ws₁ ws₂) on₁ RA RC (extSeq K₁ K₂ e₁ e₂ d) (Err.app ε₁ ε₂) d (Know.seq h₁ h₂ hon d)
    fun a ha => Carry.fib_app (F a) (G a) ws₁ ws₂ (hF a ha) fun τ => hG a τ ha
  intro a ha
  have h' := h a ha
  rwa [show mulErr (s₁ ++ s₂) (K₁.seq K₂).shape (Err.app ws₁ ws₂) (Err.app ε₁ ε₂) =
    Err.app (mulErr s₁ K₁.shape ws₁ ε₁) (mulErr s₂ K₂.shape ws₂ ε₂) from
      mulErr_app (F a) s₂ K₂.shape ws₁ ws₂ ε₁ ε₂] at h'

theorem red_pullC : Spec.red_pullC := by
  intro Xi Xo Ei Eo R s F im V hIm a τ
  show (((F (a.1, a.2)).tr τ).bind (R.out a.1 a.2)).map (fun xo => (xo, im a.2 τ)) =
    ((F a).tr τ).bind fun τ' => (R.out a.1 a.2 τ').map fun xo => (xo, R.imp a.2 τ')
  cases hτ : (F a).tr τ with
  | none => rfl
  | some τ' =>
    rw [hIm a τ τ' hτ]
    rfl

theorem know_pullC_ior : Spec.know_pullC_ior := by
  intro Xi Xo Ei Eo R s F im V ws WA WB on RA RB ext ε d hIm hK hF a ha
  refine Doomed.mono _ _ ?_
    (know_pullC _ _ WA WB R.red s F ws on RA RB ext ε d hK hF a ha)
  intro τ h b w hb hw
  exact h b w ((red_pullC Xi Xo Ei Eo R s F im V hIm a τ).symm.trans hb) hw

theorem imp_pullC_app : Spec.imp_pullC_app := by
  intro X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ s₁ s₂ F G im₁ im₂ h₁ h₂ a τ τ' hτ
  rw [← Tr.app_fst_snd τ, Carry.tr_app] at hτ
  cases hf : (F a).tr (Tr.fst τ) with
  | none =>
    rw [hf] at hτ
    cases hτ
  | some τ₁' =>
    rw [hf] at hτ
    cases hg : (G a (Tr.fst τ)).tr (Tr.snd (s := s₁) τ) with
    | none =>
      rw [Option.bind_some, hg] at hτ
      cases hτ
    | some τ₂' =>
      rw [Option.bind_some, hg] at hτ
      obtain rfl : Tr.app τ₁' τ₂' = τ' := Option.some.inj hτ
      show _ = R₂.imp (R₁.imp a.2 (Tr.fst (Tr.app τ₁' τ₂')))
        (Tr.snd (s := R₁.shape) (Tr.app τ₁' τ₂'))
      rw [Tr.fst_app, Tr.snd_app, h₁ a _ _ hf, h₂ a _ _ _ _ hg]

theorem know_pullC_seq_ior : Spec.know_pullC_seq_ior := by
  intro X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ s₁ s₂ F G im V ws₁ ws₂ W₁ W₂ W₃ on₁ on₂ RA RB RC e₁ e₂ ε₁ ε₂ d
    hIm h₁ h₂ hon hF hG
  have h := know_pullC_ior X₁ X₃ E₁ E₃ (R₁.seq R₂) (s₁ ++ s₂) (fun a => (F a).app (G a)) im V
    (Err.app ws₁ ws₂) W₁ W₃ on₁ RA RC (IOR.extSeq R₁ R₂ e₁ e₂ d) (Err.app ε₁ ε₂) d hIm
    (know_seq X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ W₁ W₂ W₃ on₁ on₂ RA RB RC e₁ e₂ ε₁ ε₂ d h₁ h₂ hon)
    fun a ha => Carry.fib_app (F a) (G a) ws₁ ws₂ (hF a ha) fun τ => hG a τ ha
  intro a ha
  have h' := h a ha
  rwa [show mulErr (s₁ ++ s₂) (R₁.seq R₂).shape (Err.app ws₁ ws₂) (Err.app ε₁ ε₂) =
    Err.app (mulErr s₁ R₁.shape ws₁ ε₁) (mulErr s₂ R₂.shape ws₂ ε₂) from
      mulErr_app (F a) s₂ R₂.shape ws₁ ws₂ ε₁ ε₂] at h'

theorem mulErr_toList : Spec.mulErr_toList
  | [], [], _, _, _ => rfl
  | r :: s, _ :: s', (_, _, k), (w, ws), (e, ε) => by
      show e * w :: (mulErr s s' ws ε).toList = e * w :: List.zipWith (· * ·) ε.toList ws.toList
      rw [mulErr_toList s s' (k (r.dOrc, r.dPlain) (Classical.arbitrary r.Chal)) ws ε]
  | [], _ :: _, F, _, _ => nomatch F
  | _ :: _, [], F, _, _ => nomatch F

theorem mulErr_ones_toList : Spec.mulErr_ones_toList
  | [], [], _, _ => rfl
  | r :: s, _ :: s', (_, _, k), (e, ε) => by
      show e * 1 :: (mulErr s s' (Err.ones s) ε).toList = e :: ε.toList
      rw [Nat.mul_one,
        mulErr_ones_toList s s' (k (r.dOrc, r.dPlain) (Classical.arbitrary r.Chal)) ε]
  | [], _ :: _, F, _ => nomatch F
  | _ :: _, [], F, _ => nomatch F

end Iop
