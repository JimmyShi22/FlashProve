-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/PubLate.lean: under the hypotheses below, an adversary without violations has the same
output distribution against two challengers: mode I (`world true`) of the challenger that publishes
a function of the key at the setup (`VCBP`), and the challenger in the late language (`chalLBP`;
both: Compile/Batch/PubChall.lean) (the modes: Rom/Defer.lean; words of this library:
lean/GLOSSARY.md).

  `hopLateBP`  From `Spec.lateCpB` and `Spec.latePpB` (Compile/Batch/SpecLate.lean), which are used
               as they are: the first gives equal outputs of the committer's two programs, key
               included, so the published values are equal. Further hypotheses: `L.Wired`,
               `Coherent`, `W.OKG`, `GrFitPB W`.
-/
import Compile.Batch.HopLate
import Compile.Batch.PubReal

noncomputable section

namespace Compile.Batch
open Iop Rom Prob
open Compile.GlueB (GCall GAdm)
open Compile.Life2 (virt up)
open Compile.DefC (virtL late_virt)

variable {I X V : Type} {lam : ℕ} {L : BatchProtocol I X}

variable (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (pw : IVK lam L → WKey lam L → V) (i : I)

theorem step_own_LBP (k : IskH lam L) (N₀ : ℕ) (b : ZKCP.Gen.Batch X Unit) (h : hasOwn b = true) :
    (chalLBP W WP p pw i).step (some (k, N₀)) (.batch b) = LStep.fresh 0 fun t₀ =>
      (virtL N₀ (t₀ + 1 - N₀) (PpL W WP p k (ownFlag b) (reqs b))).bind fun πs =>
          LStep.pure (replyOfP V b πs, some (k, N₀)) := by
  show (if hasOwn b then _ else _) = _
  rw [h, if_pos rfl]

theorem step_none_LBP (k : IskH lam L) (N₀ : ℕ) (b : ZKCP.Gen.Batch X Unit) (h : hasOwn b = false) :
    (chalLBP W WP p pw i).step (some (k, N₀)) (.batch b) = LStep.pure (.inr [], some (k, N₀)) := by
  show (if hasOwn b then _ else _) = _
  rw [h]
  rfl

/-- Under the hypotheses below: every step of the challenger is related (`Late`, with `RelB` of
Compile/Batch/HopLate.lean) to the same step of the challenger in the late language. -/
theorem late_stepBP (hC : Spec.lateCpB) (hP : Spec.latePpB) (hL : L.Wired) (hW : W.OKG)
    (hG : GrFitPB W) (hCo : L.onlineBatch.ann.Coherent) (n : ℕ) (Γ : Cx lam W.K L)
    (s s' : Option (IskH lam L × ℕ)) (m : GCall X Unit) (h : RelB W n Γ s s') :
    Late (fun n' Γ' a b => a.1 = b.1 ∧ RelB W n' Γ' a.2 b.2) n Γ
      ((VCBP W WP p pw i).step s m) ((chalLBP W WP p pw i).step s' m) := by
  obtain ⟨rfl, hF, hs⟩ := h
  rcases m with _ | b
  · cases s with
    | some k => exact Late.pure ⟨rfl, rfl, hF, hs⟩
    | none =>
      refine Late.bind (hC I X lam L W WP p i n Γ hL hW hG hF) ?_
      rintro n1 Γ1 o _ ⟨rfl, -, hF1, -, hK⟩
      exact Late.fresh fun t ht =>
        Late.pure ⟨rfl, rfl, hF1.mono (by omega), Nat.le_succ t, hK.ext (Ext.refl _ _) ht⟩
  · cases s with
    | none => exact Late.pure ⟨rfl, rfl, hF, hs⟩
    | some kN =>
      obtain ⟨k, N₀⟩ := kN
      obtain ⟨hN, hK⟩ := hs
      cases hb : hasOwn b
      · rw [HopRP.VCBP_none W WP p pw i k N₀ b hb, step_none_LBP W WP p pw i k N₀ b hb]
        exact Late.pure ⟨rfl, rfl, hF, hN, hK⟩
      · rw [HopRP.VCBP_own W WP p pw i k N₀ b hb, step_own_LBP W WP p pw i k N₀ b hb]
        refine Late.fresh fun t₀ ht₀ => ?_
        have hup : ∀ u, u < N₀ → up N₀ (t₀ + 1 - N₀) u = u := fun u hu => by simp [up, hu]
        have hup' : ∀ v, N₀ ≤ v → up N₀ (t₀ + 1 - N₀) v = v + (t₀ + 1 - N₀) := fun v hv => by
          have : ¬ v < N₀ := by omega
          simp [up, this]
        -- the context as the program sees it
        have hFv : Fut N₀ (fun v => Γ (up N₀ (t₀ + 1 - N₀) v) : Cx lam W.K L) := fun v hv o => by
          show Γ _ o = none
          rw [hup' v hv]
          exact hF _ (by omega) o
        have hKv : IskK (fun v => Γ (up N₀ (t₀ + 1 - N₀) v) : Cx lam W.K L) N₀ k :=
          hK.ext (Ext.of_frame fun t ht => by show Γ _ = Γ t; rw [hup t ht]) le_rfl
        have hv := late_virt N₀ (t₀ + 1 - N₀)
          (hP I X lam L W WP p k (ownFlag b) (reqs b) N₀ _ hL hW hG hCo hFv hKv) Γ (fun _ => rfl)
          le_rfl
        rw [show N₀ + (t₀ + 1 - N₀) = t₀ + 1 by omega] at hv
        refine Late.bind hv ?_
        rintro n' Γ' π _ ⟨hn', rfl, hle, hF', hE'⟩
        refine Late.pure ⟨rfl, rfl, fun u hu o => ?_, by omega, ?_⟩
        · have h1 := hF' (u - (t₀ + 1 - N₀)) (by omega) o
          have h2 : up N₀ (t₀ + 1 - N₀) (u - (t₀ + 1 - N₀)) = u := by rw [hup' _ (by omega)]; omega
          simp only [h2] at h1
          exact h1
        · exact (hKv.ext hE' le_rfl).ext
            (Ext.of_frame fun t ht => by show Γ' t = Γ' _; rw [hup t ht]) le_rfl

/-- Under the hypotheses below: mode I of the challenger that publishes and the challenger in the
late language give the same output, for an adversary none of whose runs against mode I ends with a
violation of the rules for tokens. -/
theorem hopLateBP (hC : Spec.lateCpB) (hP : Spec.latePpB) (hL : L.Wired) (hCo : L.onlineBatch.ann.Coherent)
    (hW : W.OKG) (hG : GrFitPB W) {α : Type}
    (A : Adv (spec lam W.K L) (GCall X Unit) (BInP V lam L) α)
    (hviol : ∀ x ∈ (interact ((VCBP W WP p pw i).world true) A (none, DSt.init _)).support,
      x.2.2.viol = false) :
    (interact ((VCBP W WP p pw i).world true) A (none, DSt.init _)).map Prod.fst =
      (interact (chalLBP W WP p pw i).world A (none, LSt.init _)).map Prod.fst :=
  Rom.DeferTail.lateView _ _ _ _ _ (VCBP W WP p pw i) (chalLBP W WP p pw i) (RelB W)
    (fun n Γ s s' m h => late_stepBP W WP p pw i hC hP hL hW hG hCo n Γ s s' m h) A none none
    ⟨rfl, fun _ _ _ => rfl, trivial⟩ hviol

end Compile.Batch

