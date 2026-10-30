-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/GrOK.lean: a wire record without proof-of-work bits (`RoundsQueryLayout.OK`, which includes gr0 =
none and grJ = none in every round): every check passes (`pass_ok`), setting the bits to 0 changes
nothing (`zero_ok`), writing nonces into the plain parts changes nothing (`putB_ok`), and (Acc)
(`Honest.Acc`, Iop/InteractiveOracleProof.lean) with a local verifier gives `GrFit` (`fit_ok`). So statements for
wire records that may have such bits cover those without (words of this library: lean/GLOSSARY.md).
-/
import Compile.Batch.SpecGrind

noncomputable section

namespace Compile.Batch
open Iop Rom Prob

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

section NoTest
variable {K : ℕ}

theorem pass_ok :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A),
      RoundsQueryLayout.OK s A W → ∀ ρ, RoundsQueryLayout.pass s A W ρ = true
  | [], _, _, _, _ => rfl
  | _ :: s, (a, A), (w, W), h, (c, ρ) => by
      show (w.pass c && RoundsQueryLayout.pass s A W ρ) = true
      rw [pass_ok s A W h.2 ρ, Bool.and_true]
      unfold WireRB.pass
      rw [h.1.gr0_none, h.1.grJ_none]
      cases a.kind <;> rfl

theorem zero_ok :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A),
      RoundsQueryLayout.OK s A W → ∀ ρ, RoundsQueryLayout.zero s A W ρ = ρ
  | [], _, _, _, _ => rfl
  | _ :: s, (a, A), (w, W), h, (c, ρ) => by
      show (w.zero c, RoundsQueryLayout.zero s A W ρ) = (c, ρ)
      rw [zero_ok s A W h.2 ρ]
      unfold WireRB.zero
      rw [h.1.gr0_none, h.1.grJ_none]
      cases a.kind <;> rfl

theorem putB_ok :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A),
      RoundsQueryLayout.OK s A W → ∀ ph nJ n0 pls, putB s A W ph nJ n0 pls = pls
  | [], _, _, _, _, _, _, _ => rfl
  | _ :: s, (a, A), (w, W), h, ph, nJ, n0, (pl, pls) => by
      unfold putB
      rw [h.1.gr0_none, h.1.grJ_none]
      cases a.kind <;> cases ph <;> simp only [putB_ok s A W h.2]

/-- For `RoundsQueryLayout.OK`: (Acc) and a local verifier (`IsLocal`) give `GrFit`. -/
theorem fit_ok {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} {Wt : Type} (H : BatchHonestProver Q Wt)
    (wq : ProtocolQueryLayout lam K Q) (valid : Wt → Y → Prop) (hw : RoundsQueryLayout.OK Q.loc.shape Q.ann wq.sh)
    (hloc : Q.loc.IsLocal) (hacc : H.one.Acc valid) : GrFit H wq valid where
  wh := fun w x ρ => by rw [zero_ok _ _ _ hw]
  run := fun w x c ρ => by rw [zero_ok _ _ _ hw]; exact ⟨rfl, fun _ => rfl⟩
  reads := fun x ρ pl => by rw [zero_ok _ _ _ hw]
  extReads := fun x ρ => by rw [zero_ok _ _ _ hw]
  readsPut := fun x ρ pl ph nJ n0 => by rw [putB_ok _ _ _ hw]
  acc := fun w x c ρ hv hρ _ nJ n0 τ h1 h2 h3 => by
    rw [putB_ok _ _ _ hw] at h2
    have hr : ((H.one.strat w x c).run ρ).1.rho = ρ := Strat.rho_run _ _
    rw [← hacc w x c ρ hv hρ]
    exact hloc x _ _ τ _ (h1.trans hr.symm) h2 (fun _ _ => rfl) fun p _ => h3 p

end NoTest

end Compile.Batch
