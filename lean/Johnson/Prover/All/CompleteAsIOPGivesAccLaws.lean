-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Prover/All/CompleteAsIOPGivesAccLaws.lean: the proof of PartsGiveCompilerPremise
(Johnson/Prover/All/CompleteAsIOPForTheCompiler.lean). It states no goal.

How. A rejected transcript that is the run but for nonces is a failure, so outside the failures the
verifier accepts (acceptedOff). The set that SetsSmall measures, with the work bits set to 0, lies
in the failures (smallOff): an abort is a failure.
-/
import Johnson.Prover.All.CompleteAsIOPForTheCompiler

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

section One
variable {Y : Type} {E : ExtSpec} {Q : InteractiveOracleProof Y E} {Wt : Type} {H : Honest Q Wt}
  {work : WorkBits Q.shape} {y : E.Str} {w : Wt} {x : Y} {c : H.Coin}

/-- Outside a set that holds the failures the verifier accepts the run, whatever the nonces. -/
theorem acceptedOff {B : Set (Rho Q.shape)} (hB : ∀ ρ, FailsAt H work y w x c ρ → ρ ∈ B)
    (τ : Tr Q.shape) (hs : work.sameButForNonces ((H.strat w x c).run τ.rho).1 τ)
    (hn : τ.rho ∉ B) : Q.accept x y τ = true := by
  by_contra hne
  exact hn (hB _ (Or.inr ⟨τ, hs, by simpa using hne⟩))

/-- The abort set with the failures is rare at the challenges that pass. -/
theorem smallOff {error : ℝ≥0∞} {S : Set (Rho Q.shape)} (hS : ∀ ρ ∈ S, FailsAt H work y w x c ρ)
    (hr : chanceAtPassing work (FailsAt H work y w x c) ≤ error) :
    pr (unif (Rho Q.shape)) {ρ | work.cleared ρ ∈ S} ≤ error := by
  have hb : pr (unif (Rho Q.shape)) {ρ | FailsAt H work y w x c (work.cleared ρ)} ≤ error := hr
  refine le_trans (pr_mono _ ?_) hb
  intro ρ hρ
  exact hS _ hρ

end One

/-- No seed is set aside. -/
theorem noSeedAside {lam K : ℕ} {D : Type} (seed : (Fin K → Dig lam) → D) :
    pr (unif (Fin K → Dig lam)) {a | seed a ∈ (∅ : Set D)} ≤ 0 := by
  have e : {a : Fin K → Dig lam | seed a ∈ (∅ : Set D)} = ∅ :=
    Set.eq_empty_of_forall_notMem fun _ h => h
  rw [e, pr_empty]

/-- **At every coin, the parts give AccLaws.** -/
theorem partsGiveCompilerPremise : PartsGiveCompilerPremise := by
  intro Index Request lam L Bd aT aL prover W S Relation offlineError linkError onlineError hP hC
  refine ⟨fun i r₁ x d hy => ⟨?_, ?_, ?_, ?_⟩, fun i r₁ x d hy => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro e₁ _ τ _ hs hn
    exact acceptedOff (H := prover.offlineProver) (work := (partsWorkOfWire (aT := aT) (aL := aL) W).offline)
      (fun ρ h => Or.inr h) τ hs hn
  · intro e₁ e₂ _ _ τ _ hs hn
    exact acceptedOff (H := prover.linkProver) (work := (partsWorkOfWire (aT := aT) (aL := aL) W).link)
      (fun ρ h => Or.inr h) τ hs hn
  · intro e₂ _ τ _ hs hn
    exact acceptedOff (H := prover.onlineProver) (work := (partsWorkOfWire (aT := aT) (aL := aL) W).online)
      (fun ρ h => Or.inr h) τ hs hn
  · intro e₂ τ hs
    exact hP.sendsCopyNumber i x d.r e₂ d.n d.κ.2.2 τ hy hs
  · exact noSeedAside S.seed
  · exact noSeedAside S.seed
  · intro e
    refine smallOff (H := prover.offlineProver) (work := (partsWorkOfWire (aT := aT) (aL := aL) W).offline)
      (y := L.encodeIndex i r₁) (w := (i, r₁, e)) (x := L.recOf i r₁ e) (c := d.κ.1) (fun ρ h => ?_)
      (hC.offline i x r₁ e hy d.κ.1)
    rcases h with h | h
    · exact Or.inl h
    · exact h
  · intro e e'
    refine smallOff (H := prover.linkProver) (work := (partsWorkOfWire (aT := aT) (aL := aL) W).link)
      (y := (L.encodeIndex i r₁, L.encodeIndex i d.r)) (w := (i, (r₁, e), (d.r, e')))
      (x := (L.recOf i r₁ e, L.recOf i d.r e')) (c := d.κ.2.1) (fun ρ h => ?_)
      (hC.link i x r₁ e d.r e' hy d.κ.2.1)
    rcases h with h | h
    · exact Or.inl h
    · exact h
  · intro e
    refine smallOff (H := prover.onlineProver) (work := (partsWorkOfWire (aT := aT) (aL := aL) W).online)
      (y := L.encodeIndex i d.r) (w := (i, d.r, e, d.n)) (x := (x, L.recOf i d.r e)) (c := d.κ.2.2)
      (fun ρ h => ?_) (hC.online i x d.r e d.n hy d.κ.2.2)
    rcases h with h | h
    · exact Or.inl h
    · exact h

end OnBytes.Prover

#print axioms OnBytes.Prover.partsGiveCompilerPremise
