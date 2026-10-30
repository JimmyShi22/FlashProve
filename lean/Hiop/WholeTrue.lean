-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/WholeTrue.lean: honest-verifier zero knowledge of the whole object for the true, uncensored
view.

Definitions and statements; the proofs are in Hiop/WholeTrueProof.lean.

Why: in Hiop/Whole.lean what is shown of a run is its "output": where the verifier's randomness ρ
lies in the withheld set of the honest side (Bad ∪ Hid), the whole run is replaced by a notice.
That is the right object after the compilation to a non-interactive argument, where the prover sees
all of ρ before it releases anything, and withholds the string. In the INTERACTIVE object, which is
what the work that this protocol builds on (lean/CREDITS.md, "Further work") defines, the earlier
messages of such a run are already out.
Which statement is which:
  Hiop/Whole.lean, `HVZKWhole`: the view with the notice. Error: the simulators' errors z only.
    This is what the compiler takes.
  this file, `HVZKWholeTrue`: the view of the honest run as it is, at every ρ, never censored
    (`trueHost`). Error: for each run, the probability u that ρ is withheld or the run simulator is
    not exact at ρ.
The environments, the bounds, the budget and the type of simulators are those of Hiop/Whole.lean,
word for word; a view that is shown is always "some v".
The simulator is `simWhole` of Hiop/Whole.lean for the run simulators completed on the notice:
where a run simulator says "notice", a fixed view d is shown in its place (`Fill`, `fillSims`): any
d, a function of the instance and of ρ.

Main names:
  `Spec.hvzk_whole_true_of`: from `GoodTrue uT uL uO` (ρ withheld or the simulator not exact:
    probability at most u; for a set J of slots |J|·uO): error
    uT + nenc·uL + (Σ_j sess j)·shown·uO.
    (not all hypotheses are named here: see its statement)
  `Spec.goodTrue_of_good`: `Sims.Good zT zL zO` and the probabilities pT, pL, pO of the withheld
    sets (`Held`; they are three fields of `BatchProtocol.Complete`) give
    `GoodTrue (zT + pT) (zL + pL) (zO + pO)`.
  `Spec.goodTrue_of_exact`: under `Held`, if the run simulators are exact at every ρ outside the
    withheld set (`ExactOff`), then `GoodTrue pT pL pO`: the simulators' errors are not paid twice.
  `Spec.hvzk_whole_true`: the first two together.

Limits: the verifier's reads are shown at every ρ, also where it would already have rejected. What
the honest prover sends on the withheld set is whatever the honest side of the interface sends there
(that work fixes these messages); the bound holds for any.
This is the honest bound, not a better simulator: on the withheld set nothing is simulated, its
probability is paid. The other differences from the definition of that work are
those of the header of Hiop/Whole.lean but the fifth.

Terms: lean/GLOSSARY.md.
-/
import Hiop.Whole

set_option autoImplicit false

noncomputable section

namespace Hiop
open Prob Iop Compile.Lifetime Compile.BatchLife
open scoped ENNReal

/-! ## 1. Runs that are never censored -/

section Runs
variable {Y X : Type} {E : ExtSpec} {Wt : Type}

/-- The true view at ρ: the disclosed view of the honest run, whether or not ρ is withheld. A
random variable over the prover's coins. -/
def trueView {Q : InteractiveOracleProof Y E} (H : Honest Q Wt) (w : Wt) (y : Y) (ρ : Rho Q.shape) : PMF (DView Q) :=
  (unif H.Coin).map fun c => Q.dview y (H.ext w) ((H.strat w y c).run ρ).1

/-- A run: uniform verifier randomness, fresh prover coins, the true view. -/
def sessTrue {Q : InteractiveOracleProof Y E} (H : Honest Q Wt) (w : Wt) (y : Y) : PMF (Sess Q) :=
  (unif (Rho Q.shape)).bind fun ρ => (trueView H w y ρ).map fun v => (ρ, some v)

/-- The true views of the slots of J (none only at an empty slot). -/
def btrueView {Q : BatchInteractiveOracleProof X E} (H : BatchHonestProver Q Wt) {N : ℕ} (w : Wt) (x : Fin N → Option X)
    (ρ : BRho N Q.loc.shape Q.ann) (J : Finset (Fin N)) :
    PMF (J → Option (DView Q.loc)) :=
  (unif (H.Coin0 × (Fin N → H.Coin))).map fun c => fun j =>
    (x j).map fun xj =>
      Q.loc.dview xj (H.ext w) ((H.one.strat w xj (c.1, c.2 j)).run (ρ.slot j.1)).1

def bsessTrue {Q : BatchInteractiveOracleProof X E} (H : BatchHonestProver Q Wt) {N : ℕ} (w : Wt)
    (x : Fin N → Option X) (J : Finset (Fin N)) : PMF (BSess Q J) :=
  (unif (BRho N Q.loc.shape Q.ann)).bind fun ρ =>
    (btrueView H w x ρ J).map fun o => (fun j => ρ.slot j.1, o)

/-- A run simulator, completed on the notice by the view d. -/
def fillSim {Q : InteractiveOracleProof Y E} (Sim : SimOf Q) (d : Y → Rho Q.shape → DView Q) : SimOf Q :=
  fun y ρ a => (Sim y ρ a).map fun o => some (o.getD (d y ρ))

def fillBSim {Q : BatchInteractiveOracleProof X E} {N : ℕ} (Sim : BSimOf Q N)
    (d : X → Rho Q.loc.shape → DView Q.loc) : BSimOf Q N :=
  fun J xs ρs a => (Sim J xs ρs a).map fun o => fun j => some ((o j).getD (d (xs j) (ρs j)))

end Runs

variable {I X : Type}

/-- What is shown in the place of a notice, for each of the three protocols. -/
structure Fill (L : BatchProtocol I X) where
  T  : Unit → Rho L.offline.shape → DView L.offline
  Lk : Unit → Rho L.link.shape → DView L.link
  B  : X → Rho L.onlineBatch.loc.shape → DView L.onlineBatch.loc

def fillSims {L : BatchProtocol I X} (Sm : Sims L) (d : Fill L) : Sims L where
  T := fillSim Sm.T d.T
  Lk := fillSim Sm.Lk d.Lk
  B := fillBSim Sm.B d.B

/-- The real side on the index i, never censored: realHost of Hiop/Whole.lean with the true
views. -/
def trueHost (L : BatchProtocol I X) (i : I) : Host L where
  σ := ℕ × (ℕ → L.EncodingRandomness)
  off := (unif L.EncodingRandomness).bind fun r => (sessTrue L.honestOfflineProver (i, r) ()).map fun a => (a, (0, fun _ => r))
  fresh := fun s =>
    (unif L.EncodingRandomness).bind fun r =>
      (sessTrue L.honestLinkProver (i, s.2 0, r) ()).map fun a => (a, (s.1 + 1, Function.update s.2 (s.1 + 1) r))
  session := fun s e J xs rest => (bsessTrue L.honestOnlineBatchProver (i, s.2 e) (vec J xs rest) J).map fun a => (a, s)
  read := fun s e p => PMF.pure (L.encodeIndex i (s.2 e) p, s)

/-- Honest-verifier zero knowledge of the whole object, for the true view. -/
def HVZKWholeTrue (L : BatchProtocol I X) (Ryes : I → X → Prop) (B : Bounds) (S : Simulator L) (z : ℝ≥0∞) :
    Prop :=
  ∀ (i : I) (α : Type) (E : Sess L.offline → Env L α),
    (∀ a, (E a).Adm B (Ryes i) 0 (fun _ => 0) fun _ => 0) →
    tv ((trueHost L i).view E) (S.host.view E) ≤ z

/-! ## 2. What is asked of the run simulators -/

/-- The probability that ρ is withheld or the run simulator is not exact at ρ. -/
structure GoodTrue {L : BatchProtocol I X} (Sm : Sims L) (Ryes : I → X → Prop) (uT uL uO : ℝ≥0∞) : Prop where
  goodT : ∀ w x,
    prRho {ρ | ρ ∈ L.honestOfflineProver.withheld w x ∨
          L.honestOfflineProver.output w x ρ ≠ Sm.T x ρ (L.offline.extAns x ρ (L.honestOfflineProver.ext w))} ≤ uT
  goodL : ∀ w x,
    prRho {ρ | ρ ∈ L.honestLinkProver.withheld w x ∨
          L.honestLinkProver.output w x ρ ≠ Sm.Lk x ρ (L.link.extAns x ρ (L.honestLinkProver.ext w))} ≤ uL
  goodB : ∀ (w : I × L.EncodingRandomness) (x : Fin L.maxBatchSize → Option X), (∀ j xj, x j = some xj → Ryes w.1 xj) →
    ∀ (J : Finset (Fin L.maxBatchSize)) (xs : J → X), (∀ j : J, x j = some (xs j)) →
      prBRho {ρ | (∃ j : J, ρ.slot j.1 ∈ L.honestOnlineBatchProver.one.withheld w (xs j)) ∨
            L.honestOnlineBatchProver.output w x ρ J ≠
              Sm.B J xs (fun j => ρ.slot j.1)
                (L.onlineBatch.extAnsJ J xs (fun j => ρ.slot j.1) (L.honestOnlineBatchProver.ext w))} ≤ J.card * uO

/-- The probabilities of the withheld sets (three fields of BatchProtocol.Complete). -/
structure Held (L : BatchProtocol I X) (Ryes : I → X → Prop) (pT pL pO : ℝ≥0∞) : Prop where
  prT : ∀ w x, prRho (L.honestOfflineProver.withheld w x) ≤ pT
  prL : ∀ w x, prRho (L.honestLinkProver.withheld w x) ≤ pL
  prB : ∀ w x, Ryes w.1 x → prRho (L.honestOnlineBatchProver.one.withheld w x) ≤ pO

/-- The run simulators are exact at every ρ outside the withheld sets. -/
structure ExactOff {L : BatchProtocol I X} (Sm : Sims L) (Ryes : I → X → Prop) : Prop where
  exT : ∀ w x ρ,
    ρ ∉ L.honestOfflineProver.withheld w x → L.honestOfflineProver.output w x ρ = Sm.T x ρ (L.offline.extAns x ρ (L.honestOfflineProver.ext w))
  exL : ∀ w x ρ,
    ρ ∉ L.honestLinkProver.withheld w x → L.honestLinkProver.output w x ρ = Sm.Lk x ρ (L.link.extAns x ρ (L.honestLinkProver.ext w))
  exB : ∀ (w : I × L.EncodingRandomness) (x : Fin L.maxBatchSize → Option X), (∀ j xj, x j = some xj → Ryes w.1 xj) →
    ∀ (J : Finset (Fin L.maxBatchSize)) (xs : J → X), (∀ j : J, x j = some (xs j)) →
      ∀ ρ : BRho L.maxBatchSize L.onlineBatch.loc.shape L.onlineBatch.ann, (∀ j : J, ρ.slot j.1 ∉ L.honestOnlineBatchProver.one.withheld w (xs j)) →
        L.honestOnlineBatchProver.output w x ρ J =
          Sm.B J xs (fun j => ρ.slot j.1) (L.onlineBatch.extAnsJ J xs (fun j => ρ.slot j.1) (L.honestOnlineBatchProver.ext w))

namespace Spec

/-- Honest-verifier zero knowledge of the whole object for the true view. -/
def hvzk_whole_true_of : Prop :=
  ∀ (I X : Type) (L : BatchProtocol I X) (Ryes : I → X → Prop) (b qT qpar qch qon : ℕ) (uT uL uO : ℝ≥0∞),
    L.Wired → L.Reads b qT qpar qch qon →
    ∀ Sm : Sims L, GoodTrue Sm Ryes uT uL uO →
      ∀ d : Fill L, ∀ B : Bounds, B.Fits b qT qpar qch qon →
        ∀ i₀ : I, HVZKWholeTrue L Ryes B (simWhole L (fillSims Sm d) i₀) (B.err uT uL uO)

def goodTrue_of_good : Prop :=
  ∀ (I X : Type) (L : BatchProtocol I X) (Ryes : I → X → Prop) (zT zL zO pT pL pO : ℝ≥0∞) (Sm : Sims L),
    Sm.Good Ryes zT zL zO → Held L Ryes pT pL pO → GoodTrue Sm Ryes (zT + pT) (zL + pL) (zO + pO)

def goodTrue_of_exact : Prop :=
  ∀ (I X : Type) (L : BatchProtocol I X) (Ryes : I → X → Prop) (pT pL pO : ℝ≥0∞) (Sm : Sims L),
    ExactOff Sm Ryes → Held L Ryes pT pL pO → GoodTrue Sm Ryes pT pL pO

/-- From the properties of the interface: under the hypotheses below, each run costs its
simulator's error and the probability of its withheld set. -/
def hvzk_whole_true : Prop :=
  ∀ (I X : Type) (L : BatchProtocol I X) (Ryes : I → X → Prop)
      (b qT qpar qch qon : ℕ) (zT zL zO pT pL pO : ℝ≥0∞),
    L.Wired → L.Reads b qT qpar qch qon →
    ∀ Sm : Sims L, Sm.Good Ryes zT zL zO → Held L Ryes pT pL pO →
      ∀ d : Fill L, ∀ B : Bounds, B.Fits b qT qpar qch qon →
        ∀ i₀ : I, HVZKWholeTrue L Ryes B (simWhole L (fillSims Sm d) i₀)
          (B.err (zT + pT) (zL + pL) (zO + pO))

end Spec
end Hiop
