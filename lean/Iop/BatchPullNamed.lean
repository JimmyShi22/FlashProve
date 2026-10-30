-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/BatchPullNamed.lean: the simulator for sets of slots after the pull-back of Iop/BatchPull.lean,
as a term. (Words of this library: lean/GLOSSARY.md.)
`hvzk_pull` (Iop/BatchPullProofs.lean), under the hypotheses of its statement, proves that a
simulator exists; the simulator in its proof is `simPullB` below, and `simPullB_good` restates its
argument for a simulator that is given, if 0 < N. (not all hypotheses are named here: see
`simPullB_good`)
The counterpart for an ordinary IOP is `simPull`, `simPull_good` of Top/Simulator.lean.

Notation: `DView Q : Type` (Iop/InteractiveOracleProof.lean): the disclosed view; `Q.extAnsJ J xs ρs y`
(Iop/Batch.lean): see its docstring; `prBRho S : ℝ≥0∞` (Iop/Batch.lean): the probability of a set of
values of ρ = (ρ_0, ρ_1, .., ρ_N); `Samplers.Good σ κ K : Prop` (Iop/Pull.lean): every fibre has at
most w elements; for each round w * card Chal ≤ κ * card Src; and the product of these ratios over
all rounds is at most K.
-/
import Iop.BatchPullProofs
noncomputable section -- Lean tags what it cannot compile

namespace Iop
open Prob BatchPull
open scoped ENNReal

variable {X : Type} {E : ExtSpec} {Wt : Type}

/-- runs the given simulator at the pushed challenges and carries its output over -/
def simPullB {Q : BatchInteractiveOracleProof X E} (σ : Samplers Q.loc.shape) {N : ℕ}
    (Sim : (J : Finset (Fin N)) → (J → X) → (J → Rho Q.loc.shape) →
      (E.Pos → Option E.Sym) → PMF (J → Option (DView Q.loc)))
    (J : Finset (Fin N)) (xs : J → X)
    (ρs : J → Rho (Q.pull σ).loc.shape) (a : E.Pos → Option E.Sym) :
    PMF (J → Option (DView (Q.pull σ).loc)) :=
  (Sim J xs (fun j => Rho.push σ (ρs j)) a).map fun f j => (f j).map (DView.pull σ)

theorem simPullB_good {Q : BatchInteractiveOracleProof X E} {H : BatchHonestProver Q Wt} {N : ℕ} (hN : 0 < N)
    {σ : Samplers Q.loc.shape} {κ K : ℝ≥0∞} (hσ : σ.Good κ K)
    (Sim : (J : Finset (Fin N)) → (J → X) → (J → Rho Q.loc.shape) →
      (E.Pos → Option E.Sym) → PMF (J → Option (DView Q.loc)))
    (w : Wt) (x : Fin N → Option X) (J : Finset (Fin N)) (xs : J → X) {z : ℝ≥0∞}
    (h : prBRho {ρ | H.output w x ρ J ≠
          Sim J xs (fun j => ρ.slot j.1) (Q.extAnsJ J xs (fun j => ρ.slot j.1) (H.ext w))} ≤
      J.card * z) :
    prBRho {ρ | (H.pull σ).output w x ρ J ≠
          simPullB σ Sim J xs (fun j => ρ.slot j.1)
            ((Q.pull σ).extAnsJ J xs (fun j => ρ.slot j.1) ((H.pull σ).ext w))} ≤
      J.card * (K ^ N * z) := by
  have hb : K ^ N *
        prBRho {ρ | H.output w x ρ J ≠
            Sim J xs (fun j => ρ.slot j.1) (Q.extAnsJ J xs (fun j => ρ.slot j.1) (H.ext w))} ≤
      J.card * (K ^ N * z) := by
    calc _ ≤ K ^ N * (J.card * z) := by gcongr
      _ = J.card * (K ^ N * z) := by ring
  refine le_trans (le_trans (pr_mono _ ?_) (prBRho_preimage_le hN hσ _)) hb
  intro ρ hρ heq
  apply hρ
  rw [output_pull, heq]
  have e : (fun j : J => (BRho.push σ ρ).slot j.1) = fun j : J => Rho.push σ (ρ.slot j.1) :=
    funext fun j => slot_push j.1 σ ρ
  rw [e]
  rfl

end Iop
