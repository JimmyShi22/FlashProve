-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/RecKitHonest.lean: book-keeping lemmas on the honest prover and on the verifier's reads of an
interactive oracle proof under a re-indexing of its inputs.

Rules of transport for the terms of Hiop/RecKit.lean, with proofs. (Soundness:
Hiop/RecKitSound.lean.)

If x' is read as f x' and the private input w' as g w', then locality, completeness, the withheld
sets, honest-verifier zero knowledge in the compiler's form (one run; sets of slots of a batch) and
the number of positions read in a batch are kept. `valid'` is any condition on (w', x') that implies
the old condition on (g w', f x').
The simulator of the new protocol is the old one at f x'; the views are the same data under another
name (`DView.comap`).

Main names: `InteractiveOracleProof.IsLocal.comap`; `Honest.Acc.comap`, `Honest.withheld_comap`, `Honest.HVZK.comap`,
  and the same three for `BatchHonestProver`; `BatchInteractiveOracleProof.ReadsAtMost.comap`: see their statements.

Limits: no converse is stated.

Terms: lean/GLOSSARY.md.
-/
import Hiop.RecKit

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

variable {X X' : Type} {E : ExtSpec}

/-- A disclosed view of Q, read as one of Q.comap f: the same data. -/
def DView.comap {Q : InteractiveOracleProof X E} (f : X' → X) (v : DView Q) : DView (Q.comap f) :=
  ⟨v.plains, v.ext, v.orc⟩

theorem InteractiveOracleProof.IsLocal.comap {Q : InteractiveOracleProof X E} (h : Q.IsLocal) (f : X' → X) : (Q.comap f).IsLocal :=
  fun x y y' τ τ' h1 h2 h3 h4 => h (f x) y y' τ τ' h1 h2 h3 h4

section One
variable {Q : InteractiveOracleProof X E} {Wt Wt' : Type} (H : Honest Q Wt) (f : X' → X) (g : Wt' → Wt)

theorem Honest.withheld_comap (w : Wt') (x : X') :
    (H.comap f g).withheld w x = H.withheld (g w) (f x) := rfl

theorem Honest.Acc.comap {H : Honest Q Wt} {valid : Wt → X → Prop} (h : H.Acc valid) (f : X' → X)
    (g : Wt' → Wt) (valid' : Wt' → X' → Prop) (hv : ∀ w x, valid' w x → valid (g w) (f x)) :
    (H.comap f g).Acc valid' :=
  fun w x c ρ hw hρ => h (g w) (f x) c ρ (hv w x hw) hρ

open Classical in
theorem Honest.output_comap (w : Wt') (x : X') (ρ : Rho Q.shape) :
    (H.comap f g).output w x ρ = (H.output (g w) (f x) ρ).map (Option.map (DView.comap f)) := by
  by_cases hρ : ρ ∈ H.withheld (g w) (f x)
  · have e1 : (H.comap f g).output w x ρ = PMF.pure none := if_pos hρ
    have e2 : H.output (g w) (f x) ρ = PMF.pure none := if_pos hρ
    rw [e1, e2, PMF.pure_map]
    rfl
  · have e1 : (H.comap f g).output w x ρ =
        (unif H.Coin).map fun c =>
          some ((Q.comap f).dview x (H.ext (g w)) ((H.strat (g w) (f x) c).run ρ).1) := if_neg hρ
    have e2 : H.output (g w) (f x) ρ =
        (unif H.Coin).map fun c =>
          some (Q.dview (f x) (H.ext (g w)) ((H.strat (g w) (f x) c).run ρ).1) := if_neg hρ
    rw [e1, e2, PMF.map_comp]
    rfl

theorem Honest.HVZK.comap {H : Honest Q Wt} {valid : Wt → X → Prop} {z : ℝ≥0∞} (h : H.HVZK valid z)
    (f : X' → X) (g : Wt' → Wt) (valid' : Wt' → X' → Prop)
    (hv : ∀ w x, valid' w x → valid (g w) (f x)) :
    (H.comap f g).HVZK valid' z := by
  obtain ⟨Sim, hS⟩ := h
  refine ⟨fun x ρ a => (Sim (f x) ρ a).map (Option.map (DView.comap f)),
    fun w x hw => le_trans (pr_mono _ ?_) (hS (g w) (f x) (hv w x hw))⟩
  intro ρ hρ hEq
  apply hρ
  rw [Honest.output_comap, hEq]
  rfl

end One

section Batch
variable {Q : BatchInteractiveOracleProof X E} {Wt Wt' : Type} (H : BatchHonestProver Q Wt) (f : X' → X) (g : Wt' → Wt)

theorem BatchHonestProver.withheld_comap (w : Wt') (x : X') :
    (H.comap f g).one.withheld w x = H.one.withheld (g w) (f x) := rfl

theorem BatchHonestProver.Acc.comap {H : BatchHonestProver Q Wt} {valid : Wt → X → Prop} (h : H.Acc valid) (f : X' → X)
    (g : Wt' → Wt) (valid' : Wt' → X' → Prop) (hv : ∀ w x, valid' w x → valid (g w) (f x)) :
    (H.comap f g).Acc valid' :=
  fun w x c ρ hw hρ => h (g w) (f x) c ρ (hv w x hw) hρ

open Classical in
theorem BatchHonestProver.output_comap
    {N : ℕ} (w : Wt') (x : Fin N → Option X') (ρ : BRho N Q.loc.shape Q.ann) (J : Finset (Fin N)) :
    (H.comap f g).output w x ρ J =
      (H.output (g w) (fun j => (x j).map f) ρ J).map fun o j => (o j).map (DView.comap f) := by
  unfold BatchHonestProver.output
  rw [PMF.map_comp]
  refine congrArg (fun F => (unif (H.Coin0 × (Fin N → H.Coin))).map F) ?_
  funext c j
  show _ = Option.map (DView.comap f) _
  beta_reduce
  cases x j.1 with
  | none => rfl
  | some xj =>
    show (if ρ.slot j.1 ∈ H.one.withheld (g w) (f xj) then none else some _) =
      Option.map (DView.comap f) (if ρ.slot j.1 ∈ H.one.withheld (g w) (f xj) then none else some _)
    by_cases hρ : ρ.slot j.1 ∈ H.one.withheld (g w) (f xj)
    · rw [if_pos hρ, if_pos hρ]
      rfl
    · rw [if_neg hρ, if_neg hρ]
      rfl

theorem BatchHonestProver.HVZK.comap {H : BatchHonestProver Q Wt} {N : ℕ} {valid : Wt → X → Prop} {z : ℝ≥0∞}
    (h : H.HVZK N valid z) (f : X' → X) (g : Wt' → Wt) (valid' : Wt' → X' → Prop)
    (hv : ∀ w x, valid' w x → valid (g w) (f x)) :
    (H.comap f g).HVZK N valid' z := by
  obtain ⟨Sim, hS⟩ := h
  refine ⟨fun J xs ρs a =>
      (Sim J (fun j => f (xs j)) ρs a).map fun o j => (o j).map (DView.comap f),
    fun w x hw J xs hxs => ?_⟩
  refine le_trans (pr_mono _ ?_)
    (hS (g w) (fun j => (x j).map f) ?_ J (fun j => f (xs j)) fun j => by
      show Option.map f (x j.1) = _; rw [hxs j]; rfl)
  · intro ρ hρ hEq
    apply hρ
    rw [BatchHonestProver.output_comap, hEq]
    rfl
  · intro j xj hj
    obtain ⟨x0, h0, rfl⟩ := Option.map_eq_some_iff.1 hj
    exact hv w x0 (hw j x0 h0)

open Classical in
theorem BatchInteractiveOracleProof.allReads_comap (Q : BatchInteractiveOracleProof X E) (f : X' → X) {N : ℕ}
    (x : Fin N → Option X') (ρ : BRho N Q.loc.shape Q.ann) :
    (Q.comap f).allReads x ρ = Q.allReads (fun j => (x j).map f) ρ := by
  unfold BatchInteractiveOracleProof.allReads
  refine Finset.biUnion_congr rfl fun j _ => ?_
  beta_reduce
  cases x j <;> rfl

theorem BatchInteractiveOracleProof.ReadsAtMost.comap
    {Q : BatchInteractiveOracleProof X E} {N q : ℕ} (h : Q.ReadsAtMost N q) (f : X' → X) :
    (Q.comap f).ReadsAtMost N q := fun x ρ => by
  rw [BatchInteractiveOracleProof.allReads_comap]
  exact h _ ρ

end Batch
end Iop
