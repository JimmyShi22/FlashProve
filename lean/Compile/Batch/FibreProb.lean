-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/FibreProb.lean: the verifier messages of a uniform ρ = (ρ_0, ρ_1, .., ρ_N), as the N
slots see them, are sampled round by round.

  `map_finRange_unif_pi`  n independent uniform values, as a list
  `map_slots_kind`  one round
  `map_slots_unif`  all rounds: (unif (BRho N s A)).map (the list of the ρ.slot j) = drawR s A N

Notation: `Kind` (Iop/Batch.lean): a round is called shared (`sh`) or local (`lo`) after its
verifier message; `a.kind.All N C`: the verifier message of the whole batch: one uniform string ρ_0
(`sh`) or a tuple (ρ_1, .., ρ_N) of independent uniform strings (`lo`); `BRho N s A`
(Iop/Batch.lean): the verifier's randomness of a whole execution of the batch; `ρ.slot j`: the
verifier messages in the local transcript τ_j; `RAnn r`, `RoundSplits s` (Iop/Batch.lean): the annotation
of one round, of a shape; `drawV C n`, `headsOf a n`, `drawR s A n` (Compile/Batch/Fibre.lean): n
independent uniform values; the verifier messages of one round, as the slots see them: independent
in a local round, one for all in a shared round; the verifier messages of the local transcripts of n
slots.

Terms: lean/GLOSSARY.md.
-/
import Compile.Batch.Fibre
import Iop.BatchUnif

noncomputable section

namespace Compile.Batch.Fibre
open Iop Rom Prob

/-- a first value and n more -/
def consE (C : Type) (n : ℕ) : C × (Fin n → C) ≃ (Fin (n + 1) → C) where
  toFun := fun x => Fin.cons x.1 x.2
  invFun := fun v => (v 0, fun j => v j.succ)
  left_inv := fun x => by simp
  right_inv := fun v => Fin.cons_self_tail v

/-- for a nonempty C: a uniform function on Fin n, taken as a list, is n independent uniform
values -/
theorem map_finRange_unif_pi (C : Type) [Fintype C] [Nonempty C] : ∀ n : ℕ,
    (unif (Fin n → C)).map (fun v => (List.finRange n).map v) = drawV C n
  | 0 => by
    have h : (fun v : Fin 0 → C => (List.finRange 0).map v) = fun _ => [] := funext fun v => by simp
    rw [h]
    exact PMF.map_const _ _
  | n + 1 => by
    have e := map_unif_equiv (consE C n)
    rw [← e, PMF.map_comp, unif_prod, prod, PMF.map_bind]
    show _ = (unif C).bind fun c => (drawV C n).map fun l => c :: l
    refine congrArg _ (funext fun c => ?_)
    rw [← map_finRange_unif_pi C n, PMF.map_comp, PMF.map_comp]
    refine congrArg (fun f => PMF.map f (unif (Fin n → C))) (funext fun v => ?_)
    show (List.finRange (n + 1)).map (Fin.cons c v : Fin (n + 1) → C) = c :: (List.finRange n).map v
    rw [List.finRange_succ, List.map_cons, List.map_map, Fin.cons_zero]
    congr 1

/-- One round: what the N slots see of a uniform verifier message. -/
theorem map_slots_kind {r : Round} (a : RAnn r) (N : ℕ) :
    (unif (a.kind.All N r.Chal)).map (fun v => (List.finRange N).map fun j => a.kind.slot v j) =
      headsOf a N := by
  unfold headsOf
  cases a.kind with
  | lo => exact map_finRange_unif_pi r.Chal N
  | sh =>
    refine congrArg (fun f => PMF.map f (unif r.Chal)) (funext fun c => ?_)
    show (List.finRange N).map (fun _ => c) = List.replicate N c
    rw [List.map_const', List.length_finRange]

/-- All rounds: the verifier messages of the N local transcripts under a uniform ρ. -/
theorem map_slots_unif (N : ℕ) : ∀ (s : Shape) (A : RoundSplits s),
    (unif (BRho N s A)).map (fun ρ => (List.finRange N).map fun j => ρ.slot j) = drawR s A N
  | [], _ => by
    have h : (fun _ρ : BRho N [] PUnit.unit => (List.finRange N).map fun _j => (() : Rho [])) =
        fun _ => List.replicate N () :=
      funext fun _ => by rw [List.map_const', List.length_finRange]
    show (unif (BRho N [] PUnit.unit)).map
        (fun _ρ => (List.finRange N).map fun _j => (() : Rho [])) =
      PMF.pure (List.replicate N ())
    rw [h]
    exact PMF.map_const _ _
  | r :: s, (a, A) => by
    show (unif (a.kind.All N r.Chal × BRho N s A)).map (fun x =>
        (List.finRange N).map fun j => ((a.kind.slot x.1 j, BRho.slot j x.2) : r.Chal × Rho s)) =
      (headsOf a N).bind fun hs => (drawR s A N).map fun ts => (hs.zip ts : List (r.Chal × Rho s))
    rw [← map_slots_kind a N, ← map_slots_unif N s A, unif_prod, prod, PMF.map_bind, PMF.bind_map]
    refine congrArg _ (funext fun v => ?_)
    rw [PMF.map_comp, Function.comp_apply, PMF.map_comp]
    refine congrArg (fun f => PMF.map f (unif (BRho N s A))) (funext fun ρ => ?_)
    simp only [Function.comp_apply, List.zip_map']

end Compile.Batch.Fibre
