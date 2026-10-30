-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/BatchSlot.lean: for every annotation and every N > 0, HVZK for sets of slots (`BatchHonestProver.HVZK`,
Iop/Batch.lean) gives HVZK of one slot (`Honest.HVZK`), with the same error (`BatchHonestProver.HVZK.one`):
take the set of one slot, all other slots empty. (Words of this library: lean/GLOSSARY.md.)
Limits: this file does not prove that the soundness property `BatchInteractiveOracleProof.SndB` (Snd-B) of a protocol
with slots (Iop/Batch.lean) gives round-by-round soundness of the slot's verifier's IOP.
-/
import Iop.BatchPartial
import Iop.BatchUnif

namespace Iop
open Prob
open scoped ENNReal

variable {X : Type} {E : ExtSpec}

namespace BatchSlot

variable {Q : BatchInteractiveOracleProof X E} {Wt : Type} (H : BatchHonestProver Q Wt) {N : ℕ} (j0 : Fin N)

/-- the vector of requests with x in slot j0 and all other slots empty -/
def only (x : X) : Fin N → Option X := fun j => if j = j0 then some x else none

theorem only_self (x : X) : only j0 x j0 = some x := if_pos rfl

/-- the slot j0 as an element of the set {j0} -/
def the : ({j0} : Finset (Fin N)) := ⟨j0, Finset.mem_singleton_self j0⟩

theorem eq_the (j : ({j0} : Finset (Fin N))) : j = the j0 :=
  Subtype.ext (Finset.mem_singleton.1 j.2)

theorem extAnsJ_single (x : X) (ρ : Rho Q.loc.shape) (y : E.Str) :
    Q.extAnsJ ({j0} : Finset (Fin N)) (fun _ => x) (fun _ => ρ) y = Q.loc.extAns x ρ y := by
  classical
  funext p
  unfold BatchInteractiveOracleProof.extAnsJ InteractiveOracleProof.extAns
  have : (∃ _j : ({j0} : Finset (Fin N)), p ∈ Q.loc.extReads x ρ) ↔ p ∈ Q.loc.extReads x ρ :=
    ⟨fun ⟨_, h⟩ => h, fun h => ⟨the j0, h⟩⟩
  exact if_congr this rfl rfl

/-- the coins that slot j0 sees are uniform -/
theorem map_coins :
    (unif (H.Coin0 × (Fin N → H.Coin))).map (fun c => (c.1, c.2 j0)) = unif (H.Coin0 × H.Coin) := by
  classical
  exact map_unif_prodMap id (fun c : Fin N → H.Coin => c j0) (PMF.map_id _)
    (map_eval_unif_pi (A := fun _ : Fin N => H.Coin) j0)

/-- At the vector `only j0 x`, the output for the set {j0} is the output of the one slot. -/
theorem output_single (w : Wt) (x : X) (ρ : BRho N Q.loc.shape Q.ann) :
    H.output w (only j0 x) ρ {j0} = (H.one.output w x (ρ.slot j0)).map fun o _ => o := by
  classical
  unfold BatchHonestProver.output Honest.output
  by_cases hρ : ρ.slot j0 ∈ H.one.withheld w x
  · rw [if_pos hρ, PMF.pure_map]
    refine (congrArg (fun g => PMF.map g (unif (H.Coin0 × (Fin N → H.Coin)))) ?_).trans
      (PMF.map_const _ _)
    funext c j
    rw [eq_the j0 j]
    split
    · rfl
    · rename_i xj hx
      obtain rfl : x = xj := Option.some.inj ((only_self j0 x).symm.trans hx)
      exact if_pos hρ
  · rw [if_neg hρ, PMF.map_comp]
    show _ = PMF.map _ (unif (H.Coin0 × H.Coin))
    rw [← map_coins H j0, PMF.map_comp]
    congr 1
    funext c j
    rw [eq_the j0 j]
    split
    · rename_i hx
      exact absurd ((only_self j0 x).symm.trans hx) (by simp)
    · rename_i xj hx
      obtain rfl : x = xj := Option.some.inj ((only_self j0 x).symm.trans hx)
      exact if_neg hρ

end BatchSlot

open BatchSlot in
/-- If 0 < N, `BatchHonestProver.HVZK` gives `Honest.HVZK` of one slot, with the same z. -/
theorem BatchHonestProver.HVZK.one {Q : BatchInteractiveOracleProof X E} {Wt : Type} {H : BatchHonestProver Q Wt} {N : ℕ} (hN : 0 < N)
    {valid : Wt → X → Prop} {z : ℝ≥0∞} (h : H.HVZK N valid z) : H.one.HVZK valid z := by
  classical
  obtain ⟨SimB, h⟩ := h
  let j0 : Fin N := ⟨0, hN⟩
  refine ⟨fun x ρ ans => (SimB {j0} (fun _ => x) (fun _ => ρ) ans).map fun f => f (the j0),
    fun w x hv => ?_⟩
  have hb := h w (only j0 x) (fun j xj e => by
      unfold only at e
      split_ifs at e
      cases e
      exact hv) {j0} (fun _ => x) (fun j => by rw [eq_the j0 j]; exact only_self j0 x)
  rw [Finset.card_singleton, Nat.cast_one, one_mul] at hb
  rw [← prBRho_slot j0 (A := Q.ann)]
  refine le_trans ?_ hb
  unfold prBRho
  refine pr_mono _ ?_
  intro ρ hρ heq
  refine hρ ?_
  rw [output_single] at heq
  have e1 : (fun j : ({j0} : Finset (Fin N)) => ρ.slot j.1) = fun _ => ρ.slot j0 := by
    funext j; rw [eq_the j0 j]; rfl
  rw [e1, extAnsJ_single] at heq
  have :=
    congrArg (PMF.map fun f : ({j0} : Finset (Fin N)) → Option (DView Q.loc) => f (the j0)) heq
  rw [PMF.map_comp] at this
  have hid : ((fun f : ({j0} : Finset (Fin N)) → Option (DView Q.loc) => f (the j0)) ∘
        fun o _ => o) = id := rfl
  rw [hid, PMF.map_id] at this
  exact this

end Iop
