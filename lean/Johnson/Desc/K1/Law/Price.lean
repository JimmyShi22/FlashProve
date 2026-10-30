-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/Price.lean: the number of a place's bad seeds in the numbers in which the
planner prices the round of a sending's seeds (OnBytes/Params/RecordPrice.lean: clashSeeds,
allSeeds).
Main names: portZ_err (the error of the library's sample map of a shape is clashSeeds at the field's
size and the cube's coordinates); seeds_total (all seeds of a message's own cube, times the rests,
are the place's joint seeds); errPort_eq.

What is not claimed. That a plan's entry has this price: the planner's accounting is not named here.
One answer a message. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.Port6
import OnBytes.Params.RecordPrice

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice Johnson.Pack Cb Cb.Ood Prob

theorem clash_nat (v q u : Nat) (hu : u = q - 1) :
    max (v * q ^ (v - 1) * u) (q ^ v) = clashSeeds q v := by
  subst hu
  rfl

theorem all_nat (v q u c : Nat) (hu : u = q - 1) (hc : c = q ^ v * u) : c = allSeeds q v := by
  subst hu
  exact hc

/-- **The error of the library's sample map of a shape, in the planner's numbers.** -/
theorem portZ_err (cs : Codes) (s : OracleShape) :
    (portZ cs s).err = clashSeeds (Fintype.card GE) (bitsZ cs s) := by
  have h : (portZ cs s).err = max (bitsZ cs s * Fintype.card GE ^ (bitsZ cs s - 1) *
      Fintype.card GEˣ) (Fintype.card GE ^ bitsZ cs s) := by
    simp
  rw [h]
  exact clash_nat _ _ _ (Fintype.card_units GE)

/-- **All seeds of a message's own cube, times the rests, are the place's joint seeds.** -/
theorem seeds_total (P : Par) (k : Fin (shapesOf P).length) (hk : sampledAt P k) :
    allSeeds (Fintype.card GE) (bitsZ P.codes (shapeAt P k)) ^ 1 *
        Fintype.card (Rest GE GEˣ P.seeds 1 P.coordinates (bitsZ P.codes (shapeAt P k))) =
      Fintype.card (Seeds P) := by
  rw [card_part P.seeds 1 P.coordinates (bitsZ P.codes (shapeAt P k)) (one_le_seeds P k hk)
    (bits_le_coordinates P k hk), Fintype.card_fun, Fintype.card_fin]
  congr 2
  exact (all_nat _ _ _ _ (Fintype.card_units GE) (by
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin])).symm

/-- **The bound on a place's bad seeds, in the planner's numbers.** -/
theorem errPort_eq (P : Par) (rad : Nat → Nat) :
    errPort P rad = ∑ k : Fin (shapesOf P).length, if sampledAt P k then
      (lOf P.codes (shapeAt P k) (rad k.val)).choose 2 *
        clashSeeds (Fintype.card GE) (bitsZ P.codes (shapeAt P k)) ^ 1 *
        Fintype.card (Rest GE GEˣ P.seeds 1 P.coordinates (bitsZ P.codes (shapeAt P k)))
      else 0 := by
  unfold errPort
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [portZ_err, pow_one]

end VerifiableInference.Desc.K1
