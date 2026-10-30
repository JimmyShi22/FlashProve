--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/CodedReads.lean: the coded values of Johnson/Desc/K14/Honest/Coded.lean,
read into a field, are the plain functions of Johnson/Desc/K14/Honest/Moves.lean at the read data.

  val_foldRowsE, val_uHonE, val_omegaHonE, val_muHonE   one for each function, at every reading
  val_uAtE, val_omegaAtE, val_muAtE   the like for the three at the shared point

What is not claimed. Every equation is between readings, not between the program's words. Nothing on
a verifier's decision, on soundness or on hiding.

-/
import Johnson.Desc.K14.Honest.Coded
import Johnson.Desc.K14.Honest.Moves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open Desc.K14.Law

variable {K : Type} [Field K] (ρ : OnBytes.Model.Reading K)

theorem val_foldRowsE (n : Nat) (w : Nat → E) (RwE : Nat → Nat → E) (k : Nat) :
    ρ.val (foldRowsE n w RwE k) =
      foldRows n (fun r => ρ.val (w r)) (fun r k => ρ.val (RwE r k)) k := by
  unfold foldRowsE foldRows
  rw [val_sumE]
  exact Finset.sum_congr rfl fun r _ => ρ.mul _ _

theorem val_uHonE (S : FoldeqShape) (gam : List E) (RwE : Nat → Nat → E) (k : Nat) :
    ρ.val (uHonE S gam RwE k) =
      uHon S (eqK (gam.map ρ.val)) (fun r k => ρ.val (RwE r k)) k := by
  unfold uHonE uHon
  by_cases h : k < S.entries
  · rw [if_pos h, if_pos h, val_foldRowsE]
    unfold foldRows
    refine Finset.sum_congr rfl fun r _ => ?_
    show ρ.val (eqE gam r) * ρ.val (RwE r k) = eqK (gam.map ρ.val) r * ρ.val (RwE r k)
    rw [val_eqE]
  · rw [if_neg h, if_neg h, ρ.zero]

theorem val_omegaHonE (S : LinShape) (psiLo : List E) (u : Nat → E) (j : Nat) :
    ρ.val (omegaHonE S psiLo u j) = omegaHon S (psiLo.map ρ.val) (fun k => ρ.val (u k)) j := by
  unfold omegaHonE omegaHon
  by_cases h : j < S.matrixRows
  · rw [if_pos h, if_pos h, val_sumE]
    exact Finset.sum_congr rfl fun t _ => by rw [ρ.mul, val_eqE]
  · rw [if_neg h, if_neg h, ρ.zero]

theorem val_muHonE (S : LinShape) (z : List E) (omega : Nat → E) (kappa : E) :
    ρ.val (muHonE S z omega kappa) =
      muHon S (z.map ρ.val) (fun j => ρ.val (omega j)) (ρ.val kappa) := by
  unfold muHonE muHon
  rw [ρ.add, val_sumE]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [ρ.mul, val_eqE]

theorem val_uAtE (S : LinShape) (psi : List E) (RwE : Nat → Nat → E) (k : Nat) :
    ρ.val (uAtE S psi RwE k) =
      uHon S.fold (eqK ((psi.drop S.kLo).map ρ.val)) (fun r k => ρ.val (RwE r k)) k :=
  val_uHonE ρ S.fold (psi.drop S.kLo) RwE k

theorem val_omegaAtE (S : LinShape) (psi : List E) (RwE : Nat → Nat → E) (j : Nat) :
    ρ.val (omegaAtE S psi RwE j) =
      omegaHon S ((psi.take S.kLo).map ρ.val) (fun k => ρ.val (uAtE S psi RwE k)) j :=
  val_omegaHonE ρ S (psi.take S.kLo) (uAtE S psi RwE) j

theorem val_muAtE (S : LinShape) (psi z : List E) (RwE : Nat → Nat → E) (kappa : E) :
    ρ.val (muAtE S psi z RwE kappa) =
      muHon S (z.map ρ.val) (fun j => ρ.val (omegaAtE S psi RwE j)) (ρ.val kappa) :=
  val_muHonE ρ S z (omegaAtE S psi RwE) kappa

end Desc.K14.Honest

#print axioms Desc.K14.Honest.val_foldRowsE
#print axioms Desc.K14.Honest.val_uHonE
#print axioms Desc.K14.Honest.val_omegaHonE
#print axioms Desc.K14.Honest.val_muHonE
#print axioms Desc.K14.Honest.val_uAtE
#print axioms Desc.K14.Honest.val_omegaAtE
#print axioms Desc.K14.Honest.val_muAtE
