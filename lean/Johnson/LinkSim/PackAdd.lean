-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/PackAdd.lean: the library's packing of a hiding polynomial's coefficients into a
table is additive in the coefficients, also when the table's columns are placed at other
coordinates. Statements and proofs. Pure algebra.
Terms of this folder: Johnson/LinkSim/Spec.lean.

What this file has.
  pkAtC_add, pkAtC_zero   the packing pkC, with its columns placed at any coordinates (pkAt), is
                          additive in the coefficients, and sends 0 to 0.
  pkC_add, pkC_zero       the table pkC h g m (Cb/Ld/LdSumPack.lean) of the sum of two coefficient
                          families is the sum of the tables; the table of 0 is 0.
  placeV_add, placeV_zero   the same for a vector placed at other coordinates, 0 elsewhere
                          (placeV).
  pkAt_add, pkAt_zero     the same for any additive packing placed at other coordinates (pkAt).

How it fits. Used in the proof of homeExact (Johnson/LinkSim/AtHome/Home.lean).
Johnson/LinkSim/AtText/State.lean uses pkAtC_add.

Limits. Nothing here on the identity that the library calls the packing's law (PackLaw,
Cb/Ld/LdSumPack.lean).
Terms: lean/GLOSSARY.md.

-/
import Cb.Ld.LdSumPack

set_option autoImplicit false

namespace OnBytes.LinkSim
open Cb

variable {E : Type} [Field E]

/-- pkC is additive in the coefficients. -/
theorem pkC_add (h g m : ℕ) (W W' : HIdx (sVars E (m + 1) (h + g)) → E) :
    pkC h g m (W + W') = pkC h g m W + pkC h g m W' := by
  funext a
  obtain ⟨β, iq | tp | u⟩ := a
  · show (W _ + W' _) * pMon iq.1 β = W _ * pMon iq.1 β + W' _ * pMon iq.1 β
    exact add_mul _ _ _
  · show (W _ + W' _) + (if pLead g m (.inl tp) then
        ∑ i : Fin h, (W _ + W' _) * pMon i β else 0) =
      (W _ + if pLead g m (.inl tp) then ∑ i : Fin h, W _ * pMon i β else 0) +
        (W' _ + if pLead g m (.inl tp) then ∑ i : Fin h, W' _ * pMon i β else 0)
    split_ifs
    · simp only [add_mul, Finset.sum_add_distrib]
      ring
    · ring
  · show (W _ + W' _) + (if pLead g m (.inr u) then
        ∑ i : Fin h, (W _ + W' _) * pMon i β else 0) =
      (W _ + if pLead g m (.inr u) then ∑ i : Fin h, W _ * pMon i β else 0) +
        (W' _ + if pLead g m (.inr u) then ∑ i : Fin h, W' _ * pMon i β else 0)
    split_ifs
    · simp only [add_mul, Finset.sum_add_distrib]
      ring
    · ring

/-- pkC of 0 is 0. -/
theorem pkC_zero (h g m : ℕ) : pkC h g m (0 : HIdx (sVars E (m + 1) (h + g)) → E) = 0 := by
  have e := pkC_add h g m (0 : HIdx (sVars E (m + 1) (h + g)) → E) 0
  rw [add_zero] at e
  exact left_eq_add.mp e

/-- placeV is additive. -/
theorem placeV_add {Cl J : Type} [Fintype Cl] [DecidableEq J] (plc : Cl → J) (v v' : Cl → E) :
    placeV plc (v + v') = placeV plc v + placeV plc v' := by
  funext j
  show (∑ c, if plc c = j then v c + v' c else 0) =
    (∑ c, if plc c = j then v c else 0) + ∑ c, if plc c = j then v' c else 0
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs
  · rfl
  · exact (add_zero _).symm

/-- placeV of 0 is 0. -/
theorem placeV_zero {Cl J : Type} [Fintype Cl] [DecidableEq J] (plc : Cl → J) :
    placeV plc (0 : Cl → E) = 0 := by
  have e := placeV_add plc (0 : Cl → E) 0
  rw [add_zero] at e
  exact left_eq_add.mp e

/-- An additive packing placed at other coordinates is additive. -/
theorem pkAt_add {Ix Rw Cl J : Type} [Fintype Cl] [DecidableEq J] (plc : Cl → J)
    (pk : (Ix → E) → Rw × Cl → E) (hpk : ∀ W W', pk (W + W') = pk W + pk W') (W W' : Ix → E) :
    pkAt plc pk (W + W') = pkAt plc pk W + pkAt plc pk W' := by
  funext a
  show placeV plc (fun c => pk (W + W') (a.1, c)) a.2 =
    placeV plc (fun c => pk W (a.1, c)) a.2 + placeV plc (fun c => pk W' (a.1, c)) a.2
  rw [hpk]
  exact congrFun (placeV_add plc (fun c => pk W (a.1, c)) fun c => pk W' (a.1, c)) a.2

/-- It sends 0 to 0. -/
theorem pkAt_zero {Ix Rw Cl J : Type} [Fintype Cl] [DecidableEq J] (plc : Cl → J)
    (pk : (Ix → E) → Rw × Cl → E) (hpk : ∀ W W', pk (W + W') = pk W + pk W') :
    pkAt plc pk 0 = 0 := by
  have e := pkAt_add plc pk hpk 0 0
  rw [add_zero] at e
  exact left_eq_add.mp e

/-- The packing pkC, placed at any coordinates, is additive. -/
theorem pkAtC_add {J : Type} [DecidableEq J] (h g m : ℕ) (plc : PCol h g m → J)
    (W W' : HIdx (sVars E (m + 1) (h + g)) → E) :
    pkAt plc (pkC h g m) (W + W') = pkAt plc (pkC h g m) W + pkAt plc (pkC h g m) W' :=
  pkAt_add plc _ (pkC_add h g m) W W'

/-- The packing pkC, placed at any coordinates, sends 0 to 0. -/
theorem pkAtC_zero {J : Type} [DecidableEq J] (h g m : ℕ) (plc : PCol h g m → J) :
    pkAt plc (pkC (E := E) h g m) 0 = 0 :=
  pkAt_zero plc _ (pkC_add h g m)

end OnBytes.LinkSim

#print axioms OnBytes.LinkSim.pkC_add
#print axioms OnBytes.LinkSim.pkAtC_add
#print axioms OnBytes.LinkSim.pkAtC_zero
