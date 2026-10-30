--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/NormBridge/BridgeHonest.lean: A TRIAL OF BridgeCore.lean:
DATA THAT HOLD EXIST, at
every size lt, NI, lNI, at every width d up to 2^16 and at all constants with 1 <= eps < 2^48 and
M <= 47: the limbs are integers of a stream, the digits are the library's honest ledger
(Inst/Model/Common/LedgerHonest.lean: hon, under its HonHyp), both laid into the field.
With honest_lines, honest_sq, honest_pr and honest_not_bad of BridgeCore.lean: at such data the
law's
premises hold at every draw and no draw is bad.

LANDED LEMMAS TAKEN: LedgerHonest.lean hon_idn; LedgerSound.lean map_idn, map_Wsum.
NOT CLAIMED: that the release's constants meet HonHyp (the tests on the plan say so of eps, M and d;
not held here).
-/
import OnBytes.Desc.First.NormBridge.BridgeCore
import Inst.Model.Common.LedgerHonest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D6.Bridge
open Inst.Model (NormPar)
open Inst.Model.Ledger (Wsum hon HonHyp)

variable {K : Type} [Field K]

/-- Data from integer limbs: b i t l j is limb l of feature j of norm i's stream at position t. -/
def honData (K : Type) [Field K] (lt d NI lNI : ℕ) (np : ℕ → NormPar) (b : ℕ → ℕ → ℕ → ℕ → ℤ) :
    Data K where
  lt := lt
  d := d
  NI := NI
  lNI := lNI
  np := np
  limb := fun i l j t => Int.castRingHom K (b i t l j)
  dig := fun i n t => Int.castRingHom K (hon (np i) d (b i t) n)

/-- **Honest data hold.** -/
theorem honData_holds (lt d NI lNI : ℕ) (np : ℕ → NormPar) (b : ℕ → ℕ → ℕ → ℕ → ℤ)
    (H : ∀ i < NI, ∀ t < 2 ^ lt, HonHyp (np i) d (b i t)) :
    (honData K lt d NI lNI np b).Holds := by
  intro i hi k hk t ht
  have h := Inst.Model.Ledger.hon_idn (H i hi t ht) k hk
  have h2 := congrArg (Int.castRingHom K) h
  rw [Inst.Model.Ledger.map_idn, map_zero] at h2
  have e : (fun s => (Int.castRingHom K) (Wsum d (b i t) s)) =
      fun s => Wsum d (fun l j => (Int.castRingHom K) (b i t l j)) s :=
    funext fun s => Inst.Model.Ledger.map_Wsum _ d (b i t) s
  rw [e] at h2
  exact h2

end D6.Bridge

#print axioms D6.Bridge.honData_holds
