-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/WalkSeat.lean: kind K5: THE BLOCKS THAT STAND BEHIND K5's IN AN ATTENTION
SEGMENT's LIST, as one seat of the first chain lays them, CARRY the ledger and what K5 heard (CarK5,
Claims/WalkK5.lean): ALL BUT ONE, which is taken as a named premise.

Which blocks (by reading; no theorem says that a seated text lays just these). The driver's kinds behind K5
(kindsBeforeBatching, Johnson/Desc/First/Driver/Chain.lean): K1 · K8 · K1 · K3. At the seat that is read here (a harness:
kind K1's lot, Johnson/Desc/ProofFile/Lot/K1.lean: its
linkNumbers gives an attention link the pieces 4 and 6; its blocks lays): piece 4: K1's later moment (laterAt,
moment 1) WITH THE STEP WITHOUT A ROUND THAT IS HANDED IN LAID BEHIND IT BY Block.andThen (the harness's
PureLots.lean hands in readsAtO there); piece 6: laterAt (moment 2) by itself.

Main names:
  laterAt_steps · piece4_steps (by stepsAndThen, Johnson/Desc/Sound/StepsThrough.lean).
  behind_k5_carry: the four blocks, the lookup on the smallness test's digits UNDER A NAMED PREMISE hK3.
IS IT EMPTY HERE? Implications on yeses. hK3 IS SHOWN OF NO BLOCK: no law on that lookup's hearing at its seat
  (Law.blockVia (seatDigits claim)) is known to us.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.StepsThrough
import Johnson.Desc.K1.Places
import Johnson.Desc.First.Att.Claims.WalkK8

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc (First.S Block stepsAndThen)
open VerifiableInference.Desc.First (K8.atS K8.approximateRangeProofDrawKind K8.Par)
open VerifiableInference.Desc.First.Att

variable {Cl : Type}

theorem laterAt_steps (q : Params.First) (gp : Desc.Plain.GPar) (link piece moment : ℕ)
    (arrays : Option (List ℕ)) :
    (VerifiableInference.Desc.K1.laterAt (Cl := Cl) q gp link piece moment arrays).Steps CarK5 :=
  commitAtS_steps _ _ _ _

/-- **Piece 4: the sending of the reads, with the step that makes the tables behind it.** -/
theorem piece4_steps (q : Params.First) (gp : Desc.Plain.GPar) (link piece moment : ℕ)
    (arrays : Option (List ℕ)) (name : String) (W : Verify.Public) (l g : ℕ) (z : Block First.S Cl)
    (hz : readsAtO W l g = some z) :
    ((VerifiableInference.Desc.K1.laterAt (Cl := Cl) q gp link piece moment arrays).andThen name z).Steps
      CarK5 :=
  stepsAndThen carK5_pre name _ _ (laterAt_steps q gp link piece moment arrays) (readsAtO_steps W l g z hz)

/-- **The four blocks behind K5's.** -/
theorem behind_k5_carry (q₄ q₆ : Params.First) (gp : Desc.Plain.GPar) (link : ℕ)
    (reads digits : Option (List ℕ)) (name : String) (W : Verify.Public) (g : ℕ) (z : Block First.S Cl)
    (hz : readsAtO W link g = some z) (p₈ : K8.Par) (b₇ : Block First.S Cl) (hK3 : b₇.Steps CarK5) :
    ∀ x ∈ [(VerifiableInference.Desc.K1.laterAt (Cl := Cl) q₄ gp link 4 1 reads).andThen name z,
        K8.approximateRangeProofDrawKind (Cl := Cl) K8.atS p₈, VerifiableInference.Desc.K1.laterAt (Cl := Cl) q₆ gp link 6 2 digits,
        b₇], x.Steps CarK5 := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact piece4_steps _ _ _ _ _ _ _ _ _ _ _ hz
  · exact k8_steps _
  · exact laterAt_steps _ _ _ _ _ _
  · exact hK3

end K5Law

#print axioms K5Law.piece4_steps
#print axioms K5Law.behind_k5_carry
