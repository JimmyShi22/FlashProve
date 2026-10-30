-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/ReadUnif.lean: if the job fits its place, the image under readC of the uniform
distribution on the honest sender's coins is the uniform distribution on the instance's coins. The
proof of Spec.readUnif.
Terms: Johnson/SendSim/At/Sim.lean; sender, readC, coinAt: Johnson/SendSim/At/Bridge.lean. Limits of
the folder: Johnson/SendSim/Defs.lean.

What this file proves. A statement on distributions of coins alone: no row's message, symbol or
answer of a sender is in it.
  readUnif              Spec.readUnif, the statement of the title. The premise is only passed on to
                        readOnto, whose proof does not use it.
  coinAt_add, readC_add   coinAt and readC are additive in the sender's coins.
  csEquiv, readHom      the sender's coins as a pair of families, one for each field; readC as an
                        additive map on that pair.

How it is proved. readC is additive and surjective (readOnto, Johnson/SendSim/At/Onto.lean). An
additive map of one finite group onto another takes the uniform distribution to the uniform
distribution (map_unif_addMonoidHom, Prob/Linear.lean).

How it fits. rowsExact (Johnson/SendSim/At/RowsExact.lean), rowsFresh
(Johnson/SendSim/At/RowsFresh.lean) and rowsFreshAny (Johnson/SendSim/At/FreshWideProofs.lean) each
take readUnif as an argument of the implications in Johnson/SendSim/At/JoinRows.lean and
Johnson/SendSim/At/FoldAnyRoad.lean.
-/
import Prob.Linear
import Johnson.SendSim.At.Onto
import Johnson.SendSim.At.Rows

set_option autoImplicit false

noncomputable section

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc Prob
open Johnson.Prover.Send (shapeAt)

/-- The sender's coins as a pair of families of field elements, one family for each field. -/
def csEquiv (d : Due) : ((Fin d.f → GF) × (Fin d.e → GE)) ≃ Cs d where
  toFun := fun x => ⟨x.1, x.2⟩
  invFun := fun c => (c.f, c.e)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

variable (P : K1.Par) (ride : Nat → Option Ride)

/-- coinAt is additive in the sender's coins. -/
theorem coinAt_add (c c' : Cs (dueR P ride)) (k : ℕ) (x : Seat × ℕ) :
    coinAt P ride (addC c c') k x = coinAt P ride c k x + coinAt P ride c' k x := by
  unfold coinAt
  split
  · rw [ce_add, crd_add]
  · rw [cf_add]

/-- readC is additive in the sender's coins. -/
theorem readC_add (c c' : Cs (dueR P ride)) :
    readC P ride (addC c c') = readC P ride c + readC P ride c' :=
  Prod.ext (funext fun n => coinAt_add P ride c c' _ _)
    (funext fun ρ => funext fun q => coinAt_add P ride c c' _ _)

/-- readC as an additive map from the pair of families to the instance's coins. -/
def readHom : ((Fin (dueR P ride).f → GF) × (Fin (dueR P ride).e → GE)) →+ (sender P ride).Coins :=
  AddMonoidHom.mk' (fun x => readC P ride (csEquiv _ x)) fun a b =>
    readC_add P ride (csEquiv _ a) (csEquiv _ b)

/-- Proof of Spec.readUnif: readC is additive and, by readOnto, surjective, and such a map takes the
uniform distribution to the uniform distribution. -/
theorem readUnif : Spec.readUnif := by
  intro P ride hf
  rw [← map_unif_equiv (csEquiv (dueR P ride)), PMF.map_comp]
  refine map_unif_addMonoidHom (readHom P ride) fun a => ?_
  obtain ⟨c, hc⟩ := readOnto P ride hf a
  exact ⟨(csEquiv _).symm c, hc⟩

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.readUnif
