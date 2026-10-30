-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtHome/HomeHVZK.lean: the library's own predicate Honest.HVZK at error 0, for the
explicit link prover at homeR b Z.
Terms of this folder: Johnson/LinkSim/Spec.lean.

What this file proves. homeHVZKAt names the simulator and is the stronger form (homeHVZK_of_at). For
every b, all public files Z, and every private input w and instance x that are valid (validLk, with
both side predicates trivially true), consider the verifier messages ρ at which
(explicitLinkProver b Z).output w x ρ differs from homeSim Z x ρ applied to the input oracles' symbols at the
queried positions. That set has probability at most 0. homeHVZK states the library's predicate
(explicitLinkProver b Z).HVZK (validLk …) 0 (Honest.HVZK, Iop/InteractiveOracleProof.lean), which asks only that some simulator
exist; homeHVZK_of_at proves it from homeHVZKAt.

homeHVZKAt restates homeExactAll (Johnson/LinkSim/AtHome/HomeExactAll.lean) in the form of the
library's predicate, with the simulator named; only that direction is proved here. What the result
means is told in Johnson/LinkSim/AtHome/Home.lean, under "The result."

How it fits. This is the corollary that Home.lean's notes name (Honest.HVZK.of_exact). homeHVZKAt
follows from homeExactAll: the set is empty, and the empty set has probability 0. homeHVZK follows
by Honest.HVZK.of_exact, with homeSim Z and the empty exceptional set. Under Johnson/LinkSim/ no
file calls this file's theorems.

Names (namespace OnBytes.LinkSim.AtHome): Spec.homeHVZK and Spec.homeHVZKAt (statements);
homeHVZK_of_at, homeHVZKAt and homeHVZK (theorems).

Limits. All limits of homeExact apply (Johnson/LinkSim/AtHome/Home.lean); this file adds none.

Sources. A statement here is covered by the note on sources in the head of Spec.lean.

Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtHome.HomeExactAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off here, so that no
statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.LinkSim.AtHome
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD Rom
open OnBytes.Flat OnBytes.Slice OnBytes.Maker
open OnBytes.LinkSim (validLk)
open _root_.Iop (Rho InteractiveOracleProof Honest prRho)

/- These definitions are made irreducible here, so that Lean does not unfold them while it
elaborates. This is for speed; the kernel still checks every proof. -/
attribute [local irreducible] theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem riDigits fieldRows

/-- Statement only; proved as homeHVZK below. The library's predicate Honest.HVZK at error 0, for
the explicit link prover. -/
def Spec.homeHVZK : Prop :=
  ∀ (b : PublicFiles → ℕ) (Z : PublicFiles),
    (explicitLinkProver b Z).HVZK (validLk (homeR b Z).protocol (fun _ => True) (fun _ => True)) 0

/-- Statement only; proved as homeHVZKAt below. The body of Honest.HVZK at error 0, with homeSim Z
as the simulator. -/
def Spec.homeHVZKAt : Prop :=
  ∀ (b : PublicFiles → ℕ) (Z : PublicFiles) (w : HomeWt b Z) (x : RecFull × RecFull),
    validLk (homeR b Z).protocol (fun _ => True) (fun _ => True) w x →
    prRho {ρ : Rho (HomeQ Z).shape | (explicitLinkProver b Z).output w x ρ ≠
      homeSim Z x ρ ((HomeQ Z).extAns x ρ ((explicitLinkProver b Z).ext w))} ≤ 0

/-- The form that names the simulator implies the library's predicate. -/
theorem homeHVZK_of_at : Spec.homeHVZKAt → Spec.homeHVZK :=
  fun h b Z => ⟨homeSim Z, h b Z⟩

/-- The set of verifier messages at which the two outputs differ is empty, by homeExactAll. -/
theorem homeHVZKAt : Spec.homeHVZKAt := by
  intro b Z w x hv
  have h : {ρ : Rho (HomeQ Z).shape | (explicitLinkProver b Z).output w x ρ ≠
      homeSim Z x ρ ((HomeQ Z).extAns x ρ ((explicitLinkProver b Z).ext w))} = ∅ :=
    Set.eq_empty_iff_forall_notMem.2 fun ρ hρ => hρ (homeExactAll b Z w x hv ρ)
  rw [h]
  exact le_of_eq (Prob.pr_empty _)

/-- The library's predicate holds at error 0, with the empty exceptional set. -/
theorem homeHVZK : Spec.homeHVZK := fun b Z =>
  Honest.HVZK.of_exact (explicitLinkProver b Z) _ 0 (homeSim Z) (fun _ _ => ∅)
    (fun w x hv ρ _ => homeExactAll b Z w x hv ρ) (fun _ _ _ => le_of_eq (Prob.pr_empty _))

end OnBytes.LinkSim.AtHome

#print axioms OnBytes.LinkSim.AtHome.homeHVZK_of_at
#print axioms OnBytes.LinkSim.AtHome.homeHVZKAt
#print axioms OnBytes.LinkSim.AtHome.homeHVZK
