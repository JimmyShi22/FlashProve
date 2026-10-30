-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtHome/HomeNotIdle.lean: the link's private inputs at homeR b Z form a non-empty
type, and a valid pair of private input and instance exists.
Terms of this folder: Johnson/LinkSim/Spec.lean.

What this file proves. home_wt_nonempty: the type HomeWt b Z of the link's private inputs
(Johnson/LinkSim/AtHome/SpecHome.lean) has a member. The member has the zero matrix as its index.
For each of the two tables, its encoding randomness is entry 0 of the enumeration riDigits Z
(Johnson/Goal/Conditions/WideDigits.lean), and its seed is some OOD seed; which seed is not said.
home_valid_exists: there are a private input w and an instance x that are valid (validLk,
Johnson/LinkSim/Spec.lean) at the range of all indices and the set of all seeds. x is the pair of
w's two honest OOD samples. It follows from the first alone: x is chosen as w's two samples, so it
says nothing of the samples, the encoder or the link.

Why. A statement "for all private inputs" over an empty type would be vacuous. This file rules out
that one way of being vacuous, and no other; the file's name is wider than what it proves.

How it fits. It guards every statement of the folder that begins "for every private input w : HomeWt
b Z", such as homeExact, homeExactAt and two_plains. home_wt_nonempty is used by the three forms
that say "there are two valid private inputs": two_indices, two_views_valid and two_plains_valid.
home_valid_exists is used by nothing in this folder.

Names (namespace OnBytes.LinkSim.AtHome): home_wt_nonempty, home_valid_exists.

Limits. Only at the widest range and seed set: that a statement "for all valid pairs" (homeExact,
Johnson/LinkSim/AtHome/Home.lean) is not vacuous for want of a valid pair is proved for the range of
all indices and the set of all seeds. At a narrower range or set nothing is said.
The member's index is the zero matrix.

Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtHome.HomeTies
import Johnson.Goal.Conditions.HomeIdle

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

/- These definitions are made irreducible here, so that Lean does not unfold them while it
elaborates. This is for speed; the kernel still checks every proof. -/
attribute [local irreducible] theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem riDigits fieldRows

/-- **The private inputs are not an empty type.** -/
theorem home_wt_nonempty (b : PublicFiles → ℕ) (Z : PublicFiles) : Nonempty (HomeWt b Z) := by
  obtain ⟨e⟩ : Nonempty (homeR b Z).protocol.OutOfDomainSeed :=
    (recZ frS.P.T.l 29 1).ne
  exact ⟨((fun _ _ => 0 : Cells (frS.toDecR frZ 402653181) numsRef),
    (padB b Z ((riDigits Z).e 0), e), (padB b Z ((riDigits Z).e 0), e))⟩

/-- **A valid pair exists**, at the range of all indices and the set of all seeds. -/
theorem home_valid_exists (b : PublicFiles → ℕ) (Z : PublicFiles) :
    ∃ (w : HomeWt b Z) (x : RecFull × RecFull),
      validLk (homeR b Z).protocol (fun _ => True) (fun _ => True) w x := by
  obtain ⟨w⟩ := home_wt_nonempty b Z
  exact ⟨w, _, trivial, trivial, trivial, rfl⟩

end OnBytes.LinkSim.AtHome

#print axioms OnBytes.LinkSim.AtHome.home_wt_nonempty
#print axioms OnBytes.LinkSim.AtHome.home_valid_exists
