-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/HomeServed.lean: THE CLAUSE "served" OF EndFits
(Johnson/Goal/Conditions/HomeEnd.lean) PAID, at a written instance of a request and a written set of
true instances: in scope, where the reader returns: a served request with the model's own output is
built by the input's builder, and what is built is a true instance at the weights' index.

Main names.
  valB   a request of the input at b, as the library's instance: the passage is made at a letter b.
  xAt b Z x₀   THE INSTANCE OF A REQUEST: what the input's builder builds; x₀ where it builds
    nothing.
  yesAt b Z hr   THE TRUE INSTANCES: (i, x): i is the index that stands for some weights w, and x is
    true under the files' policy at w's index (Policy.IsTrueUnder).
  served_home   THE STATEMENT. yesAt_met   the set is not empty.

Calls: true_of_served, served_met (Johnson/Goal/Meaning/ServedMeans.lean); build_home_of_built
(Johnson/Prover/At/HomeMore.lean).

Limits. It says nothing on whether the honest records accept at all of yesAt: that is the clause
"honest", which stays a premise: if the description's lookups admit less than the integer model's 16
bits, "honest" can hold at this set only at error terms that sum to at least 1 (argued on paper, not
proved: Johnson/Goal/Conditions/HomeEnd.lean, limit 2). No completeness.
This file states no goal.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.HomeAtWider
import Johnson.Prover.At.HomeMore
import Johnson.Goal.Meaning.ServedMeans

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles

/- Lean compares these by their names. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem riDigits fieldRows

variable (b : PublicFiles → ℕ) (Z : PublicFiles)

/-- A request of the input at b, as the library's instance. -/
def valB (x : (homeR b Z).Instance) : Inst.Model.Instance Inst.Model.ppref := (show Flat.Req from x).1

/-- **The instance of a request**: what the input's builder builds. -/
def xAt (x₀ : (homeR b Z).Instance) (p o : List Token) : (homeR b Z).Instance :=
  ((homeR b Z).buildInstance (p, o) []).getD x₀

variable {pp : Inst.Model.ScalesAndPolicy}

/-- **The true instances**: at the index that stands for weights w: the requests that are true under
the files' policy at w's index. -/
def yesAt (hr : readFiles Z = .ok pp) (i : (homeR b Z).Index) (x : (homeR b Z).Instance) : Prop :=
  ∃ w : ModelWeights (settingsOfRead pp), i = backB b Z (settingsOfRead pp) w ∧
    Policy.IsTrueUnder (Cm.Scales.of pp) pp.pol (indexOfWeights (valid_of_read hr) w) (valB b Z x)

/-- **The clause "served".** -/
theorem served_home (scope : InScope Z = true) (hr : readFiles Z = .ok pp) (x₀ : (homeR b Z).Instance)
    (w : ModelWeights (settingsOfRead pp)) (p o : List Token)
    (hd : CanServe (settingsOfRead pp) w p o) (hm : ModelOutput (settingsOfRead pp) w p o) :
    (homeR b Z).buildInstance (p, o) [] = some (xAt b Z x₀ p o) ∧
      yesAt b Z hr (backB b Z (settingsOfRead pp) w) (xAt b Z x₀ p o) := by
  obtain ⟨x, hx, hT⟩ := Meaning.true_of_served scope hr w p o hd hm
  have hb := build_home_of_built b Z hx
  have e : xAt b Z x₀ p o = ⟨x, Flat.wellFormed_of_built hx⟩ := by
    unfold xAt
    rw [hb]
    rfl
  rw [e]
  exact ⟨hb, w, rfl, hT⟩

/-- The set is not empty. -/
theorem yesAt_met (scope : InScope Z = true) (hr : readFiles Z = .ok pp) (x₀ : (homeR b Z).Instance) :
    ∃ i x, yesAt b Z hr i x := by
  obtain ⟨w, p, o, hd, hm⟩ := Meaning.served_met hr
  exact ⟨_, _, (served_home b Z scope hr x₀ w p o hd hm).2⟩

end FlashProve

#print axioms FlashProve.served_home
#print axioms FlashProve.yesAt_met
