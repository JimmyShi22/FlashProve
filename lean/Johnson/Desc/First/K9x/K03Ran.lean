-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/K9x/K03Ran.lean: THE ROW K03_sits AT THE PROOF FILE, ITS SECOND ARM: "ITS YES
GIVES THAT LAW's PREMISE". K03_law's Lean statement (`K3ClaimsGiveOut`,
Johnson/Top/H/K3OutStatement.lean) asks, behind the kind's own yes, `K3RanAt` of three runs of
claims and one ledger that is later than all three. Here a yes of the description that
`ProofFile.onlineDescription` returns gives, at every lookup of every link, the link's trace and `RanAllUpTo`: NO
PREMISE IS LEFT BUT `onlineDescription … = .ok F` AND F's YES. Theorems with their proofs.

WHOSE LAWS ARE SPENT, each of its lot's own block's decision: K1: `k1Pure_steps` ·
K3: `stated_steps_look`, with `k03_lot_is` · K4: `k4C_stepsFo` · K5:
`lotN_stepsFo` · K6: `k6_lot_steps` · K8: `whole_steps_carriesFo` · K11:
`K11.blkAt_steps_look` | `_tl`.

  `kindsStepLook`: the seven fields of `KindsStep S.lookHeard? Z G`, at every Z and G.
  `mergeStepsDigits`: the merge's law at the reading `heardD`.
  **`k03_ran_calls`**: `onlineDescription o pol lay KL = .ok F` gives the public part Z and
    `RoadAtK3 S.lookHeard? (fun _ => True) o Z F` (RoadPaid.lean).
  **`k03_ran_digits`**: the like at `heardD`, at the second lookup of every link:
    `RoadAtK3 heardD (6 ≤ ·) o Z F`.

Limits. Frame's laws: no error; nothing on soundness. WHAT STAYS THE ROW's DEBT: inside `RanUpTo` |
`RanAllUpTo`: that the record behind the lookup's decision holds something as heard, and a ledger
with its sizes: the first is the lookups' law's own conclusion where the ledger in front has its
sizes; "sized from the link's start" is not joined here. At a layers' link and at the digits the
lookup's second and third runs lie inside another kind's run: `k3RanInside` (K3RanAtN.lean) with the
caller's law. Nothing on transcripts. NO MEMBER: that `onlineDescription` returns, or that F says yes,
anywhere, is a run's word.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.K9x.RoadPaid
import Johnson.P5K3R.SitsLot
import Johnson.Desc.K1.Law.CarriesAtLot
import Johnson.Desc.First.Look.K3StatedSteps
import Johnson.Desc.ProofFile.Lot.K5StepsFo
import Johnson.P4R.LotSteps
import Johnson.Desc.First.K8.LawRuns
import Johnson.Top.H0.MergeLaw.StepsFo

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open ProofFile (Pub Ground Cl Inst pureSeat onlineDescription pureRoad)

/-- **The seven laws at what the lookup on the calls was heard to return.** -/
theorem kindsStepLook (Z : Pub) (G : Ground) : KindsStep S.lookHeard? Z G where
  k1 := by
    intro b hb _
    rcases IM.blocks_mem hb with ⟨x, hx, rfl⟩ | h
    · exact K1.k1Pure_steps Z G x hx
    · exact nomatch h
  k3 := fun b hb hp =>
    OnPublicFiles.stated_steps_look _ _ _ _ _ _ b (K3Lot.k03_lot_is hb) hp
  k4 := by
    intro b hb _
    rcases IM.blocks_mem hb with ⟨x, hx, -⟩ | h
    · exact nomatch hx
    · obtain ⟨x, _, rfl⟩ := List.mem_map.1 h
      exact OnBytes.Desc.First.K4.k4C_stepsFo OnBytes.Desc.First.K4.keepsIn_look
        { x.2 with k3Runs := true }
  k5 := fun _ hb hp => H2K5.lotN_stepsFo hb hp
  k6 := fun _ hb _ => P4.k6_lot_steps hb
  k8 := by
    intro b hb _
    rcases IM.blocks_mem hb with ⟨x, hx, -⟩ | h
    · exact nomatch hx
    · obtain ⟨x, _, rfl⟩ := List.mem_map.1 h
      exact First.K8.whole_steps_carriesFo _
  k11 := by
    intro b hb _
    rcases IM.blocks_mem hb with ⟨x, hx, -⟩ | h
    · exact nomatch hx
    · obtain rfl := List.mem_singleton.1 h
      exact K11.blkAt_steps_look Z G

/-- The merge's law at what the lookup on the digits was heard to return. -/
theorem mergeStepsDigits (Z : Pub) (G : Ground) :
    ∀ b ∈ (K11.lot Z).blocks G, b.planOk = true → b.Steps (CF heardD) := by
  intro b hb _
  rcases IM.blocks_mem hb with ⟨x, hx, -⟩ | h
  · exact nomatch hx
  · obtain rfl := List.mem_singleton.1 h
    exact K11.blkAt_steps_tl Z G fun t => t.bind (·.heard)

/-- **K03_sits' SECOND ARM AT THE LOOKUP ON THE CALLS** (and, at that reading, at both lookups). -/
theorem k03_ran_calls (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (F : FileDescription Inst)
    (h : onlineDescription o pol lay KL = .ok F) :
    ∃ Z, pureRoad.pub o pol lay KL = .ok Z ∧ RoadAtK3 S.lookHeard? (fun _ => True) o Z F := by
  obtain ⟨Z, hZ, hr⟩ := ranAtDescPureNLook o pol lay KL F h
  exact ⟨Z, hZ, roadAtCalls hr (kindsStepLook Z)⟩

/-- **K03_sits' SECOND ARM AT THE LOOKUP ON THE DIGITS.** -/
theorem k03_ran_digits (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (F : FileDescription Inst)
    (h : onlineDescription o pol lay KL = .ok F) :
    ∃ Z, pureRoad.pub o pol lay KL = .ok Z ∧ RoadAtK3 heardD (6 ≤ ·) o Z F := by
  obtain ⟨Z, hZ, hr⟩ := ranAtDescPureNDigits o pol lay KL F h
  exact ⟨Z, hZ, roadAtDigits hr (mergeStepsDigits Z)⟩

end VerifiableInference.Desc.K9

#print axioms VerifiableInference.Desc.K9.kindsStepLook
#print axioms VerifiableInference.Desc.K9.mergeStepsDigits
#print axioms VerifiableInference.Desc.K9.k03_ran_calls
#print axioms VerifiableInference.Desc.K9.k03_ran_digits
