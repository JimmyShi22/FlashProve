-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFPol/PlanSeat.lean: the plan's seat (`FlashProve.filesParametersOrRefusalAt`,
Johnson/Goal/Description/Plan.lean) at a parameter file with another acceptance policy. A statement
and its proof.
Premises: hX, hX': `publicOfO` returns X at the first parameter file and `X.withPol C theta cap` at
the second.
  `planLaid_wp`: where the seat returns G at the first files, it returns some G' at the second, and
      the two depths that `theLive_of_returns` (Johnson/Goal/Skeleton/LiveOfReturns.lean) asks of
      are G's.
How. `ProofFile.Law.planned_eq` (Johnson/Desc/ProofFile/Law/PlainIsPlanned.lean): the plain planner is the
seat's planner but for the segments' routines, refusals too; `planned_wp`
(Johnson/LPFPol/PubPlain.lean) carries the plain planner.
Limits. hX' is a premise. G' and G are not shown to be one. Nothing on soundness.

-/
import Johnson.LPFPol.PubPlain
import Johnson.Desc.ProofFile.Law.PlainIsPlanned
import Johnson.Goal.Description.Plan

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace LPFPol
open OnBytes OnBytes.Model
open VerifiableInference.PlanWritten (publicOfO plannedAtO)
open VerifiableInference.OnPublicFiles (bigReq)
open VerifiableInference.Desc (fixedConfigurationDigest)

theorem map_ok {ε α β : Type} {x : Except ε α} {f : α → β} {b : β} (h : x.map f = .ok b) :
    ∃ a, x = .ok a ∧ f a = b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, Except.ok.inj h⟩

theorem depth_first (p : Verify.Planned) :
    (bigReq p).c.first.binding.logLeaves = p.chains.proof.first.binding.logLeaves := rfl

theorem depth_key (p : Verify.Planned) :
    (bigReq p).k.oneTime.binding.logLeaves = p.chains.key.oneTime.binding.logLeaves := rfl

theorem planLaid_wp {o : Nat → ByteArray → ByteArray} {pol pol' lay KL : ByteArray}
    {X : Verify.Public}
    {C theta cap : Nat} (hX : publicOfO o pol KL (some lay) = .ok X)
    (hX' : publicOfO o pol' KL (some lay) = .ok (X.withPol C theta cap))
    {G : OnBytes.Flat.FilesParameters LPFD.Full.XF OnBytes.Flat.RecFull}
    (hG : FlashProve.filesParametersOrRefusalAt o ⟨pol, lay, KL⟩ = .ok G) :
    ∃ G', FlashProve.filesParametersOrRefusalAt o ⟨pol', lay, KL⟩ = .ok G' ∧
      G'.c.first.binding.logLeaves = G.c.first.binding.logLeaves ∧
      G'.k.oneTime.binding.logLeaves = G.k.oneTime.binding.logLeaves := by
  obtain ⟨p, hp, rfl⟩ := map_ok (show (plannedAtO o pol KL (some lay) fixedConfigurationDigest).map bigReq =
      .ok G from hG)
  have h1 := ProofFile.Law.planned_eq o pol KL (some lay)
  rw [hp] at h1
  have h2 := planned_wp hX hX' (h1 : ProofFile.Plain.planned o pol KL (some lay) = .ok _)
  rw [ProofFile.Law.planned_eq] at h2
  obtain ⟨p', hp', e⟩ := map_ok h2
  have ec : p'.chains = p.chains := by
    have e2 := congrArg Verify.Planned.chains e
    exact e2
  refine ⟨bigReq p', ?_, ?_, ?_⟩
  · show (plannedAtO o pol' KL (some lay) fixedConfigurationDigest).map bigReq = _
    rw [hp']
    rfl
  · rw [depth_first, depth_first, ec]
  · rw [depth_key, depth_key, ec]

end LPFPol

#print axioms LPFPol.planLaid_wp
