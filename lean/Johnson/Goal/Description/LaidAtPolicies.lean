-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Description/LaidAtPolicies.lean: where the plan's seat of the description holds a plan
at `storedPublicFiles`, it holds one at all public files in the goals' scope that differ from `storedPublicFiles` in the
numbers C, theta, cap of the acceptance policy alone.

`storedPublicFiles` is a set of three public files as Ladder/Stored.lean spells them. "Differ in the policy
alone": the scale file is `storedPublicFiles`'s, and the parameter file is `policyFile` at the stored free
numbers with C, theta, cap in the place of 256, 256, 0. The layout file is `storedPublicFiles`'s at all files in
scope.

Why. Statements that tie the committer that runs to the committer as mathematics ask that the
frame's salts have 40 bytes, which in scope says that the plan's seat holds a plan
(Johnson/Bind/Cpp/SaltAt.lean). This file carries that from one policy to another from the seat's
own return. The laws that carry the test `protocolDataWellFormed` (Johnson/LPFPol/LiveAtPolicy.lean) start from a
yes of `protocolDataWellFormed`, which asks all three seats' returns.

Main names.
* `laid_at_policy_of_full`: THE STATEMENT. Four calls: the plan out of the seat's return;
  `plannedAtO_public`; `LPFPol.publicOfO_returns_inScope` (Johnson/LPFPol/PublicInScope.lean): the
  public part returns at the second files; `LPFPol.planLaid_wp` (Johnson/LPFPol/PlanSeat.lean): so
  the seat holds a plan there.
* `laid_gap_of_full`: the same at `zGap`, which is `storedPublicFiles` under the policy (25856, 512, 1).
* `plannedAtO_public`: what the planner's text with the digest as an argument returns holds the
  public part that `publicOfO` returns.
* `thePlanLaid_eq`: the seat's text. `lay_of_scope`: files in scope have `storedPublicFiles`'s layout file.

Limits.
* AN IMPLICATION. THAT THE SEAT HOLDS A PLAN AT `storedPublicFiles` IS SHOWN NOWHERE IN THIS FILE OR BENEATH IT.
  Until it is a theorem, these statements say nothing of any file.
* That Z is in scope is a premise. At which policies the files are in scope:
  Johnson/Goal/Files/ScopeAtPolicies.lean.
* The two plans are not shown to be one but for the policy: "there is a plan" is all that is said.
* The five other free numbers and the scale file are `storedPublicFiles`'s. Files in scope can differ in these
  too: of such files nothing is said.
* The seat lays its plan at a constant in the digest's place (`fixedConfigurationDigest`: 32 bytes of 1), at all
  files: nothing here stands at the files' own digest.
* `storedPublicFiles` is a term written in Ladder/Stored.lean. No Lean ties it to files in a folder of examples,
  and the example's weights are synthetic (that file's head).
* Nothing is said on what the head's link's check does under any policy: no test of a policy is
  shown to be right or to be run. Nothing on soundness, on binding, on hiding or on a security
  level.

-/
import Johnson.LPFPol.PlanSeat
import Johnson.LPFPol.PublicInScope
import Johnson.Goal.Files.ScopeExample

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FlashProve
open VerifierAndGoals
open OnBytes OnBytes.Model OnBytes.Model.Verify
open OnBytes.Params (exc_bind)
open VerifiableInference.PlanWritten (publicOfO plannedAtO)

/-- What the planner's text with the digest as an argument returns holds the public part that
publicOfO returns. -/
theorem plannedAtO_public {o : Nat → ByteArray → ByteArray} {pol KL c : ByteArray}
    {layout : Option ByteArray} {p : Verify.Planned} (h : plannedAtO o pol KL layout c = .ok p) :
    publicOfO o pol KL layout = .ok p.X := by
  unfold plannedAtO at h
  obtain ⟨X, hX, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  cases h
  exact hX

/-- The plan's seat is the planner's text at the constant in the digest's place. -/
theorem thePlanLaid_eq (Z : PublicFiles) :
    thePlanLaid (asDescriptionFiles Z) =
      (plannedAtO secondHashFunction Z.pol Z.KL (some Z.lay) fixedConfigurationDigest).map VerifiableInference.OnPublicFiles.bigReq :=
  rfl

/-- Public files in scope have the layout file of `storedPublicFiles`. -/
theorem lay_of_scope {Z : PublicFiles} (hZ : InScope Z = true) : Z.lay = storedPublicFiles.lay := by
  by_contra h
  have e := outOfScope_of_lay h
  rw [hZ] at e
  cases e

/- The named files stay folded: left to unfold them, Lean compares whole files byte by byte and runs
out of stack (Johnson/Goal/Files/FilesReadProof.lean's own note). -/
attribute [local irreducible] storedPublicFiles

/-- **Where the plan's seat holds a plan at `storedPublicFiles`, it holds one at all public files in scope that
differ from `storedPublicFiles` in the numbers C, theta, cap alone.** -/
theorem laid_at_policy_of_full {Z : PublicFiles} {C theta cap : Nat} (hZ : InScope Z = true)
    (hK : Z.KL = storedPublicFiles.KL)
    (hpol : Z.pol = policyFile { storedLines with C := C, theta := theta, cap := cap })
    (h : ∃ G, thePlanLaid (asDescriptionFiles storedPublicFiles) = .ok G) : ∃ G', thePlanLaid (asDescriptionFiles Z) = .ok G' := by
  obtain ⟨G, hG⟩ := h
  obtain ⟨p, hp, -⟩ := LPFPol.map_ok ((thePlanLaid_eq storedPublicFiles).symm.trans hG)
  have hX := plannedAtO_public hp
  have hX0 := hX
  rw [pol_zFull] at hX0
  have hZ' : InScope ⟨policyFile { storedLines with C := C, theta := theta, cap := cap }, Z.lay,
      storedPublicFiles.KL⟩ = true := by
    rw [← hpol, ← hK]
    exact hZ
  have hX' := LPFPol.publicOfO_returns_inScope hX0 hZ'
  obtain ⟨G', hG', -, -⟩ := LPFPol.planLaid_wp hX hX'
    (show filesParametersOrRefusalAt secondHashFunction ⟨storedPublicFiles.pol, storedPublicFiles.lay, storedPublicFiles.KL⟩ = .ok G from hG)
  refine ⟨G', ?_⟩
  show filesParametersOrRefusalAt secondHashFunction ⟨Z.pol, Z.lay, Z.KL⟩ = .ok G'
  rw [hpol, hK, lay_of_scope hZ]
  exact hG'

/-- **Where the plan's seat holds a plan at `storedPublicFiles`, it holds one at `zGap`.** -/
theorem laid_gap_of_full (h : ∃ G, thePlanLaid (asDescriptionFiles storedPublicFiles) = .ok G) :
    ∃ G', thePlanLaid (asDescriptionFiles zGap) = .ok G' :=
  laid_at_policy_of_full inScope_gap Read.kl_zGap pol_zGap h

end FlashProve

#print axioms FlashProve.plannedAtO_public
#print axioms FlashProve.thePlanLaid_eq
#print axioms FlashProve.lay_of_scope
#print axioms FlashProve.laid_at_policy_of_full
#print axioms FlashProve.laid_gap_of_full
