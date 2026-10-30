-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
`E2E/PackRadiiAreThePlans.lean`: every decoding radius in the full-size list of sampled messages, `Johnson.G.packFullLit`, is the
planner's own radius at a group, with the message's code, of one of the nine proximity tests of a plan computed from public files in
scope.

`packFullLit` is a literal: 119 entries (sendings) with 207 sampled messages, each with a decoding radius. The library ties it to
public files by evaluation alone (`#guard packFullLit == packFull`, at the shipped full-size example). Statements on sendings
beneath the soundness theorem read radii off it.

What this file proves.
* `pack_radii_are_the_plans`: under the premise `H2K.Sizes.LayoutGroupsAre` (see `E2E/RadiiAreThePlans.lean`), for all `Z` in scope
  and every plan `p` that the verifier's planner returns at `Z`: for every entry `x` of the list and every sampled message `y` of it
  there are a test `t` of `Johnson.Bridge.nineTests p.chains.made.sized` and a stage `z` of `t` whose group has the message's code
  and at which `radiusIn t.1 y.1 z.g = y.2`.
* `pack_radii_under_the_head`: the same at the plan of the verifier's public part, under `P5J.AtMg` (the library's bundle of
  premises: the files are in scope and read, the verifier's description is built from them, and its tests on the plan return true).
* `all_fit` (by Lean's kernel): at each of the 207 messages some group of `typedNine` fits. `fits_says`: what a true answer of the
  comparison says.
* The comparison is `groupFits cs sh e x`: the group's code is the shape's in its three numbers (the main code where the shape has
  main rows, else the mask code: the library's `sameCode`, as in `packListOf`'s own test), and `Johnson.G.radiusIn` at the group's
  setting, the shape and the group is `e`. `radiusIn` is the function by which `packListOf` computes a radius: the upper end of the
  relative radius that `Params.analysis` derives for the group, times the code's length, rounded down. `groupsOf T` lists the groups
  of the stages of a list of tests, each with its test's setting.
* `pack_comparison_can_fail`: the comparison is not vacuous: at the list's first message with one position more, no group fits.

What this file does not say.
* It is a membership, not the map. Each written radius is the planner's at some group of the plan with the message's code. It is not
  said that this group is the one that sets the radius of that message's sample (`packListOf`'s map from a message to its groups:
  see the limits in `Johnson/G/PackList.lean`), nor that `packListOf` returns this list at any files. Two groups with one code and
  different derived radii would both pass the comparison of codes; the radius then tells them apart.
* The shapes and the codes of the list are not tied to the plan here: the radii alone.
* The statements go one way: from a planner that returns.
* Which statements read which entry of the list is not shown here.
* All limits stated in `E2E/RadiiAreThePlans.lean` apply. Facts evaluated by `decide +kernel` are used here and beneath.
-/
import E2E.RadiiAreThePlans
import Johnson.G.PackLit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.Bridge.AtPlan
open OnBytes OnBytes.Params
open Johnson.G (packFullLit sameCode radiusIn)
open Johnson.Bridge (nineTests)

/-- The groups of the stages of a list of tests, each with its test's setting. -/
def groupsOf (T : List (Setting × List StageSize)) : List (Setting × GroupSize) :=
  T.flatMap fun x => x.2.map fun y => (x.1, y.g)

/-- The group has the shape's code, and the planner's radius of the shape in the group is e. -/
def groupFits (cs : Codes) (sh : OracleShape) (e : ℕ) (x : Setting × GroupSize) : Bool :=
  (if sh.mainRows != 0 then sameCode cs.base[sh.code]? x.2.main
    else sameCode cs.mask[sh.maskCode]? x.2.mask) && radiusIn x.1 sh x.2 == e

/-- **At each of the 207 sampled messages some group of `typedNine` fits.** By Lean's kernel. -/
theorem all_fit :
    (packFullLit.all fun x => x.2.all fun y => (groupsOf typedNine).any (groupFits x.1 y.1 y.2)) = true := by
  decide +kernel

/-- A control: at the list's first message with one position more, no group fits. -/
theorem pack_comparison_can_fail :
    (packFullLit.head?.bind fun x => x.2.head?.map fun y =>
      (groupsOf typedNine).any (groupFits x.1 y.1 (y.2 + 1))) = some false := by
  decide +kernel

/-- What a true answer of the comparison at a list of tests says. -/
theorem fits_says {T : List (Setting × List StageSize)} {cs : Codes} {sh : OracleShape} {e : ℕ}
    (h : (groupsOf T).any (groupFits cs sh e) = true) :
    ∃ t ∈ T, ∃ z ∈ t.2,
      (if sh.mainRows != 0 then sameCode cs.base[sh.code]? z.g.main
        else sameCode cs.mask[sh.maskCode]? z.g.mask) = true ∧ radiusIn t.1 sh z.g = e := by
  obtain ⟨x, hx, hf⟩ := List.any_eq_true.1 h
  unfold groupsOf at hx
  obtain ⟨t, ht, hx⟩ := List.mem_flatMap.1 hx
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
  unfold groupFits at hf
  rw [Bool.and_eq_true] at hf
  exact ⟨t, ht, z, hz, hf.1, beq_iff_eq.1 hf.2⟩

/-- **In scope, at every plan: each radius of the full-size list is the planner's at a group of the plan's nine tests with the message's code.** -/
theorem pack_radii_are_the_plans (groups : H2K.Sizes.LayoutGroupsAre) {Z : VerifierAndGoals.PublicFiles} (scope : VerifierAndGoals.InScope Z = true) {p : Model.Verify.Planned}
    (hp : Model.Verify.planned Z.pol Z.KL (some Z.lay) = .ok p) :
    ∀ x ∈ packFullLit, ∀ y ∈ x.2, ∃ t ∈ nineTests p.chains.made.sized, ∃ z ∈ t.2,
      (if y.1.mainRows != 0 then sameCode x.1.base[y.1.code]? z.g.main
        else sameCode x.1.mask[y.1.maskCode]? z.g.mask) = true ∧ radiusIn t.1 y.1 z.g = y.2 := by
  rw [nine_in_scope groups scope hp]
  intro x hx y hy
  exact fits_says (List.all_eq_true.1 (List.all_eq_true.1 all_fit x hx) y hy)

open VerifiableInference.PlanWritten (pinnedAt_of_row) in
open VerifiableInference.PlanWritten.Joined (made_in_scope writtenSized) in
open Johnson.G.MadeFree (Free) in
/-- The same at the plan of the verifier's public part, under `P5J.AtMg`. -/
theorem pack_radii_under_the_head {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
    (h : P5J.AtMg o Z D r Zp Np cF) :
    ∀ x ∈ packFullLit, ∀ y ∈ x.2, ∃ t ∈ nineTests Zp.p.chains.made.sized, ∃ z ∈ t.2,
      (if y.1.mainRows != 0 then sameCode x.1.base[y.1.code]? z.g.main
        else sameCode x.1.mask[y.1.maskCode]? z.g.mask) = true ∧ radiusIn t.1 y.1 z.g = y.2 := by
  obtain ⟨hm, -⟩ := h.pins
  have hy := pinnedAt_of_row (Z := Zp) (by rw [hm, Bool.or_true])
  have hsz : Zp.p.chains.made.sized = writtenSized :=
    congrArg Free.sized (made_in_scope h.scope h.laid.pub hy)
  rw [hsz, nine_written]
  intro x hx y hy'
  exact fits_says (List.all_eq_true.1 (List.all_eq_true.1 all_fit x hx) y hy')

end Johnson.Bridge.AtPlan

#print axioms Johnson.Bridge.AtPlan.all_fit
#print axioms Johnson.Bridge.AtPlan.pack_comparison_can_fail
#print axioms Johnson.Bridge.AtPlan.fits_says
#print axioms Johnson.Bridge.AtPlan.pack_radii_are_the_plans
#print axioms Johnson.Bridge.AtPlan.pack_radii_under_the_head
#check @Johnson.Bridge.AtPlan.pack_radii_are_the_plans
