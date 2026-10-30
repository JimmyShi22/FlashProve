-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Riders/BuiltNs.lean: THE NUMBER OF SLOTS THAT THE BUILT SEGMENT 2 g BEARS IS THAT
OF THE GROUP's OWN LIST OF NUMBERS hp. WHY: the composed meaning's public test freeAbove reads the
number of slots of segment m as (built[m]?).map (·.ns) (pubD.nsOf, Johnson/Desc/Sound/MgAll.lean;
NOT IMPORTED), while K4's sub-protocol and the row's structure K4RowPlan speak of par.hp.ns: were
the two numbers apart, the promise in front of K4 would hold at no state that K4's law wants.

  `built_ns_plain`: at every function o in the place of our second, non-standard hash (built on
    BLAKE2b's compression function): where pubPlain o returns Z, with attention's segments
    (p4 = true), group g's entries of Z.p.X.G and Z.p.X.A being hp and a: the built segment 2 g is
    there and bears hp.ns. Premises: the return (the opening's field pub) · three lines on the
    public parameters (in the goals' scope: Meaning.scope_plans and IM.k4_of).
  **`built_ns`**: in the goals' scope, at an opening of the IOP as written in Lean, g < 12, at
    every member x of K4's lot's list that bears the number 2 g, at every array built that is
    Z.p.built.links: (built[2 * g]?).map (·.ns) = some x.2.hp.ns. Premises: the scope (hS, hR) ·
    the opening O · hx, hl (k04_sits_desc gives such an x) · hb (whoever fills the composed
    meaning's parameter built).
No new argument: the text of ProofFile.Plain.linksPlain; listLinksH_with
(OnBytes/Tie/Pv/Keeps/LinksOrder.lean's namespace OnBytes.L5.LinksOrder); Meaning.built_at
(Johnson/Goal/Meaning/PlanShapes.lean); IM.planned_built, IM.plain_built
(Johnson/IMR/PureJoin.lean); k4Of_of_open, k04_sits_one
(Johnson/Road/K4/K04Sits.lean).
Limits. That there is an opening is shown by no theorem (IM.seat_open: wherever onlineDescription returns).
hb is a premise. Nothing on the other fields of a built segment. K04_law, the law of K4's
sub-protocol itself, IS NOT PROVED. Nothing on soundness.


-/
import Johnson.Road.K4.Riders.PlanOfScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Riders

open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH SubPlanH)
open OnBytes.Desc.First.K4 (Par)
open VerifiableInference.Desc (Block FileDescription)
open VerifiableInference.Desc.First (S)

/-- Where the plain road returns the public part Z: the built segment 2 g bears the number of slots
of group g's own list of numbers. -/
theorem built_ns_plain {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) (h4 : Z.p.X.p4 = true) {g : ℕ} {hp : Layer.HPlan2}
    {a : Attention.Plan} (hgp : Z.p.X.G[g]? = some hp) (ha : Z.p.X.A[g]? = some a) :
    (Z.p.built.links[2 * g]?).map (·.ns) = some hp.ns := by
  have hB : ProofFile.Plain.builtOf Z.p.X Z.p.chains = .ok Z.p.built :=
    IM.planned_built (ProofFile.Law.madeOf_planned (ProofFile.Law.pubBy_made
            (show ProofFile.pubBy (ProofFile.PlainG.madeOf o) ProofFile.plainStarts pol lay KL = .ok Z from hZ)))
  obtain ⟨l₀, h₀, hB⟩ := IM.plain_built hB
  unfold ProofFile.Plain.linksPlain at h₀
  rw [h4] at h₀
  obtain ⟨_, _, _, p0, _⟩ := OnBytes.L5.LinksOrder.listLinksH_with _ _ _ _ _ h₀
  have s0 : (Z.p.X.G.map fun hp : Layer.HPlan2 =>
      ({ tl := hp.tl, Fp := hp.Fp, Tp := hp.Tp, ns := hp.ns, NCL := hp.NCL,
         run := ProofFile.Plain.notToBeRun } : SubPlanH))[g]? =
      some { tl := hp.tl, Fp := hp.Fp, Tp := hp.Tp, ns := hp.ns, NCL := hp.NCL,
             run := ProofFile.Plain.notToBeRun } := by
    rw [Array.getElem?_map, hgp]
    rfl
  have t0 : (Z.p.X.A.map fun A : Attention.Plan =>
      ({ tl := A.seam.tl, Fp := A.seam.Fp, Tp := A.seam.Tp, ns := A.ns,
         run := ProofFile.Plain.notToBeRun } : SubPlanH))[g]? =
      some { tl := a.seam.tl, Fp := a.seam.Fp, Tp := a.seam.Tp, ns := a.ns,
             run := ProofFile.Plain.notToBeRun } := by
    rw [Array.getElem?_map, ha]
    rfl
  obtain ⟨q0, _⟩ := p0 g _ _ s0 t0
  obtain ⟨ar, e⟩ := (Meaning.built_at hB).2 (2 * g) _ q0
  rw [e]
  rfl

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}

/-- **In the goals' scope, at an opening, at every member of K4's lot's list that bears the number
2 g, g < 12: the built segment's number of slots is the member's.** -/
theorem built_ns {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    {c : VerifiableInference.Desc.Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {x : Bool × Par} (hx : x ∈ ProofFile.k4From Z Bs.G₀ Bs.G₀.built.toList 0 none)
    (hl : x.2.link = 2 * g) {built : Array LinkH} (hb : built = Z.p.built.links) :
    (built[2 * g]?).map (·.ns) = some x.2.hp.ns := by
  subst hb
  obtain ⟨k4, _, _, hA⟩ := Meaning.scope_plans hS hR O.public
  obtain ⟨a, ha, _⟩ := hA g hg
  obtain ⟨_, _, y, _, _, e3, _, e5, _, _, e8, _⟩ := k4Of_of_open hS hR O g hg
  obtain rfl : x = y := k04_sits_one hx e3 hl e5
  rw [O.W] at k4 ha e8
  exact built_ns_plain O.pub k4 e8 ha

end OnBytes.Road.K4.Riders

#print axioms OnBytes.Road.K4.Riders.built_ns_plain
#print axioms OnBytes.Road.K4.Riders.built_ns
