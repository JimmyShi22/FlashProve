-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Riders/BuiltNcl.lean: THE BUILT SEGMENT 2 g BEARS THE NUMBER OF CLAIMS ON THE
WEIGHTS OF GROUP g's OWN LIST OF NUMBERS, hp.NCL. The road is that of
Johnson/Road/K4/Riders/BuiltNs.lean (the field ns), at the field NCL.

  `built_ncl_plain`: where the plain road returns the public part Z: the equation at
    Z.p.built.links. Premises: hZ · Z.p.X.p4 = true · the two entries of Z.p.X.G and Z.p.X.A at g.
  **`built_ncl`**: in the goals' scope (hS, hR), at an opening O of the IOP as written in Lean, at
    g < 12, at the member x of K4's lot's list that bears the number 2 g (hx, hl):
    ((Z.p.built.links[2 * g]?).map (·.NCL)).getD 0 = x.2.hp.NCL: the field ncl of d1At Z
    (Johnson/Top/H0/Fill/D1At.lean) at 2 g, written out.
Limits. That there is an opening is shown by no theorem. K04_law, the law of K4's sub-protocol
itself, IS NOT PROVED. Nothing on soundness.


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

/-- Where the plain road returns the public part Z: the built segment 2 g bears the number of
claims on the weights of group g's own list of numbers. -/
theorem built_ncl_plain {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) (h4 : Z.p.X.p4 = true) {g : ℕ} {hp : Layer.HPlan2}
    {a : Attention.Plan} (hgp : Z.p.X.G[g]? = some hp) (ha : Z.p.X.A[g]? = some a) :
    (Z.p.built.links[2 * g]?).map (·.NCL) = some hp.NCL := by
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

/-- **In the goals' scope, at an opening, at the member of K4's lot's list that bears the number
2 g, g < 12: the built segment's number of claims on the weights is the member's.** -/
theorem built_ncl {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    {c : VerifiableInference.Desc.Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {x : Bool × Par} (hx : x ∈ ProofFile.k4From Z Bs.G₀ Bs.G₀.built.toList 0 none)
    (hl : x.2.link = 2 * g) :
    ((Z.p.built.links[2 * g]?).map (·.NCL)).getD 0 = x.2.hp.NCL := by
  obtain ⟨k4, _, _, hA⟩ := Meaning.scope_plans hS hR O.public
  obtain ⟨a, ha, _⟩ := hA g hg
  obtain ⟨_, _, y, _, _, e3, _, e5, _, _, e8, _⟩ := k4Of_of_open hS hR O g hg
  obtain rfl : x = y := k04_sits_one hx e3 hl e5
  rw [O.W] at k4 ha e8
  rw [built_ncl_plain O.pub k4 e8 ha]
  rfl

end OnBytes.Road.K4.Riders

#print axioms OnBytes.Road.K4.Riders.built_ncl_plain
#print axioms OnBytes.Road.K4.Riders.built_ncl
