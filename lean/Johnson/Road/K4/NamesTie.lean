-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/NamesTie.lean: THE NAMES' TIE, AS A THEOREM IN THE GOALS' SCOPE: at an opening of
the IOP as written in Lean, at each of the twelve feed-forward segments and each of its nine
matrices, the name that the public part's own built segment lists at the matrix's tree is (owner,
name) by the public parameters' label. Two statements: names_at_links
(Johnson/Road/K4/Names/NamesAtLinks.lean) called on the plain road to Z.p.built. One is the
form without an opening: of an opening's clauses the proof spends one.

  **`names_tie_plain`**: see its statement. PREMISES: the scope (hS, hR) · hZ: the plain road
    returns the public part Z, at our second, non-standard hash OnBytes.secondHashFunction · g < 12 · μ below
    the library's own number of matrices of segment 2 g. NO OPENING.
  `names_tie`: the same at an opening O: hZ := O.pub.
The road to Z.p.built is that of Johnson/Road/K4/Riders/BuiltNs.lean.
Limits. AT OnBytes.secondHashFunction ALONE: the library's laws over publicOf are spent. That the plain road
returns is a premise. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on
soundness.


-/
import Johnson.Road.K4.Names.NamesAtLinks
import Johnson.Road.K4.Riders.PlanOfScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (SubPlanH)
open VerifiableInference.Desc (Block FileDescription)
open VerifiableInference.Desc.First (S)
open Meaning (labAt ownerK ownerA nameOf)

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {c : VerifiableInference.Desc.Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The names' tie, in the goals' scope, where the plain road returns the public part.** -/
theorem names_tie_plain (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction Pb.pol ly Pb.KL = .ok Z) {g : ℕ} (hg : g < 12) {μ : ℕ}
    (hμ : μ < (_root_.Meaning.sizesOf Z.p.X (2 * g)).NM) :
    ((Z.p.built.links.map (·.arrayOf)).getD (2 * g) #[])[(Meaning.tlAt Z.p.X
        (2 * g)).gtTree.getD μ 0]? =
      some (ownerK (labAt Z.p.X (2 * g) μ), nameOf (ownerA (labAt Z.p.X (2 * g) μ))) := by
  have hpub : Verify.publicOf Pb.pol Pb.KL (some ly) = .ok Z.p.X := by
    rw [← VerifiableInference.PlanWritten.publicOfO_older]
    exact ProofFile.Law.pub_public
      (show ProofFile.pureRoad.pub OnBytes.secondHashFunction Pb.pol ly Pb.KL = .ok Z from hZ)
  obtain ⟨k4, kN, _, hA⟩ := Meaning.scope_plans hS hR hpub
  have C := Hd.core_of_scope hS hR hpub
  have hB : ProofFile.Plain.builtOf Z.p.X Z.p.chains = .ok Z.p.built :=
    IM.planned_built (ProofFile.Law.madeOf_planned (ProofFile.Law.pubBy_made
            (show ProofFile.pubBy (ProofFile.PlainG.madeOf OnBytes.secondHashFunction) ProofFile.plainStarts Pb.pol ly Pb.KL = .ok Z
              from hZ)))
  obtain ⟨l₀, h₀, hB⟩ := IM.plain_built hB
  unfold ProofFile.Plain.linksPlain at h₀
  rw [k4] at h₀
  obtain ⟨_, _, _, p0, _⟩ := OnBytes.L5.LinksOrder.listLinksH_with _ _ _ _ _ h₀
  refine Names.names_at_links hpub C k4 kN (fun g' hp hg' hgp => ?_) hB hg hμ
  obtain ⟨a, ha, _⟩ := hA g' hg'
  have s0 : (Z.p.X.G.map fun hp : Layer.HPlan2 =>
      ({ tl := hp.tl, Fp := hp.Fp, Tp := hp.Tp, ns := hp.ns, NCL := hp.NCL,
         run := ProofFile.Plain.notToBeRun } : SubPlanH))[g']? =
      some { tl := hp.tl, Fp := hp.Fp, Tp := hp.Tp, ns := hp.ns, NCL := hp.NCL,
             run := ProofFile.Plain.notToBeRun } := by
    rw [Array.getElem?_map, hgp]
    rfl
  have t0 : (Z.p.X.A.map fun A : Attention.Plan =>
      ({ tl := A.seam.tl, Fp := A.seam.Fp, Tp := A.seam.Tp, ns := A.ns,
         run := ProofFile.Plain.notToBeRun } : SubPlanH))[g']? =
      some { tl := a.seam.tl, Fp := a.seam.Fp, Tp := a.seam.Tp, ns := a.ns,
             run := ProofFile.Plain.notToBeRun } := by
    rw [Array.getElem?_map, ha]
    rfl
  obtain ⟨q0, _⟩ := p0 g' _ _ s0 t0
  exact ⟨_, q0, rfl⟩

/-- The same at an opening of the IOP as written in Lean. -/
theorem names_tie (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12) {μ : ℕ}
    (hμ : μ < (_root_.Meaning.sizesOf Z.p.X (2 * g)).NM) :
    ((Z.p.built.links.map (·.arrayOf)).getD (2 * g) #[])[(Meaning.tlAt Z.p.X
        (2 * g)).gtTree.getD μ 0]? =
      some (ownerK (labAt Z.p.X (2 * g) μ), nameOf (ownerA (labAt Z.p.X (2 * g) μ))) :=
  names_tie_plain hS hR O.pub hg hμ

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.names_tie_plain
#print axioms OnBytes.Road.K4.names_tie
