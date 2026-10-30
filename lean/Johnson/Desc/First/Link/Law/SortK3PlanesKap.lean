-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SortK3PlanesKap.lean: WHAT IS LEFT OF A LINK's LAW (K9): ANOTHER FILE's
FIELD k3k (a yes of a run at a lookup's entry leaves, of the open ledger, the map of handed-out
weights, the plan's number of claims and the count of claims) AT THE ENTRY "planes": PAID, IN THE
GOALS' SCOPE, WHERE THE CALLING KIND's READERS ARE THERE. One theorem: a call. IT PAYS NO LAW OF ITS
OWN. The field k3k stands in LinkRestAtSort3C.lean.

  k3k_planes    At L (IM.k3Ix m false, "planes") run ⊢ ∀ n e cl e₁, run n e = .ok (cl, e₁) → the
                three numbers of e₁'s open ledger are e's: by the tie at_planes_is
                (SortK3Planes.lean) and planes_kap · kapOf_of_puts
                (Johnson/Top/H/Keep/PutsKap.lean)
THE END IS WRITTEN IN kapOf_of_puts's OWN UNFOLDED TEXT (see SortK3ObjectsKap.lean's head).

PREMISES: hS hR O · m < 25 · hL : c.links[m]? = some L · hr : K3Lot.readersAt Bs.G₀.W m = some r.
Limits. NO MEMBER: no state is shown at which the run says yes. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.SortK3Planes
import Johnson.Top.H.Keep.PutsKap

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.LinkJoin (At)

/-- **k3k at "planes".** -/
theorem k3k_planes {Pf : VerifierAndGoals.PublicFiles} {pp₀ : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B) {m : ℕ} (hm : m < 25)
    {L : Link S ProofFile.Cl} (hL : c.links[m]? = some L) {r : Desc.K3.Readers S}
    (hr : K3Lot.readersAt Bs.G₀.W m = some r)
    (run : ℕ → S → Except String (List ProofFile.Cl × S)) (h : At L (IM.k3Ix m false, "planes") run) :
    ∀ n e cl e₁, run n e = .ok (cl, e₁) →
      (e₁.fork?.map fun G => (G.kapMapF, G.planClaimsF, G.nClaim)) =
        e.fork?.map fun G => (G.kapMapF, G.planClaimsF, G.nClaim) := by
  obtain ⟨p, _, rfl⟩ := at_planes_is hS hR O hm hL hr h
  exact kapOf_of_puts (planes_kap _ k03_atS2_calls p.lm r)

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3k_planes
