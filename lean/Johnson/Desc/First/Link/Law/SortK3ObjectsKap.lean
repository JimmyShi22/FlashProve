-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SortK3ObjectsKap.lean: WHAT IS LEFT OF A LINK's LAW (K9): ANOTHER
FILE's FIELD k3k (a yes of a run at a lookup's entry leaves, of the open ledger, the map of
handed-out weights, the plan's number of claims and the count of claims) AT THE ENTRIES "objects":
PAID, IN THE GOALS' SCOPE. Theorems: calls. IT PAYS NO LAW OF ITS OWN. k3k: LinkRestAtSort3C.lean.

  k3k_objects   At L (IM.k3Ix m d, "objects") run ⊢ ∀ n e cl e₁, run n e = .ok (cl, e₁) → the three
                numbers of e₁'s open ledger are e's: by the tie at_objects_is (SortK3Objects.lean)
                and objects_kap · kapOf_of_puts
                (Johnson/Top/H/Keep/PutsKap.lean)
  k3k_layers    at a layers' link (m ≠ 24): at both entries of its list
THE END IS WRITTEN IN kapOf_of_puts's OWN UNFOLDED TEXT: kapOf
(KapRuns.lean) is that text by definition, ON A WORD NOT CHECKED HERE: not imported,
not read here.

PREMISES: hS hR O · m < 25 · hL : c.links[m]? = some L.
Limits. NO MEMBER: no state is shown at which the run says yes. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.SortK3Objects
import Johnson.Top.H.Keep.PutsKap

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.LinkJoin (At)

section
variable {Pf : VerifierAndGoals.PublicFiles} {pp₀ : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
  (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
  (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B) {m : ℕ} (hm : m < 25)
  {L : Link S ProofFile.Cl} (hL : c.links[m]? = some L)
include hS hR O hm hL

/-- **k3k at "objects".** -/
theorem k3k_objects (d : Bool) (run : ℕ → S → Except String (List ProofFile.Cl × S))
    (h : At L (IM.k3Ix m d, "objects") run) :
    ∀ n e cl e₁, run n e = .ok (cl, e₁) →
      (e₁.fork?.map fun G => (G.kapMapF, G.planClaimsF, G.nClaim)) =
        e.fork?.map fun G => (G.kapMapF, G.planClaimsF, G.nClaim) := by
  rw [at_objects_is hS hR O hm d hL h]
  exact kapOf_of_puts (objects_kap _ (atS2_seatOf d))

/-- **k3k at a layers' link, whole.** -/
theorem k3k_layers (h24 : m ≠ 24) :
    ∀ o ∈ [((1 : ℕ), "objects"), (6, "objects")], ∀ run, At L o run →
      ∀ n e cl e₁, run n e = .ok (cl, e₁) →
        (e₁.fork?.map fun G => (G.kapMapF, G.planClaimsF, G.nClaim)) =
          e.fork?.map fun G => (G.kapMapF, G.planClaimsF, G.nClaim) := by
  intro o ho run h
  obtain ⟨d, rfl⟩ := objects_entry_low h24 (by simpa using ho)
  exact k3k_objects hS hR O hm hL d run h

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3k_objects
#print axioms VerifiableInference.OnPublicFiles.k3k_layers
