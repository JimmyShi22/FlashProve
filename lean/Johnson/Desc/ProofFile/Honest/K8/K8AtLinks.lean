-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/K8AtLinks.lean: THE SMALLNESS TEST: THE PREMISE `K8At` OF THE LAW
ON THE COUNTS IN FRONT OF THE BATCHING (Johnson/Desc/ProofFile/Honest/K8/CountsFrontK8.lean) AT EACH
OF THE 25 LINKS OF THE PROOF FILE's DESCRIPTION, IN THE GOALS' SCOPE: at the place of the kind's own
lot. Three corollaries; none of the library's goals.

  **`k8At_layers`**, **`k8At_attention`**, **`k8At_head`**   there is the planned link Xl, and every
                   link Lk that the chain has at that number and that has its sort's orders
                   (`LinkJoin.SegAt`) has K8At Lk ‹sort› (ProofFile.k8ParW Z G₀ Xl ‹number›)
By the library's seats (`IM.k8_of_layers`, `IM.k8_of_attention`, `IM.k8_of_head`,
Johnson/IMR/K8Seat.lean) and Johnson/Desc/ProofFile/Honest/K8/K8AtSeat.lean.
Limits. THE FULL SIZE ALONE, in the goals' scope, at the format's second hash function. `SegAt` stays a
premise: the library has it of the links that its own maker lays.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.K8AtSeat
import Johnson.IMR.K8Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **At a layers' link.** -/
theorem k8At_layers (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {g : Nat} (hg : g < 12) :
    ∃ Xl : LinkH, Bs.G₀.built[2 * g]? = some Xl ∧ ∀ Lk, c.links[2 * g]? = some Lk →
      LinkJoin.SegAt (2 * g) .layers Lk →
      K8At Lk .layers (ProofFile.k8ParW Z Bs.G₀ Xl (2 * g)) := by
  obtain ⟨Lk, b, Xl, hp, e1, e2, hX, la, -⟩ := IM.k8_of_layers hS hR O g hg
  refine ⟨Xl, hX, fun Lk' hL hseg => ?_⟩
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans hL)
  exact k8At_of_alone (entry_layers hseg) e2 la

/-- **At an attention link.** -/
theorem k8At_attention (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {g : Nat} (hg : g < 12) :
    ∃ Xl : LinkH, Bs.G₀.built[2 * g + 1]? = some Xl ∧ ∀ Lk, c.links[2 * g + 1]? = some Lk →
      LinkJoin.SegAt (2 * g + 1) .attention Lk →
      K8At Lk .attention (ProofFile.k8ParW Z Bs.G₀ Xl (2 * g + 1)) := by
  obtain ⟨Lk, b, Xl, a, e1, e2, hX, la, -⟩ := IM.k8_of_attention hS hR O g hg
  refine ⟨Xl, hX, fun Lk' hL hseg => ?_⟩
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans hL)
  exact k8At_of_alone (entry_attention hseg) e2 la

/-- **At the head's link.** -/
theorem k8At_head (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) :
    ∃ Xl : LinkH, Bs.G₀.built[24]? = some Xl ∧ ∀ Lk, c.links[24]? = some Lk →
      LinkJoin.SegAt (24) .head Lk →
      K8At Lk .head (ProofFile.k8ParW Z Bs.G₀ Xl (24)) := by
  obtain ⟨Lk, b, Xl, e1, e2, hX, la, -⟩ := IM.k8_of_head hS hR O
  refine ⟨Xl, hX, fun Lk' hL hseg => ?_⟩
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans hL)
  exact k8At_of_alone (entry_head hseg) e2 la

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.k8At_layers
#print axioms ProofFile.Honest.K8.k8At_attention
#print axioms ProofFile.Honest.K8.k8At_head
