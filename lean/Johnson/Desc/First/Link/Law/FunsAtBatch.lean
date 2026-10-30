-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/FunsAtBatch.lean: THE LIST OF TABLES (`S.funs?`) AT A STATE THAT IS
REACHED IN FRONT OF
THE BATCHING: StretchBack.lean's walk at the relation `SameFuns` (FunsStay.lean: the list is left as
it
was). In the goals' scope. Statements and proofs: calls.

  `sameFuns_stretch`: `StretchKeeps SameFuns`.
  `funs_from_reads`: **l < 24: reached at 14 l + 9 (in front of the batching) ⊢ there is a state
reached
    at 14 l + 6 (behind the sending of the reads) with the same public part and the same list.**
  `funs_from_reads_head`: **the like at the head: from 347 back to 343.**
  `funsSkel_at_batch`: **g < 12: AT EVERY STATE REACHED IN FRONT OF THE BATCHING OF THE LAYERS'
SEGMENT 2 g
    (at 28 g + 9): ∃ funs, s.funs? = some funs ∧ shapesOf funs = layShapes Bs.G₀.W.layers g ∧ every
    table lies on the third vector**: by `funsSkel_reached`
    (Johnson/Road/K4/FunsSkelReached.lean: the same at 28 g + 5).
Limits. AT THE ATTENTION SEGMENTS AND THE HEAD NOTHING IS SAID HERE OF WHAT THE LIST IS: there the
quiet
step at the sending of the reads makes it. Nothing on the weights. No soundness statement.

-/
import Johnson.Desc.First.Link.Law.StretchBack
import Johnson.Desc.First.Link.Law.FunsStay
import Johnson.Road.K4.FunsSkelReached

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.Road.K4 (funsSkel_reached)

theorem sameFuns_stretch : StretchKeeps SameFuns where
  trans := sameFuns_trans
  k8 := k8_sameFuns
  k1 := fun q gp link piece moment arrays => k1Later_sameFuns q gp link piece moment arrays
  k3 := fun claim readers X codes shape a _ h => k3_sameFuns claim readers X codes shape a h
  k11 := k11_sameFuns

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Q : Type} {start : Q → S}

/-- **FROM THE BATCHING's BORDER BACK TO THE BORDER BEHIND THE SENDING OF THE READS.** -/
theorem funs_from_reads (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {l : ℕ} (hl : l < 24) {z : Q}
    {s' : S} (h : Reach 0 c.blocksInOrder start (14 * l + 9) (z, s')) :
    ∃ s, Reach 0 c.blocksInOrder start (14 * l + 6) (z, s) ∧ s'.funs? = s.funs? :=
  stretch_back sameFuns_stretch hS hR O hl h

/-- **THE LIKE AT THE HEAD.** -/
theorem funs_from_reads_head (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {z : Q} {s' : S}
    (h : Reach 0 c.blocksInOrder start 347 (z, s')) :
    ∃ s, Reach 0 c.blocksInOrder start 343 (z, s) ∧ s'.funs? = s.funs? :=
  stretch_back_head sameFuns_stretch hS hR O h

/-- **THE SKELETON IN FRONT OF THE BATCHING, AT THE LAYERS' SEGMENTS.** -/
theorem funsSkel_at_batch (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12) {z : Q}
    {s' : S} (h : Reach 0 c.blocksInOrder start (28 * g + 9) (z, s')) :
    ∃ funs, s'.funs? = some funs ∧
      OnBytes.Tie.Pv.Tail.Closed.shapesOf funs =
        OnBytes.Tie.Pv.Tail.Closed.layShapes Bs.G₀.W.layers g ∧
      ∀ Fn ∈ funs.toList, Fn.tree = 2 := by
  obtain ⟨s₀, r0, q0⟩ :=
    stretch_back_layers sameFuns_stretch quietLayers_sameFuns hS hR O hg h
  obtain ⟨funs, f1, f2, f3⟩ := funsSkel_reached hS hR O hg r0
  exact ⟨funs, Eq.trans q0 f1, f2, f3⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.sameFuns_stretch
#print axioms VerifiableInference.Desc.LinkJoin.funs_from_reads
#print axioms VerifiableInference.Desc.LinkJoin.funs_from_reads_head
#print axioms VerifiableInference.Desc.LinkJoin.funsSkel_at_batch
