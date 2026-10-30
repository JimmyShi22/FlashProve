-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/H2K5R/SeatedStates.lean: KIND K5: WHAT THE SEATED BLOCK STATES: at an
attention link of the proof file's description the third hearing block's named runs of claims are
the kind's own four (runsN a), each behind the seat's guard on the reply.

Why. The readers of a link (K9.readersOfLink, Johnson/Desc/First/Batch/ReadersOfLink.lean) read what
the link's blocks state. The seat lays the lot's block under wrappers, and these do not keep its
runs of claims as they are: each stands behind a guard (IM.claims_alone). A law that speaks of the
kind's own runs meets the seated link through this equation.

Main names:
  `same_of_out`: two states of the verifier with one field "out" pass the seat's test on the reply.
  `K05_states_of_open`: **from an opening, at every o, where the proof covers attention, for g below
    the number of groups with plan a**: the link Lk at 2 g + 1, its third hearing block E, and
    K9.statesOfLink Lk 2 = (runsN a).map fun r => (r.1, IM.guardRun ProofFile.sameReply r.2).
OVER WHAT IT STANDS: all that LawAtEntry.lean's head names.
No soundness of the protocol is claimed.
Nothing is claimed on completeness or hiding.

-/
import Johnson.H2K5R.LawAtEntry
import Johnson.Desc.First.Batch.ReadersOfLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Claim Block Chain Link FileDescription)

/-- One field "out": the seat's test on the reply says yes. -/
theorem same_of_out (s t : First.S) (h : t.out = s.out) : ProofFile.sameReply s t = true := by
  unfold ProofFile.sameReply
  rw [h]
  exact beq_self_eq_true _

/-- **WHAT THE SEATED BLOCK STATES.** -/
theorem K05_states_of_open {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block First.S Claim)}
    {c : Chain First.S Claim} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (O : IM.Open o pol lay KL F Z Bs base c A B) (h4 : Bs.G₀.W.p4 = true) {g : ℕ}
    (hg : g < Bs.G₀.W.NGr) {a : Attention.Plan} (ha : Bs.G₀.W.A[g]? = some a) :
    ∃ (Lk : Link First.S Claim) (E : Block First.S Claim), c.links[2 * g + 1]? = some Lk ∧
      Lk.hear[2]? = some E ∧
      VerifiableInference.Desc.K9.statesOfLink Lk 2 =
        (runsN a).map fun r => (r.1, IM.guardRun ProofFile.sameReply r.2) := by
  obtain ⟨Lk, E, blk, e1, e2, hat, hla⟩ := k5_alone O h4 hg
  obtain ⟨a', ea', eb⟩ := k5AtN_is _ _ _ _ _ hat
  obtain rfl : a' = a := Option.some.inj (ea'.symm.trans ha)
  refine ⟨Lk, E, e1, e2, ?_⟩
  unfold VerifiableInference.Desc.K9.statesOfLink
  rw [e2]
  show E.claims = _
  rw [IM.claims_alone hla]
  show blk.claims.map _ = _
  rw [eb]
  rfl

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.same_of_out
#print axioms VerifiableInference.Desc.First.Att.P.K05_states_of_open
