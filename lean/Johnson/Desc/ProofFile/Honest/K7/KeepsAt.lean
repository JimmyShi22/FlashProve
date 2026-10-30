-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K7/KeepsAt.lean: what an accepting step of the next token's
sub-protocol (the kind K7) leaves of the verifier's state, as one condition that also takes a place.
One definition and four short lemmas. The condition itself, `K7MemberKeeps`, and the lemma that
proves it from an accepting step are in Honest/K7/Keeps.lean; this file adds the place.

  1  `K7KeepsAt`   the condition, by the place
  2  `K7KeepsAt.own`, `K7KeepsAt.elsewhere`, `K7KeepsAt.mark`   at the sub-protocol's own place it
     is `K7MemberKeeps`; at every other place it is false; after the step no failure mark is set
  3  `k7KeepsAt_of_step`   it holds after an accepting step of the whole sub-protocol

The place and the segment's number are computed from the ground `G`, by the terms of the lot's own
block (`P4.k7Core`, Johnson/Desc/ProofFile/Lot/K6K7.lean). So the definition does not depend on a
size.

Limits.
  * `G` is an argument. Nothing here says that it is the ground of a description.
  * `k7KeepsAt_of_step` takes as hypotheses that the sub-protocol is the lot's block joined as
    `IM.Joined` says, and that its place is the lot's block's place. Neither is proved here.
  * The lemmas state no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K7.Keeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Tied (StepYes)
open ProofFile (Cl)

/-- **What an accepting step of the next token's sub-protocol leaves of the verifier's state, by the
place.** At the place of the lot's own block (`P4.k7Core G`, Johnson/Desc/ProofFile/Lot/K6K7.lean)
it is `K7MemberKeeps` at the ground's own tail, vocabulary and last segment's number. At every other
place it is false. -/
def K7KeepsAt (G : Ground) (p : Place) (s s' : S) : Prop :=
  p = (P4.k7Core G).place ∧ K7MemberKeeps G.W.H.tl G.W.hS.V (G.built.size - 1) s s'

theorem K7KeepsAt.own (G : Ground) (s s' : S) :
    K7KeepsAt G (P4.k7Core G).place s s' ↔
      K7MemberKeeps G.W.H.tl G.W.hS.V (G.built.size - 1) s s' :=
  ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

theorem K7KeepsAt.elsewhere {G : Ground} {p : Place} (hp : p ≠ (P4.k7Core G).place) (s s' : S) :
    ¬ K7KeepsAt G p s s' := fun h => hp h.1

theorem K7KeepsAt.mark {G : Ground} {p : Place} {s s' : S} (h : K7KeepsAt G p s s') :
    s'.failed = none := h.2.mark

/-- From the whole sub-protocol's accepting step. -/
theorem k7KeepsAt_of_step {Z : Pub} {G : Ground} {b : Block S Cl} {a : Place} {x : Block S Unit}
    (hx : x ∈ h1Own G) (hj : IM.Joined Z (G.built.size - 1) b x.retype a)
    (hp : b.place = (P4.k7Core G).place) {ft : Nat} {s s' : S} (h : StepYes ft b s s') :
    K7KeepsAt G b.place s s' :=
  ⟨hp, k7MemberKeeps_of_step hx hj h⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.K7KeepsAt.own
#print axioms ProofFile.Honest.K7KeepsAt.elsewhere
#print axioms ProofFile.Honest.K7KeepsAt.mark
#print axioms ProofFile.Honest.k7KeepsAt_of_step
