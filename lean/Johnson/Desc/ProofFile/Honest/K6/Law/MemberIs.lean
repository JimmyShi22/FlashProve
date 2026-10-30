-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/MemberIs.lean: CONDITIONAL. NOT a law on a distribution, NOT on
a decision, and NOT yet at a description: what a block has THAT HAS THE FORM IN WHICH A DESCRIPTION
SEATS K6's MEMBER (`K6MemberIs`, Johnson/Desc/Kinds/Law/K6WayUp.lean: the seated constant, alone,
under a name at an address, behind two guards): wrapping leaves the rounds and the oracle messages,
and lays the place.

  `headSeated_oracles`   the seated constant has one empty list of oracle messages a round
  `member_is`   a member of that form stands at the address, has the rounds that the verifier's text
                declares at the public data's numbers, and no oracle message

A THIN FILE APART: it imports that one file of the verifier's side and nothing of the honest side,
so that whoever wants these two sentences alone takes in no more.

The public numbers are `Head.parOf W.hS (workOf W)`: the term of `headParAt` (Honest/K6/Part.lean).

Called. `K6MemberIs`, `K6MemberIs.rounds`: Johnson/Desc/Kinds/Law/K6WayUp.lean. TYPED ANEW, AND WHY:
`headSeated_oracles`: the tree has "the member tells no oracle message" as `oracles.flatMap id = []`
(Johnson/Desc/K6/Honest/Law/KeepsMember.lean: `member_tells_nothing`), which does not say how many
empty lists there are; a caller wants one for each round.

Limits. That a description's chain holds a member of that form is shown elsewhere, under premises
(Honest/K6/Law/RowAtMg.lean). Nothing on any property.

-/
import Johnson.Desc.Kinds.Law.K6WayUp

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (Block Place Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head.Law (K6MemberIs workOf)

variable {W : OnBytes.Model.Verify.Public} {l : Nat} {same : S → S → Bool} {a : Place}
  {b : Block S Claim}

/-- CONDITIONAL. The seated constant has one empty list of oracle messages for each round. By
unfolding. -/
theorem headSeated_oracles {ms : List (Nat × Nat)} {bS : Block S Claim}
    (h : Head.seatedClaims W l ms = some bS) :
    bS.oracles = (Head.parOf W.hS (workOf W)).rounds.map fun _ => [] := by
  unfold Head.seatedClaims Head.blockClaims at h
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨iU3, -, rfl⟩ := Option.map_eq_some_iff.1 hc
  rfl

/-- CONDITIONAL. **A member of the form in which a description seats it** stands at the address, has
the declared rounds, and no oracle message. -/
theorem member_is (M : K6MemberIs W l same a b) :
    b.place = a ∧ b.rounds = (Head.parOf W.hS (workOf W)).rounds ∧
      b.oracles = (Head.parOf W.hS (workOf W)).rounds.map fun _ => [] := by
  have hr : b.rounds = (Head.parOf W.hS (workOf W)).rounds := M.rounds
  obtain ⟨ms, bS, name, hS, hla⟩ := M
  exact ⟨IM.alone_place hla, hr, (IM.alone_oracles hla).trans (headSeated_oracles hS)⟩

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.headSeated_oracles
#print axioms ProofFile.Honest.K6.member_is
