-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K6/Honest/Law/KeepsMember.lean: `K6Keeps` (Honest/Law/Keeps.lean) AT THE MEMBER AS THE
IOP AS WRITTEN IN LEAN SEATS IT: the two premises of that file's payers on the sub-protocol ("the
lot's seated block is there"; "B narrows it") paid from one sentence on the member (`K6MemberIs`,
Johnson/Desc/Kinds/Law/K6WayUp.lean). And: that member tells no oracle message. EVERY THEOREM IS
CONDITIONAL.

  `k6_keeps_of_member`, `k6_keeps_of_member_step`   a yes of the member's decision, of its step
  `member_tells_nothing`   the member states no oracle message in any round

What is called: `k6_keeps_member`, `k6_keeps_step`; that a sub-protocol which is laid alone has the
lot's sub-protocol's rounds and accepts only where that one does (`IM.alone_underR`,
Johnson/IMR/SeatForm.lean), which is `Block.Narrows` by unfolding (so says `underR_iff_narrows`,
Johnson/Desc/Sound/SeatNarrows.lean, which is not called here); `IM.alone_oracles` (same file);
`seatedClaims_some` (Johnson/Desc/Kinds/Law/SeatedBridge.lean).

Limits. `K6MemberIs` by itself is a form. That the first chain's flat list holds a sub-protocol of
that form at its place is another file's (`k6_member_at_mg`,
Johnson/Desc/Kinds/Law/K6WayUpAtSeat.lean), under the hypothesis that ties the letters to the IOP as
written in Lean: AT THE FULL SIZE ALONE (link 24, number 341): neither file speaks of a smaller
size. No module under lean/Johnson/Goal/ is among what this file imports; some are among what that
other file imports: whoever calls it takes them into its own. No pair of states is shown at which a
yes is said. Nothing on any property.

-/
import Johnson.Desc.K6.Honest.Law.Keeps
import Johnson.Desc.Kinds.Law.K6WayUp

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Honest
open VerifiableInference.Desc (Block Claim OpenedColumn Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.Head.Law (K6MemberIs)

variable {W : OnBytes.Model.Verify.Public} {l : Nat} {same : S → S → Bool} {a : Place}
  {b : Block S Claim}

/-- **A yes of the member's decision leaves what `K6Keeps` says.** CONDITIONAL: b has the form in
which the IOP as written in Lean seats the member (`K6MemberIs`); that the decision accepts. -/
theorem k6_keeps_of_member (M : K6MemberIs W l same a b) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hd : b.decide s rs gs = .ok s') : K6Keeps s s' := by
  obtain ⟨ms, bS, name, hS, hla⟩ := M
  exact k6_keeps_member hS (IM.alone_underR hla) hd

/-- **A yes of the member's step.** CONDITIONAL, as the last. -/
theorem k6_keeps_of_member_step (M : K6MemberIs W l same a b) {ft n : Nat} {s s' : S}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} (h : b.step ft s rs cols = .ok (s', n)) :
    K6Keeps s s' := by
  obtain ⟨ms, bS, name, hS, hla⟩ := M
  exact k6_keeps_step hS (IM.alone_underR hla) h

/-- **The member tells no oracle message.** CONDITIONAL: b has the form in which the IOP as written
in Lean seats the member. -/
theorem member_tells_nothing (M : K6MemberIs W l same a b) : b.oracles.flatMap id = [] := by
  obtain ⟨ms, bS, name, hS, hla⟩ := M
  rw [IM.alone_oracles hla]
  obtain ⟨b0, h0, rfl⟩ := Law.seatedClaims_some hS
  unfold blockClaims at h0
  obtain ⟨i, _, rfl⟩ := Option.map_eq_some_iff.mp h0
  show ((List.map (fun _ => ([] : List VerifiableInference.Desc.Oracle)) _).flatMap id) = []
  simp

end VerifiableInference.Desc.Kinds.Head.Honest

#print axioms VerifiableInference.Desc.Kinds.Head.Honest.k6_keeps_of_member
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.k6_keeps_of_member_step
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.member_tells_nothing
