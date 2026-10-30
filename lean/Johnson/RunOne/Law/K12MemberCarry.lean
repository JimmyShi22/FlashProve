-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12MemberCarry.lean: FROM A FACT ON THE RECORD's OWN MESSAGE TO THE MEMBER OF THE PLAIN DATA THAT THE RECORD FIXES. Two statements with proofs; each is calls of two other files' lemmas. GENERAL IN THE PLACE AND THE CHAIN: no key file stands in them.
OBJECT. `Fixes` (Johnson/Desc/K12/Coin/Sheet.lean): what a record t in front of a proximity test fixes: the group G0, the plain data D with its members D.mems.
USER. Whoever pays the composition's clauses on one member (MemberFacts, Johnson/Desc/Sound/SeamMembers.lean: they speak at D.st and at (D.mems.get j).id | .sh) from facts at the record's own statement and a message's number.
  one_member: where the group's members are just [n]: the plain data have one member, and its number is n. By mems_ids (Johnson/Desc/K12/Coin/MembersLaid.lean).
  member_carry: in the first arm (the record names a mask): at the member j whose number is o, and the record's message x at o: the member's shape is x's; the plain data's message is there, with x's sample rows. By member_below_first | member_at (Johnson/Desc/K12/Coin/MemberShape.lean).
WHY NO SEED, ROW OR ANSWER IS NAMED: the clause that this feeds binds them in ONE "there is" with the reading's half: so they must ride outside: the caller opens its own "there is" once and closes the clause's once, with the same letters.
Limits. The first arm alone. Nothing on soundness, nothing on hiding.

-/
import Johnson.Desc.K12.Coin.MemberShape
import Johnson.Desc.K12.Coin.MembersLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.K12MemberCarry
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.K12.Coin
open H2K.First (Plain)

variable {π : P12} {t : T12} {a : Fmt.M1.Stage} {rest : List Fmt.M1.Stage} {G0 : Group}
  {Ly : GroupLayout} {D : Plain}

/-- **A group of one has one member in the plain data.** -/
theorem one_member (hf : Fixes π t a rest G0 Ly D) (n : ℕ) (hG : G0.members.toList = [n]) :
    D.mems.length = 1 ∧ ∀ j : Fin D.mems.length, (D.mems.get j).id = n := by
  obtain ⟨h1, h2⟩ := mems_ids π t a rest G0 Ly D hf
  have hs : G0.members.size = 1 := by
    have e := congrArg List.length hG
    simpa using e
  refine ⟨h1.trans hs, fun j => ?_⟩
  have hj : j.val = 0 := by
    have := j.isLt
    omega
  have h3 := h2 j
  rw [hj] at h3
  have h4 : G0.members[0]? = some n := by
    rw [← Array.getElem?_toList, hG]
    rfl
  exact Option.some.inj (h3.symm.trans h4)

/-- **The member's shape and sample rows are those of the record's own message.** -/
theorem member_carry (hf : Fixes π t a rest G0 Ly D) (hmk : t.mask.isSome = true)
    (j : Fin D.mems.length) (o : ℕ) (hid : (D.mems.get j).id = o) (x : OnBytes.Oracle)
    (h1 : t.st.oracles[o]? = some x) :
    (D.mems.get j).sh = x.shape ∧
      ∃ x', D.st.oracles[(D.mems.get j).id]? = some x' ∧ x'.sampleRows = x.sampleRows := by
  obtain ⟨x0, x', e1, e2, e3, _, _, e6⟩ := member_at hf j (member_below_first hf hmk j)
  rw [hid, h1] at e1
  obtain rfl : x = x0 := Option.some.inj e1
  exact ⟨e3, x', e2, e6⟩

end Johnson.RunOne.Law.K12MemberCarry

#print axioms Johnson.RunOne.Law.K12MemberCarry.one_member
#print axioms Johnson.RunOne.Law.K12MemberCarry.member_carry
