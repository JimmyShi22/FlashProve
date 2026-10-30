-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/RowAtMember.lean: CONDITIONAL. NOT a law on a distribution of
its own, and NOT yet at a description: THE STRUCTURE `HeadSeated` (Honest/K6/Law/Row.lean) IS MET
WHERE THE SIDE's ROW IS THE HEAD's (a premise: hrow) AND ITS BLOCK HAS THE FORM IN WHICH A
DESCRIPTION SEATS K6's MEMBER (`K6MemberIs`, Johnson/Desc/Kinds/Law/K6WayUp.lean: the seated
constant, alone, under a name at an address, behind two guards): wrapping leaves the rounds and the
oracle messages, and lays the place.

  1  `headSeated_of_member`   ONE MORE DOOR TO THE STRUCTURE: the side's block is of that form, its
     row is the head's: by `member_is` (Honest/K6/Law/MemberIs.lean)
  2  `members_at_of_member`, `head_goodAt_of_member`   where no other member of the chain's list
     stands at the address: what `head_goodAt` (Honest/K6/Law/GoodRow.lean) asks of the list; so
     `Lettered.goodAt` there, at every `earlier`: STILL CONDITIONAL ON THE NAMED PREMISE `SumLawAt`
     AND ON THE BOOL ON THE BOOK

The public numbers are `Head.parOf W.hS (workOf W)`: the term of `headParAt` (Honest/K6/Part.lean)
at a ground whose public record is W: `workOf` (Johnson/Desc/Kinds/Law/RowRides.lean) unfolds to it.
"Member" in this file: a block of a chain's list, the library's sense (`K6MemberIs`): not the
frame's `Member`.

Called. `member_is`: Honest/K6/Law/MemberIs.lean. `K6MemberIs`: Johnson/Desc/Kinds/Law/K6WayUp.lean.

Limits. That a description's chain holds a member of that form: Honest/K6/Law/RowAtMg.lean (not in
the library), under that file's premise. THAT NO OTHER MEMBER STANDS AT THE ADDRESS IS A NAMED
PREMISE (hu): the description's own test on places is meant to give it; nothing here calls that
test. All that the Limits of Honest/K6/Law/GoodRow.lean say holds here. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K6.Law.MemberIs
import Johnson.Desc.ProofFile.Honest.K6.Law.GoodRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (Block Place Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head.Law (K6MemberIs workOf)
open ProofFile.Honest.Small

variable {X W₀ Rc Tr : Type} {W : OnBytes.Model.Verify.Public} {l : Nat} {same : S → S → Bool}
  {a : Place} {b : Block S Claim}

/-! ## 1 One more door to the structure -/

/-- CONDITIONAL. The structure, where the side's block is of that form and its row is the head's. -/
theorem headSeated_of_member {σ : Side S Claim (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst}
    {wit : Local W₀ Rc Inst Tr → HeadAsk} (M : K6MemberIs W l same a σ.block)
    (hrow : σ.row = headSided wit (Head.parOf W.hS (workOf W)) a) :
    HeadSeated σ wit (Head.parOf W.hS (workOf W)) a :=
  ⟨hrow, (member_is M).1, (member_is M).2.1, (member_is M).2.2⟩

/-! ## 2 At a chain's list -/

/-- CONDITIONAL. What `head_goodAt` asks of the list, where no other member stands at the address.
-/
theorem members_at_of_member {bs : List (Block S Claim)} (M : K6MemberIs W l same a b)
    (hu : ∀ b' ∈ bs, b'.place = a → b' = b) :
    ∀ b' ∈ bs, b'.place = a → b'.rounds = (Head.parOf W.hS (workOf W)).rounds ∧
      b'.oracles = (Head.parOf W.hS (workOf W)).rounds.map fun _ => [] := by
  intro b' hb' hp
  rw [hu b' hb' hp]
  exact (member_is M).2

/-- CONDITIONAL ON THE NAMED PREMISE `SumLawAt`, and on M, hu and the Bool hB. **The form that the
frame's rule takes** (`Lettered.goodAt`; in form alone: see `head_goodAt`), at a list of which every
member at the address is b. That b is in the list is no premise: where it is not, nobody stands at
the address, and the sentence is met for nothing. `earlier` is a free letter: the form stands at
every value of it. -/
theorem head_goodAt_of_member {earlier : List (Nat × Nat × List Fmt.DeclaredRound)}
    (φ : Face (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) Inst)
    (Bk : ProverCoinCounts)
    (wit : Local W₀ Rc Inst Tr → HeadAsk) (bs : List (Block S Claim)) (ord : List Place)
    (chain firstTree : Nat) (fs : List (Fall S)) (M : K6MemberIs W l same a b)
    (hu : ∀ b' ∈ bs, b'.place = a → b' = b)
    (hSum : ∀ σ : Side S Claim (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst,
      SumLawAt φ σ wit chain firstTree (fun _ _ _ _ => True) headBud)
    (hB : ((List.range 8).all fun i => noneSpent Bk ⟨a, i⟩) = true) :
    (headLettered (S := S) (Cl := Claim) (X := X) Bk wit (Head.parOf W.hS (workOf W)) a).goodAt
      earlier φ bs ord chain firstTree fs :=
  head_goodAt φ Bk wit _ a bs ord chain firstTree fs (members_at_of_member M hu) hSum hB

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.headSeated_of_member
#print axioms ProofFile.Honest.K6.members_at_of_member
#print axioms ProofFile.Honest.K6.head_goodAt_of_member
