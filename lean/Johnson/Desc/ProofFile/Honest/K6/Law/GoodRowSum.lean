-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/GoodRowSum.lean: CONDITIONAL. NO NEW EQUATION BETWEEN TWO
DISTRIBUTIONS, NOT `plays`, NOT `acc`: THE NAMED PREMISE `SumLawAt` (Honest/K6/Law/GoodRow.lean) IS
PAID, by another folder's law, `exact_sumPart_field` (Honest/SumLaw/SumExact.lean): so `ExactMember`
(Honest/Small/Field.lean), which gives the field `exact` of `Good` (Honest/Side.lean) at every
`pre`, stands AT ALL EIGHT MEMBERS of the row of the sub-protocol "the output head's own rounds",
under the structure `HeadSeated` (Honest/K6/Law/Row.lean) alone, GENERAL IN THE PLACE's PUBLIC
NUMBERS p.

  `sumLawAt`   the premise, at every face, side, reader of the small input, chain, firstTree, On and
               bud: ONE TERM of that law, at the row's lens
  `head_exact_all`   `ExactMember` at all eight members: under the structure
  `head_good_all`   `Good` as one term, at every `pre`, at A := False (so `plays` and `acc` hold
                    there for nothing): under the structure and the Bool on the book
  `head_goodAt_all`, `head_goodAt_of_member_all`   the form that the frame's rule takes, at every
  `earlier`: at a list whose blocks at the place have the declared rounds and no oracle message; at
  a list of which every block at the place is b (hu), a block of the form in which a description
  seats K6's member (M): that b is in the list is no premise

A THIN FILE APART, because it imports Honest/SumLaw/SumExact.lean (the masked sumcheck's law on
`ExactMember`, by other authors).

Called. `exact_sumPart_field`: Honest/SumLaw/SumExact.lean: a law of another folder, by other
authors.

Limits. ALL THAT THAT LAW's HEAD SAYS RIDES ON, in its own words ("this folder" there is
Honest/SumLaw/): "the spender's half alone · the owners' sentences are typed by no file of this
folder, and none is called here · one part at a time, all else fixed before the coins · it holds at
every job, right or wrong, so it says nothing on whether the job is the protocol's · nothing on
hiding". The owners' sentences: the field `fresh` of `Good` at the parts that own the two stretches.
Its two lent stretches are TAKEN as uniform and independent. ALL THAT THE LIMITS OF
Honest/K6/Law/GoodRow.lean SAY HOLDS HERE: the carriers behind the row; at A := False `plays` and
`acc` are met for nothing; `goodAt` is met for nothing where no block stands at the place. "Members"
in this file: `σ.members`, the frame's `Member`; "K6's member": the library's `K6MemberIs`, a block.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.SumLaw.SumExact
import Johnson.Desc.ProofFile.Honest.K6.Law.RowAtMember

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (Block Place Claim)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head.Law (K6MemberIs workOf)
open ProofFile.Honest.Small ProofFile.Honest.SumLaw

variable {S Cl X W₀ Rc Tr : Type}

/-- **The named premise is paid**: one term of the masked sumcheck's law, at the row's lens. -/
theorem sumLawAt (φ : Face (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) Inst)
    (σ : Side S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst)
    (wit : Local W₀ Rc Inst Tr → HeadAsk) (chain firstTree : Nat)
    (On : (u : Member (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst) →
      CsAll u.part.carries → Mid (Local W₀ Rc Inst Tr) X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) :
    SumLawAt φ σ wit chain firstTree On bud :=
  fun j rs a' name endName J h1 h2 h3 =>
    exact_sumPart_field φ σ chain firstTree On bud (fun _ => ()) wit (fun _ => ()) (fun x _ => x)
      (fun _ _ => rfl) (fun _ => rfl) name endName J h1 rs h2 h3 j a'

/-- CONDITIONAL. **`ExactMember` at all eight members**: under the structure alone. It gives the
field `exact` of `Good` at every `pre` (`exactAt_of_exact`, Honest/Small/Field.lean). -/
theorem head_exact_all (φ : Face (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) Inst)
    {σ : Side S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst}
    {wit : Local W₀ Rc Inst Tr → HeadAsk} {p : Head.Par} {at_ : Place}
    (h : HeadSeated σ wit p at_) (chain firstTree : Nat)
    (On : (u : Member (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst) →
      CsAll u.part.carries → Mid (Local W₀ Rc Inst Tr) X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) :
    ∀ u ∈ σ.members, ExactMember φ σ chain firstTree On bud u :=
  head_exact φ h chain firstTree On bud (sumLawAt φ σ wit chain firstTree On bud)

/-- CONDITIONAL. **`Good` at the row's side, AS ONE TERM, at A := False**: `plays` and `acc` ARE MET
FOR NOTHING THERE. `pre` is a free letter: the term stands at every `pre`. -/
theorem head_good_all {pre : List (Nat × Nat × List Fmt.DeclaredRound)}
    (φ : Face (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) Inst)
    {σ : Side S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst}
    {wit : Local W₀ Rc Inst Tr → HeadAsk} {p : Head.Par} {at_ : Place}
    (h : HeadSeated σ wit p at_) (Bk : ProverCoinCounts) (ord : List Place) (chain firstTree : Nat)
    (B : Coins Bk → S → Mid (Local W₀ Rc Inst Tr) X → Env → Prop)
    (hB : ((List.range 8).all fun i => noneSpent Bk ⟨at_, i⟩) = true) :
    Good pre φ σ Bk ord chain firstTree (fun _ _ _ _ => False) B (fun _ _ _ _ => True) headBud :=
  head_good φ h Bk ord chain firstTree B (sumLawAt φ σ wit chain firstTree _ _) hB

/-- CONDITIONAL. **The form that the frame's rule takes**, at the chain's list and ITS FALLS. IN
FORM ALONE, and met for nothing where no block of bs stands at the place: see `head_goodAt`.
`earlier` is a free letter: the form stands at every value of it. -/
theorem head_goodAt_all {earlier : List (Nat × Nat × List Fmt.DeclaredRound)}
    (φ : Face (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) Inst) (Bk : ProverCoinCounts)
    (wit : Local W₀ Rc Inst Tr → HeadAsk) (p : Head.Par) (at_ : Place) (bs : List (Block S Cl))
    (ord : List Place) (chain firstTree : Nat) (fs : List (Fall S))
    (hb : ∀ b ∈ bs, b.place = at_ → b.rounds = p.rounds ∧ b.oracles = p.rounds.map fun _ => [])
    (hB : ((List.range 8).all fun i => noneSpent Bk ⟨at_, i⟩) = true) :
    (headLettered (S := S) (Cl := Cl) (X := X) Bk wit p at_).goodAt earlier φ bs ord chain firstTree
      fs :=
  head_goodAt φ Bk wit p at_ bs ord chain firstTree fs hb
    (fun σ => sumLawAt φ σ wit chain firstTree _ _) hB

/-- CONDITIONAL. The like at a list of which every block at the address is b (hu), a block of the
form in which a description seats K6's member (M). That b is in the list is no premise. `earlier` is
a free letter: the form stands at every value of it. -/
theorem head_goodAt_of_member_all {earlier : List (Nat × Nat × List Fmt.DeclaredRound)}
    {W : OnBytes.Model.Verify.Public} {l : Nat}
    {same : VerifiableInference.Desc.First.S → VerifiableInference.Desc.First.S → Bool}
    {a : Place} {b : Block VerifiableInference.Desc.First.S Claim}
    (φ : Face (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) Inst) (Bk : ProverCoinCounts)
    (wit : Local W₀ Rc Inst Tr → HeadAsk)
    (bs : List (Block VerifiableInference.Desc.First.S Claim)) (ord : List Place)
    (chain firstTree : Nat) (fs : List (Fall VerifiableInference.Desc.First.S))
    (M : K6MemberIs W l same a b) (hu : ∀ b' ∈ bs, b'.place = a → b' = b)
    (hB : ((List.range 8).all fun i => noneSpent Bk ⟨a, i⟩) = true) :
    (headLettered (S := VerifiableInference.Desc.First.S) (Cl := Claim) (X := X) Bk wit
      (Head.parOf W.hS (workOf W)) a).goodAt earlier φ bs ord chain firstTree fs :=
  head_goodAt_of_member φ Bk wit bs ord chain firstTree fs M hu
    (fun σ => sumLawAt φ σ wit chain firstTree _ _) hB

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.sumLawAt
#print axioms ProofFile.Honest.K6.head_exact_all
#print axioms ProofFile.Honest.K6.head_good_all
#print axioms ProofFile.Honest.K6.head_goodAt_all
#print axioms ProofFile.Honest.K6.head_goodAt_of_member_all
