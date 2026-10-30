-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/ExactFresh/Forms.lean: FORMS OF PREMISES. The forms under which
`ExactMember` and `FreshMember` (Honest/Small/Field.lean) are stated at the parts of the row of the
layers' own rounds (kind K4). Definitions; two small statements on `fresh`, with their proofs.

`FreshMember` is the text of the field `fresh` of `Good` (Honest/Side.lean) at one member.
`ExactMember` is the text of the field `exact` WITHOUT ITS HYPOTHESIS ON THE OPENED COLUMNS; it
gives that field's text at the member, at every `pre` (`exactAt_of_exact`, Honest/Small/Field.lean).
What declared rounds state is the sentence `StatedBy` (Honest/SumLaw/Fits.lean).

  `MSForm marked`  the premise's form.
  `k4RowEnds Q`, `k4TermEnds Q`   TWO TESTS ON THE PLAN's PUBLIC NUMBERS: the token sumcheck on the
      row products, and the second token sumcheck, have at least one end value. `shapeOk`
      (Johnson/Desc/Part/MaskedSum4.lean) asks it of a call. Who shows them: whoever lays the plan.
  `k4Lift`         the one way in which every part of the row is seated.
  `k4_fresh_once`, `k4_fresh`   `FreshMember` at a member that no entry by which a part spends names
      as owner; at a member that no entry of the book names as owner.

Limits. `MSForm marked` IS A PREMISE's FORM, NOT A THEOREM: the equation of two laws at the frame's
masked sumcheck's part beside its simulator, at every job. IT IS AT EVERY On, AND `ExactMember`
BINDS THE STATE m BY "∀": so the form asks its equation at every value of `m.opened` too. It is
shown in Law/ExactFresh/Paid.lean, at `betaMarked`, by one call of `exact_sumPart_field`
(Honest/SumLaw/SumExact.lean). The test `marked` on the declared rounds is its parameter.
`betaMarked` (Honest/SumLaw/BetaMarked.lean) is the test that is meant there: that of the masked
sumcheck's own law. AT marked := fun _ _ => false THE FORM IS MET FOR NOTHING, and at fun _ _ =>
true it is not meant to hold: THE FORM THAT COUNTS IS `MSForm betaMarked`. At a call without end
values `MSForm betaMarked` holds the law with no test on a mark. THE TWO STATEMENTS ON `fresh` ARE
IDENTITIES: where nothing of the member's is spent by a part, the field's two laws are one law. They
name no coin and say nothing of K4, nor of the runs that K4's parts spend: `fresh` AT THE OWNERS OF
THESE RUNS is owed by whoever writes the owners' parts, and is typed nowhere here. The tests
`lendsNone` and `noneSpent` follow from no clause of the book's own tests;
Law/ExactFresh/JoinTest.lean (no part of the library yet) evaluates the first at a small synthetic
book alone.

Kin. `MSForm marked` has the text of `exact_sumPart_field` (Honest/SumLaw/SumExact.lean, of other
writers) with `marked` in the stead of `betaMarked` and the binders in another order.
Honest/K5/Law/GoodForms.lean, of other writers, has a definition of the same short name,
`K5.MSForm`: a form of the like premise: bud is its parameter, On is True, a fixed premise
`DrawnLike` on the rounds stands where `marked` stands here, the lens is onto Unit, the simulator's
address is the member's own, and it ends in that folder's `ExactU`. The identity of `k4_fresh_once`
stands, among others: at every member of a side at once, under the same test, as `fresh_at`
(Honest/K14/GoodCalls.lean); at every side and member, as here, under the sentence `OwnsNothing` (no
entry of the book names the part as owner: what `lendsNone` tests) and ending in that folder's
`FreshU`, as `fresh_u` (Honest/K5/Law/GoodForms.lean): the nearest kin of `k4_fresh`; at other
types as `member_fresh` (Honest/Small/ToyScalars.lean); at the masked sumcheck's member, from the
empty lists of entries themselves, as `fresh_sumPart_field` (Honest/SumLaw/SumExact.lean); at the
output head's row as `head_fresh` (Honest/K6/Law/GoodRow.lean). None of these
five files lies beneath this one, and none of these statements is called. Sought: by statement, to
the letter and up to the bound letters, and by short name, among the theorems of the library as it
lay with the writer: no hit; by short name among the definitions under Honest/: the one told. The
search by statement does not see a statement that has a binder in front of the colon where ours has
it behind, or the other way round. The kin on `fresh` were found by the names `FreshMember` and
`noneSpent`, `fresh_u` by the name `fresh_of_nil`. Not sought: twins of the four definitions in
other letters.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Part
import Johnson.Desc.ProofFile.Honest.Small.Book
import Johnson.Desc.ProofFile.Honest.Small.StatedBy
import Johnson.Desc.ProofFile.Honest.SumLaw.BetaMarked

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes.Model (ledNO)
open OnBytes.Model.Layer (nEndT)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Place Oracle)
open VerifiableInference.Desc.Part.MaskedSum (Call shapeOk)
open ProofFile.Honest.Small (ExactMember FreshMember lendsNone noneSpent spentBy_of_noneSpent
  noneSpent_of_lendsNone)
open ProofFile.Honest.SumLaw (StatedBy)

/-- **The masked sumcheck's part beside its simulator: the form of a premise.** `ExactMember` (the
text of `Good.exact` without its hypothesis on the opened columns) at a member written out: at every
side, face, On, bud, job, pair of names, number of the member, list of its rounds and address of the
simulator; at every see and wit; at every get and set with get (set x y) = y and set x (get x) = x;
under three premises on public data: `shapeOk` at the job's shape, `StatedBy` at the shape's numbers
of scalars, and marked, a test on the shape and the declared rounds. Shown at `betaMarked` in
Law/ExactFresh/Paid.lean. -/
def MSForm (marked : Call → List (Fmt.DeclaredRound × List Oracle) → Bool) : Prop :=
  ∀ (S Cl V W X Pb V' W' Y : Type) (φ : Face V W Pb) (σ : Side S Cl V W X Pb)
    (chain firstTree : Nat)
    (On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop)
    (see : V → V') (wit : W → W') (get : X → Y) (set : X → Y → X),
    (∀ x y, get (set x y) = y) → (∀ x, set x (get x) = x) →
    ∀ (name endName : String) (J : SumJob W' Y) (j : Nat)
      (rs : List (Fmt.DeclaredRound × List Oracle)) (a : Addr),
      shapeOk J.shape = true → StatedBy (scalarsOf J.shape) rs → marked J.shape rs = true →
      ExactMember φ σ chain firstTree On bud
        ⟨j, rs, (sumPart (V := V') name endName J).lift see wit get set, sumSim a J.shape⟩

/-- **Whether the token sumcheck on the row products has an end value**: a test on the plan's
numbers, true or false: the form of a premise (of `k4_exact_8_6`, Law/ExactFresh/AtParts.lean).
Nothing here shows it at a plan. -/
def k4RowEnds (Q : K4Pub) : Bool := decide (1 ≤ ledNO Q.P.y.h.xl * Q.P.y.NI)

/-- **Whether the second token sumcheck has an end value**: a test on the plan's numbers, true or
false: the form of a premise (of `k4_exact_9_7`, Law/ExactFresh/AtParts.lean). Nothing here shows
it at a plan. -/
def k4TermEnds (Q : K4Pub) : Bool := decide (1 ≤ nEndT Q.P.y)

variable {W₀ Rc Xi Tr X : Type}

/-- **How every part of the row is seated** (`k4Row`, Honest/K4/Part.lean). A way of writing a
member, no premise: the example below holds it against `k4Row`. -/
def k4Lift (Q : K4Pub) (cells : Tr → Cells) (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : List Fmt.Drawn → OnBytes.Model.Forest.Heard) (p : Part Unit K4In Unit) :
    Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  p.lift (fun _ => ()) (k4Wit Q cells weights tokens look) (fun _ => ()) fun x _ => x

/-- The row is made so. -/
example (Q : K4Pub) (cells : Tr → Cells) (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : List Fmt.Drawn → OnBytes.Model.Forest.Heard) :
    (k4Row Q cells weights tokens look : List (Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)) =
      (k4RowIn Q).map (k4Lift Q cells weights tokens look) := rfl

section
variable {S Cl V W Y Pb : Type} (φ : Face V W Pb) (σ : Side S Cl V W Y Pb) (Bk : ProverCoinCounts)
  (ord : List Place) (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop)
  (u : Member V W Y Pb)

/-- **`FreshMember` at a member that no entry by which a part spends names as owner.** AN IDENTITY:
where nothing of the member's is spent by another part the field's two laws are one law. It says
nothing of the runs that K4's parts spend. At every side and member. CONDITIONAL on that test on the
book. -/
theorem k4_fresh_once (h : noneSpent Bk ⟨σ.block.place, u.number⟩ = true) :
    FreshMember φ σ Bk ord bud u :=
  fun p _ _ _ _ _ _ _ _ => fresh_of_nil _ (spentBy_of_noneSpent h p) _ _

/-- **The same at a member that no entry of the book names as owner.** AN IDENTITY, as the first.
CONDITIONAL on that test on the book, which asks more. -/
theorem k4_fresh (h : lendsNone Bk ⟨σ.block.place, u.number⟩ = true) :
    FreshMember φ σ Bk ord bud u :=
  k4_fresh_once φ σ Bk ord bud u (noneSpent_of_lendsNone h)

end

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.MSForm
#print axioms ProofFile.Honest.K4.k4RowEnds
#print axioms ProofFile.Honest.K4.k4TermEnds
#print axioms ProofFile.Honest.K4.k4Lift
#print axioms ProofFile.Honest.K4.k4_fresh_once
#print axioms ProofFile.Honest.K4.k4_fresh
