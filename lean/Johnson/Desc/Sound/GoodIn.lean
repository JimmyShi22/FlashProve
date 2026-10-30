-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/GoodIn.lean: what a block with a promise owes, so that a claim can be carried
past it. A SHEET OF STATEMENTS: one definition, and propositions written as `def … : Prop`. NOTHING
IS PROVED IN THIS FILE.

The setting. Johnson/Desc/Sound/ChainRule.lean asks of each block the library's `BK.Good`, whose
third part is `KnowInto`: knowledge soundness from the relation in front into the condition and the
relation behind. The condition behind a block is a PROMISE on which the later blocks' clauses rest
(after a proximity test: the tested word is close to the code). `KnowInto` counts a transcript that
leads outside the promise as the prover's win, to be paid in the errors, UNLESS the extractor's
value is a witness in front whatever is handed to it. So at a statement whose relation in front
holds anyway it bounds nothing: the prover may leave the promise for free.

That is harmless as long as the relation in front is all that is claimed. It is not where a further
claim is CARRIED PAST the block: a claim that the block neither reads nor tests, and that a later
block closes (what a file's first chain leaves open for the third, carried past the second). Take a
statement at which the block's own relation holds and the carried claim is false: leaving the
promise costs nothing there, behind the promise the later clauses say nothing, and the false claim
can be accepted. So `BK.Good` at R does not give `BK.Good` at "R and the carried claim" at the same
errors, even where the extractor keeps the carried claim at every transcript. The counter-model is
not typed here: the argument above is by reading.

What is said. `Piece.GoodIn`: at the block's errors the prover has lost towards ONE property of the
transcript that holds both: where the block says yes, THE STATEMENT BEHIND IS INSIDE THE PROMISE,
and a witness behind gives, by the block's extractor, a witness in front. `GoodOfGoodIn`: it gives
`BK.Good`. `GoodInOfCarry`: a block that keeps the promise at every transcript and is knowledge
sound has it. `GoodInOfBadFam`: so has a block with the three facts from which the library proves
"into" (`knowInto_of_badFam`, Ior/KnowColl.lean): as a named notion `GoodIn` is not in the library;
as the premises of that rule it is. `GoodInBeside`: it bears a carried claim: if the extractor keeps
the carried claim at outputs inside the promise, `GoodIn` at R gives `GoodIn` at "R and the carried
claim".

Limits. (1) `GoodIn` is a premise, owed for each block with a promise by whoever proves that block.
The library's rules that carry a claim beside a reduction (`know_beside`, Ior/KnowRules.lean; for a
batch `knowB_shared_beside`, Ior/KnowBRules.lean) ask that the condition is carried at every
transcript; the library has no such rule for `KnowInto` (the nearest, `knowInto_and`,
Cb/Pv/Switch/FoldSeam.lean, adds to the condition behind a property that every output has, and
carries nothing in front). (2) That the prover has lost towards two
properties, each at a list of errors, gives that it has lost towards both only at the sum of the
errors (`Doomed.and`, Iop/Compose.lean): so the promise stands inside the one property. (3) The
degenerate cases of ChainRule.lean, Limits (2), make these statements true and empty too: an error
that is the number of a round's challenges; a condition in front that holds of no statement; a block
that refuses all. (4) Nothing on acceptance.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.ChainRule

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed)

variable {S Cl W : Type} {C : CK} {F : Frame}

/-- **What a block with a promise owes.** `Doomed s ε lost` (Iop/Rbr.lean) says that the prover has
lost the game over the rounds s towards `lost`: whatever it sends in a round, at most the round's
entry of ε many values of the challenge lead to a position in which it has not lost; and at the end
`lost` holds of the transcript. Here: from every statement with `on`, at the block's errors, the
prover has lost towards: where the block says yes, the statement behind has `on'` (the promise is
kept), and every witness of it gives, by the block's extractor, a witness of the statement in front.
-/
def Piece.GoodIn (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (R R' : S × F.E.Str → W → Prop) : Prop :=
  ∀ a, on a → Doomed (uLT C p.ds) p.err fun τ =>
    ∀ b, p.ior.red.out a τ = some b → on' b ∧ ∀ w, R' b w → R a (p.ext a τ w)

/-- Every block of a row has it, between the conditions and relations at its two places (as
`EachGood`). -/
def EachGoodIn (on : ℕ → S × F.E.Str → Prop) (R : ℕ → S × F.E.Str → W → Prop) :
    ℕ → List (Piece C F S Cl W) → Prop
  | _, [] => True
  | i, p :: l => p.GoodIn (on i) (on (i + 1)) (R i) (R (i + 1)) ∧ EachGoodIn on R (i + 1) l

/-- It gives the premise that `EachGood` asks. -/
def GoodOfGoodIn : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (R R' : S × F.E.Str → W → Prop), p.GoodIn on on' R R' → (p.bk on on' R R').Good

/-- A block that keeps the promise at every transcript, and is knowledge sound between the two
relations, has it. -/
def GoodInOfCarry : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (R R' : S × F.E.Str → W → Prop),
    (∀ a τ b, on a → p.ior.red.out a τ = some b → on' b) →
    p.ior.red.Know on R R' p.ext p.err → p.GoodIn on on' R R'

/-- **From sets of bad challenges**: the three premises of the library's rule by which "into" is
proved (`knowInto_of_badFam`, Ior/KnowColl.lean): the bad sets are within the errors; on a
transcript without a bad challenge the statement behind is inside the promise; and on such a
transcript a witness behind gives one in front. So whoever has proved a block's `KnowInto` by that
rule has `GoodIn` from the same three facts. -/
def GoodInOfBadFam : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (R R' : S × F.E.Str → W → Prop) (bad : S × F.E.Str → Iop.BadFam (uLT C p.ds)),
    (∀ a, on a → (bad a).Within p.err) →
    (∀ a τ b, on a → (bad a).Clean τ → p.ior.red.out a τ = some b → on' b) →
    (∀ a τ b w, on a → (bad a).Clean τ → p.ior.red.out a τ = some b → R' b w →
      R a (p.ext a τ w)) →
    p.GoodIn on on' R R'

/-- **It bears a carried claim.** Rc: a claim that the block neither reads nor tests. The premise on
the extractor, asked at outputs inside the promise alone: where the block says yes, a witness of Rc
at the statement behind gives a witness of Rc at the statement in front. -/
def GoodInBeside : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (R R' Rc : S × F.E.Str → W → Prop),
    p.GoodIn on on' R R' →
    (∀ a τ b w, on a → p.ior.red.out a τ = some b → on' b → Rc b w → Rc a (p.ext a τ w)) →
    p.GoodIn on on' (fun a w => R a w ∧ Rc a w) (fun b w => R' b w ∧ Rc b w)


end VerifiableInference.Desc.Sound
