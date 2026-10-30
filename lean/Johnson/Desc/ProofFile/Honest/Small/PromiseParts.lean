-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Small/PromiseParts.lean: THE PROMISE OF THE FIRST CHAIN's
TABLE AT A BORDER (`onAt`, Johnson/Desc/First/Borders.lean), AT A STATE WITHOUT A MARK, CLAUSE BY
CLAUSE, WHERE THE MEANING IS ONE OF THE HONEST SIDE: from the promise at such a meaning M to the
clauses at the meaning M0 whose public fields it bears; and back. Two structures, two statements
with their proofs.

What it is not. Nothing says that a promise holds at any state, or that any meaning is like another:
both statements are CONDITIONAL. They are unfoldings of the table's own text. No letter of any
sub-protocol, border or size stands in the file: it is general in both meanings, the numbers, the
segments' sorts, the places and the border, and it stands over the library alone. Nothing is claimed
on soundness, completeness or hiding.

  `HonestLike M0 M`   pub, pubP, held, inOrder and more of M are M0's; decodes, shown and noColl of
                      M hold outright
  `PartsAt N M0 links ps k a`   the eight clauses of the promise that read the verifier's state
                      alone: shape, rows, members, order, pub, book, samples, pubP
  `partsAt_of_onAt`   CONDITIONAL on `HonestLike M0 M` and "no mark": the promise at M gives them
  `onAt_of_partsAt`   CONDITIONAL on `HonestLike M0 M`: they give the promise at M, at any strings

Why. The library's lemmas that take a clause out of the promise (Johnson/Desc/Sound/OnParts.lean:
`OnParts`, `onParts_of_on`) and those that stand on them are stated at one meaning, in a frame, with
the oracles' strings; the promise's first clause there is "the stored table decodes". On the honest
side the promise stands at a meaning in which the three clauses on strings are true by make, so
that it does not give the library's promise at M0; it does give every clause that reads the state.

What is typed anew, and why. `PartsAt` is `OnParts` without its clause on strings, at no frame; the
first proof is `onParts_of_on`'s unfolding, which cannot be called here: it wants a frame and a
member of its strings.

All names stand in the namespace ProofFile.Honest.Small: a caller opens it.

-/
import Johnson.Desc.Sound.OnParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Small
open VerifiableInference.Desc (Place Strs)
open VerifiableInference.Desc.First (S ModelPart Item Numbers Meaning onAt shapeAt rowsHeld membersHeld
  bookAt sampledIn pubOfItems pubHeld samplesHeld)
open VerifiableInference.Desc.Sound (openQ pubQ)

variable {P W : Type}

/-- **A meaning that is like M0 on the honest side**: the five fields that a promise reads of the
verifier's state alone are M0's; the three that it reads of the oracles' strings hold outright. -/
structure HonestLike (M0 M : Meaning P W) : Prop where
  pub : M.pub = M0.pub
  pubP : M.pubP = M0.pubP
  held : M.held = M0.held
  inOrder : M.inOrder = M0.inOrder
  more : M.more = M0.more
  decodes : ∀ a y, M.decodes a y
  shown : ∀ j t y, M.shown j t y
  noColl : ∀ j t a y, M.noColl j t a y

/-- **The promise at border k, at a state without a mark, clause by clause**, but for the clauses
on the oracles' strings: at no frame and no strings. -/
structure PartsAt (N : Numbers) (M0 : Meaning P W) (links : List ModelPart) (ps : List Place) (k : Nat)
    (a : P × S) : Prop where
  shape : shapeAt links ps[k]? a.2 = true
  rows : rowsHeld N (openQ links ps k) a.2 = true
  members : membersHeld N (openQ links ps k) a.2 = true
  order : M0.inOrder a = true
  pub : ∀ q ∈ pubQ M0.more links ps k ++ pubOfItems (openQ links ps k), M0.pub q a = true
  book : bookAt N ps[k]? a.2 = true
  samples : ∀ x ∈ sampledIn N (openQ links ps k), M0.held x.1 x.2 a = true
  pubP : ∀ q ∈ pubQ M0.more links ps k, M0.pubP q a

/-- **From the promise at a meaning that is like M0, at a state without a mark, to M0's clauses.**
-/
theorem partsAt_of_onAt {N : Numbers} {M0 M : Meaning P W} (E : HonestLike M0 M) (links : List ModelPart)
    (ps : List Place) (k : Nat) (a : P × S) (y : Strs)
    (h : onAt N M links ps[k]? (openQ links ps k) (pubQ M.more links ps k) a y)
    (hm : a.2.failed = none) : PartsAt N M0 links ps k a := by
  unfold onAt at h
  obtain ⟨_, h2⟩ := h
  rcases h2 with h2 | ⟨hb, hs, _, hpp⟩
  · exact absurd hm h2
  · simp only [Bool.and_eq_true] at hb
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hb
    unfold pubHeld at h5
    unfold samplesHeld at hs
    rw [E.more, E.pub] at h5
    rw [E.inOrder] at h4
    rw [E.held] at hs
    rw [E.more, E.pubP] at hpp
    exact ⟨h1, h2, h3, h4, fun q hq => List.all_eq_true.1 h5 q hq, h6,
      fun x hx => List.all_eq_true.1 hs x hx, hpp⟩

/-- **And back**, at any strings. -/
theorem onAt_of_partsAt {N : Numbers} {M0 M : Meaning P W} (E : HonestLike M0 M) (links : List ModelPart)
    (ps : List Place) (k : Nat) (a : P × S) (y : Strs) (h : PartsAt N M0 links ps k a) :
    onAt N M links ps[k]? (openQ links ps k) (pubQ M.more links ps k) a y := by
  unfold onAt
  refine ⟨E.decodes a y, Or.inr ⟨?_, ?_, fun x _ => ⟨E.shown _ _ _, E.noColl _ _ _ _⟩, ?_⟩⟩
  · simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨h.shape, h.rows⟩, h.members⟩, ?_⟩, ?_⟩, h.book⟩
    · rw [E.inOrder]
      exact h.order
    · unfold pubHeld
      rw [E.more, E.pub]
      exact List.all_eq_true.2 h.pub
  · unfold samplesHeld
    rw [E.held]
    exact List.all_eq_true.2 h.samples
  · rw [E.more, E.pubP]
    exact h.pubP

end ProofFile.Honest.Small

#print axioms ProofFile.Honest.Small.partsAt_of_onAt
#print axioms ProofFile.Honest.Small.onAt_of_partsAt
