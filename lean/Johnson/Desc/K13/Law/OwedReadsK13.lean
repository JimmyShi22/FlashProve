-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/OwedReadsK13.lean: A STATEMENT THAT IS OWED, WRITTEN AS A DEFINITION OF A Prop:
no proof stands here. With it two definitions.
IN PLAIN WORDS. Which components of the witness kind K13's layer's sentence reads at the two items
that it fills ("every pending row holds", `Item.pile`; "the one claim holds", `Item.pileOne`): the
index masks' tenant's message, that tenant's pad, and the cells: and no more: two witnesses that
agree on these three give the sentence one truth value, INSIDE THE PROMISE in front of block number
k and at a verifier's state without a mark (the form of `ReadsOkAtQ`,
Johnson/Desc/Sound/BordersSidesOn.lean).
  `readsK13 arr N`: the three components, at the two items; nothing at every other item.
  `BorderK13 M links ps k`: WHAT IS ASKED OF THE TABLE AT BORDER k: a fact on closed lists. EITHER
    the index masks' pin is open there and the four public items on which the reader leans (the
    proximity test's three; "K13.pileMasks") are open there; OR "nothing is sent yet"
    (`Pub.noneSent`) is open there and the border is not the chain's end: then no row is on the
    table, and the sentence holds of every witness.
  `OwedReadsK13`: the statement.
WHY INSIDE THE PROMISE. The sentence finds the index masks' message's seat through the book of trees
in the verifier's own state. Outside the promise that book may name any seat.
Words. "Block": a sub-protocol of the IOP as it is written in Lean. "The plan": the list of rounds
with each round's error bound, and the numbers made of it. "The verifier's state": what the verifier
carries from one sub-protocol to the next. "The promise": the condition on the public side at a
border between two sub-protocols.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.MgK13OfFills
import Johnson.Desc.K13.Law.PlanTestsM3
import Johnson.Desc.Sound.BordersSidesOn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice OnBytes.Maker
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers Comp)
open VerifiableInference.Desc.Sound (MsgT Sending Mem Frame onQ meansQ sameQ)

/-- **Which components of the witness the layer's sentence reads.** -/
def readsK13 (arr : ℕ → ℕ → ℕ) (N : Numbers) : Item → List Comp
  | .pile => [.msg (arr N.index.1 N.index.2), .pad N.index.1 N.index.2, .cells]
  | .pileOne => [.msg (arr N.index.1 N.index.2), .pad N.index.1 N.index.2, .cells]
  | _ => []

/-- **What is asked of the table at border k.** -/
def BorderK13 (M : First.More) (links : List ModelPart) (ps : List Place) (k : ℕ) : Prop :=
  (Item.pinI ∈ openAt links ps k ∧ ∀ q ∈ knownK13, q ∈ (First.pubSets M links ps)[k]?.getD []) ∨
    (Pub.noneSent ∈ (First.pubSets M links ps)[k]?.getD [] ∧
      ∃ p, ps[k]? = some p ∧ First.standAt links p ≠ .mem)

/-- **OWED.** Inside the promise, without a mark: the sentence reads the three components alone. -/
def OwedReadsK13 : Prop :=
  ∀ {A Pp Xi Cells Tok : Type} {nR : ℕ} {Fr : Frame} (P : Where) (N : Numbers)
    (Mg : Meaning Pp (Desc.Wit Cells Tok MsgT)) (cs : Codes) (sh : Params.ReqShape)
    (ly : Params.ReqLayout) (rest : Pp × S → Bool) (arr : ℕ → ℕ → ℕ)
    (mat : Cells → Fin nR → (Fin P.lin.kCol → Bool) → GE) (G : FileDescription Xi)
    (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells)
    (M : List OracleShape) (L : K12.Door.Laid) (links : List ModelPart) (ps : List Place)
    (get : A → Pp × S) (k : ℕ),
    FillsK13 P N Mg cs sh ly rest arr mat G smp ms decT M L → PlanM3 L M ms cs N →
    (∀ x, Mg.pub .noneSent x = noneSentC N x.2) → BorderK13 Mg.more links ps k →
    ∀ (i : Item) (a : A × Fr.E.Str) (w w' : Desc.Wit Cells Tok MsgT), i = .pile ∨ i = .pileOne →
      onQ N Mg links ps get k a → (get a.1).2.failed = none →
      (∀ c ∈ readsK13 arr N i, sameQ c w w') → meansQ N Mg get i a w → meansQ N Mg get i a w'

end VerifiableInference.Desc.K13.Law
