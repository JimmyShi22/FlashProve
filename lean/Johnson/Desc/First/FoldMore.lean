-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/FoldMore.lean: two facts more that laws take from "REACHED", in a structure of
their own beside `FoldFacts`. One structure. Statements alone. No Mathlib of its own.

Why. `FoldFacts` (Johnson/Desc/First/FoldFacts.lean) is built whole by three groups of files; a
field more would change each of them. So these two facts stand apart, and a law names the one that
it spends.

What is said. `FoldMore Rch at_ nsAt ps`, at every statement a that Rch holds at border k and whose
state bears no mark:
  bookHas   the book has just one place for every oracle message of the statement
  slots     in front of a sub-protocol of segment m, where the state holds an open ledger G: its
            number of slots is nsAt m, and its list of slots has that length.
nsAt m: the number of slots of segment m's ledger, off the list of rounds.

Who makes, who spends. bookHas: it is the second clause of the promise's own `bookAt`; spent, at
reached states, by the closing's law on the carried rows and by the code switch's tie. slots: made
where a segment is opened; spent by the batching's ties.

Limits. Statements alone: nothing is proved here. Both facts were evaluated on an honest run.
Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open VerifiableInference.Desc

/-- **Two facts more that the laws take from "reached".** -/
structure FoldMore {X P : Type} (Rch : Nat → X → Prop) (at_ : X → P × S) (nsAt : Nat → Nat)
    (ps : List Place) : Prop where
  bookHas : ∀ k a, Rch k a → (at_ a).2.failed = none →
    (at_ a).2.book.place.size = (at_ a).2.st.oracles.size
  slots : ∀ k a p m G, Rch k a → (at_ a).2.failed = none → ps[k]? = some p → p.link = some m →
    (at_ a).2.fork? = some G → G.ns = nsAt m ∧ G.LS.size = G.ns

end VerifiableInference.Desc.First
