-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/OwedFoldFacts.lean: K13's FILES' FACTS ALONG THE FOLD, EACH WRITTEN AS A
DEFINITION OF A Prop: no proof stands here. THIN: over the layer's tests as code
(Johnson/Desc/K13/PubK13.lean) and `inOrderK13` (Johnson/Desc/K13/Law/FillK13.lean) alone. Why. Four
sentences of ours only carry a fact on the chain's state past many sub-protocols: the public items
"K13.pileMasks", "K13.pileWithin", "K13.oneRow" and our conjunct of "in order". They
leave the table's door; each becomes a field of one Lean structure of facts
along the fold, of the form: at every border k and every statement a that is reached there, THE
TEST's OWN TEXT accepts a's state. "Reached" is a letter here (a family Rch of sentences on a
border's number and a statement): `RchAt F` (Johnson/Top/H0/Walk/ReachAt.lean) is
the family that is meant.
  `RchRows Rch`: every row on the table names mask entries of the index masks' message alone; every
  such entry lies within its table, and every ledger is that of so many takes since it was made;
  where the chain stands at its end, one row lies on the table, with a mask entry. ONE Prop FOR THE
  THREE: the second is earned from the ledgers' clause, the third beside the first.
  `RchOrder cs sh ly Rch`: the statement is tidy, and its code table, the frame's shape and the
  rows' layout are the given ones.
THE ROAD THAT IS MEANT, FOR EACH: (1) the fact holds at the chain's first state; (2) every
sub-protocol of the first chain's flat list keeps it (`Keeps.Decides (Keeps.ofInv ‹the fact›)`,
Johnson/Desc/FoldKeeps.lean): ONE induction over "who writes the fields that it reads"; (3) an
induction on "reached" itself. THE CAUTION THAT BINDS EVERY SPENDER: "reached" says "there are
rounds and columns": these conclusions read the state alone; nothing may be drawn from the witnesses
of "some".
What is not claimed. That either holds. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.FillK13

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Slice
open VerifiableInference.Desc.First (S)

/-- The three tests on the rows on the table, as one fact on the chain's state. -/
def RowsFact (s : S) : Prop :=
  pileMasksC s = true ∧ pileWithinC s = true ∧ oneRowC s = true

/-- **OWED.** At every reached statement the three tests accept. -/
def RchRows {Pp Str : Type} (Rch : ℕ → (Pp × S) × Str → Prop) : Prop :=
  ∀ k a, Rch k a → RowsFact a.1.2

/-- **OWED.** At every reached statement our conjunct of "in order" accepts. -/
def RchOrder {Pp Str : Type} (cs : Codes) (sh : Params.ReqShape) (ly : Params.ReqLayout)
    (Rch : ℕ → (Pp × S) × Str → Prop) : Prop :=
  ∀ k a, Rch k a → inOrderK13 cs sh ly a.1.2 = true

end VerifiableInference.Desc.K13.Law
