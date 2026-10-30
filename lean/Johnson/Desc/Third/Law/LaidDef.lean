-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/Law/LaidDef.lean: what K14's second part of the last chain has laid, as one
structure of plain facts on the record in front (s) and the record behind (s'). A structure of Prop.
No theorem.

Why. A table of this chain's joints wants these facts and nothing else of the block. They are stated
here without any of the laws' own definitions, over the chain's record and the library's
`Means.RowIn` alone, so that a file which spends them need not import the laws. That the block's yes
gives them: Johnson/Desc/Third/Law/Laid.lean.

The fields are the clauses of `Says` (Johnson/Desc/Third/Law/Says.lean), with "(Dot) is a plain row"
in the place of "is no sample row", of `Sharp` (Law/Sharp.lean), and, of `BookSays` (Law/Book.lean),
"statement and book are in step" and the frame on the older places; and `dotIn`: (Dot) has passed
the plain ground's tests on a new open row, in the library's form `OnBytes.Means.RowIn`
(Law/DotIn.lean).

And `order`: `Means.InOrder` is kept (Law/Order.lean). Of the book besides: `places` (one
place more), `oldTrees` (every older tree as it was) and `tree` (Omega's tree in the border's copy
of the shared book has one part, Law/Alone.lean; the new tree behind has its number and source).

Limits. Those of the six. Nothing on what a row, a place or a tree means. Nothing on soundness or
on hiding.
-/
import Johnson.Desc.Third.State
import Johnson.Desc.Means.Order

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes

namespace VerifiableInference.Desc.Third

/-- **What K14's second part has laid.** S: the plan's shape of the test on the table. b: the border
that lay in front. y: Omega in the border's copy of the shared statement. G: the own group in front.
dot: the row (Dot). -/
structure Laid (S : Params.LinShape) (s s' : S₃) (b : Border) (y : OnBytes.Oracle)
    (G : OnBytes.Group) (dot : OnBytes.Row) : Prop where
  border : s.loc.border = some b
  loc : s'.loc = { s.loc with border := none, omega := s.st.oracles.size }
  there : b.shared.st.oracles[b.shared.omega]? = some y
  sampled : y.sampled = true
  size : s'.st.oracles.size = s.st.oracles.size + 1
  copy : s'.st.oracles[s.st.oracles.size]? = some
    { shape := y.shape, sampled := true
      sampleRows := y.sampleRows.map (·.renamed s.st.oracles.size), pad := y.pad
      groups := [s.loc.own] }
  group : s.st.groups[s.loc.own]? = some G
  notBegun : G.inRun = false
  dotIs : linDotRow S b.g b.shared.psi s.st.oracles.size (linLayOmega s.st.codes S) s.loc.w
    (linLayW s.st.codes S) = some dot
  plain : dot.kind = .plain
  group' : s'.st.groups[s.loc.own]? = some { G with
    members := G.members.insertIdxIfInBounds (G.members.filter (· < s.st.oracles.size)).size
      s.st.oracles.size
    kept := G.kept.insertIdxIfInBounds (G.members.filter (· < s.st.oracles.size)).size false
    rows := G.rows.push dot }
  dotIn : Means.RowIn s'.st { G with
    members := G.members.insertIdxIfInBounds (G.members.filter (· < s.st.oracles.size)).size
      s.st.oracles.size
    kept := G.kept.insertIdxIfInBounds (G.members.filter (· < s.st.oracles.size)).size false
    rows := G.rows.push dot } dot
  codes : s'.st.codes = s.st.codes
  old : ∀ i : Nat, i < s.st.oracles.size → s'.st.oracles[i]? = s.st.oracles[i]?
  oldGroups : ∀ i : Nat, i ≠ s.loc.own → s'.st.groups[i]? = s.st.groups[i]?
  groups : s'.st.groups.size = s.st.groups.size
  roots : s'.roots = s.roots
  trees : s'.book.trees.size = s.book.trees.size + 1
  step : s.st.oracles.size = s.book.place.size
  place : s'.book.place[s.st.oracles.size]? = some (s.book.trees.size, 0)
  oldPlaces : ∀ i : Nat, i < s.book.place.size → s'.book.place[i]? = s.book.place[i]?
  /-- one place more in the book: so statement and book are in step behind as well -/
  places : s'.book.place.size = s.book.place.size + 1
  /-- every older tree is as it was -/
  oldTrees : ∀ i : Nat, i < s.book.trees.size → s'.book.trees[i]? = s.book.trees[i]?
  /-- Omega's tree: in the border's copy of the shared book it has one part (the block's own test);
  the new tree behind has that tree's number and source -/
  tree : ∃ (q : Nat × Nat) (t tO : Tree), b.shared.book.place[b.shared.omega]? = some q ∧
    b.shared.book.trees[q.1]? = some t ∧ t.parts.size = 1 ∧
    s'.book.trees[s.book.trees.size]? = some tO ∧ tO.number = t.number ∧ tO.src = t.src
  /-- "in order" (`Means.InOrder`) is kept: from this statement in front and the border's
  copy of the shared statement to the statement behind -/
  order : Means.InOrder s.st → Means.InOrder b.shared.st → Means.InOrder s'.st

end VerifiableInference.Desc.Third
