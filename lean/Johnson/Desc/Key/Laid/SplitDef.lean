-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/Laid/SplitDef.lean: what the shared chain's block "SPLIT" (K14's text,
Johnson/Desc/K14/Text.lean: `split`) has laid where the shape splits the row over two codes, as one
structure of plain facts on the record in front (d) and the record behind (d'). A structure of Prop.
No theorem.

Why. A table of this chain's joints wants these facts and nothing else of the block. That the
block's function's yes gives them: Johnson/Desc/Key/Laid/Split.lean.

  `SplitLaid S d d' GU GO x l n row mu`: GU, GO: the groups G_u and G_omega in front. x: o_sp's
    record in front; l: its ledger. n: the mask entry taken (kappa). row: (fold)'s row. mu: the
    scalar that the prover sent.

Limits. Nothing on what a row means. Nothing on soundness or on hiding.
-/
import Johnson.Desc.K14.Law.Base
import Johnson.Desc.Means.Order

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes
open _root_.Desc.K14 (fold)
open _root_.Desc.K14.Law (onOmega onU)

namespace VerifiableInference.Desc.Key

/-- **What "SPLIT" has laid.** -/
structure SplitLaid (S : Params.LinShape) (d d' : _root_.Desc.K14.St) (GU GO : OnBytes.Group)
    (x : OnBytes.Oracle) (l : OnBytes.Ledger) (n : Nat) (row : OnBytes.Row) (mu : E) : Prop where
  loc : d'.loc = d.loc
  book : d'.book = d.book
  roots : d'.roots = d.roots
  opened : d'.opened = d.opened
  codes : d'.st.codes = d.st.codes
  size : d'.st.oracles.size = d.st.oracles.size
  two : d.loc.gOmega ≠ d.loc.gU
  /-- (fold)'s row, made of the small record and the codes -/
  made : fold S d.loc (linLayOmega d.st.codes S) = some row
  /-- o_sp and its ledger in front: not shut, an entry left -/
  sp : d.st.oracles[d.loc.oSp]? = some x
  ledger : x.ledger = some l
  notShut : l.closed = false
  left : 0 < l.left
  /-- behind: the same record but for the ledger: one entry less is left -/
  sp' : d'.st.oracles[d.loc.oSp]? =
    some { x with ledger := some { l with next := n + 1, left := l.left - 1 } }
  msgs : ∀ o : Nat, o ≠ d.loc.oSp → d'.st.oracles[o]? = d.st.oracles[o]?
  groups : d'.st.groups.size = d.st.groups.size
  gU : d.st.groups[d.loc.gU]? = some GU
  gO : d.st.groups[d.loc.gOmega]? = some GO
  gU' : d'.st.groups[d.loc.gU]? =
    some { GU with rows := GU.rows.push (onU row GO.members d.loc.oSp n mu) }
  gO' : d'.st.groups[d.loc.gOmega]? =
    some { GO with rows := GO.rows.push (onOmega row GO.members d.loc.oSp n mu) }
  other : ∀ i : Nat, i ≠ d.loc.gU → i ≠ d.loc.gOmega → d'.st.groups[i]? = d.st.groups[i]?
  /-- the two new rows have passed the ground's tests, at the statement and the groups behind -/
  inU : Means.RowIn d'.st { GU with rows := GU.rows.push (onU row GO.members d.loc.oSp n mu) }
    (onU row GO.members d.loc.oSp n mu)
  inO : Means.RowIn d'.st { GO with rows := GO.rows.push (onOmega row GO.members d.loc.oSp n mu) }
    (onOmega row GO.members d.loc.oSp n mu)
  /-- "in order" (`Means.InOrder`) is kept -/
  order : Means.InOrder d.st → Means.InOrder d'.st

end VerifiableInference.Desc.Key
