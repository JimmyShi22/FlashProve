-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/Laid/RecDef.lean: what the shared chain's block "(rec_gamma)" (K14's text,
Johnson/Desc/K14/Text.lean: `laysRec`) has laid, as one structure of plain facts on the record in
front (d) and the record behind (d'). A structure of Prop. No theorem.

Why. A table of this chain's joints wants these facts and nothing else of the block. That the
block's function's yes gives them: Johnson/Desc/Key/Laid/Rec.lean.

  `RecLaid p d d' GU rows`: p: the plan's letter of the text. GU: the group G_u in front. rows: the
    rows that have been laid, in order.

Every field but `order` is an equation or a test's yes. Each message is stated whole: o_u has noted
G_u; every other message is as it was.

Limits. Nothing on what a row means. Nothing on soundness or on hiding.
-/
import Johnson.Desc.Key.Laid.JoinedDef
import Johnson.Desc.K14.Law.LawRL

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes
open _root_.Desc.K14.Law (recRows)

namespace VerifiableInference.Desc.Key

/-- **What "(rec_gamma)" has laid.** -/
structure RecLaid (p : _root_.Desc.Plain.Par) (d d' : _root_.Desc.K14.St) (GU : OnBytes.Group)
    (rows : List OnBytes.Row) : Prop where
  loc : d'.loc = d.loc
  book : d'.book = d.book
  roots : d'.roots = d.roots
  opened : d'.opened = d.opened
  codes : d'.st.codes = d.st.codes
  size : d'.st.oracles.size = d.st.oracles.size
  /-- the block's three tests -/
  fits : d.loc.key.fits p.S.fold.index = true
  seeds : (d.loc.key.seeds.all fun s => !isZeroE s.beta) = true
  gamma : (_root_.Desc.K14.gamma p.S d.loc).length = p.S.fold.index.v
  /-- o_u has noted G_u; every other message is as it was -/
  u : ∀ x : OnBytes.Oracle, d.st.oracles[d.loc.oU.oracle]? = some x →
    d'.st.oracles[d.loc.oU.oracle]? = some (noted x [d.loc.gU])
  rest : ∀ o : Nat, o ≠ d.loc.oU.oracle → d'.st.oracles[o]? = d.st.oracles[o]?
  groups : d'.st.groups.size = d.st.groups.size
  gU : d.st.groups[d.loc.gU]? = some GU
  gU' : d'.st.groups[d.loc.gU]? =
    some { entered GU d.loc.oU.oracle false with rows := GU.rows ++ rows.toArray }
  other : ∀ i : Nat, i ≠ d.loc.gU → d'.st.groups[i]? = d.st.groups[i]?
  /-- the rows: one (rec_gamma) a seed of the key, in the seeds' order -/
  made : recRows p d.loc = some rows
  /-- "in order" (`Means.InOrder`) is kept -/
  order : Means.InOrder d.st → Means.InOrder d'.st

end VerifiableInference.Desc.Key
