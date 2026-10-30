-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/Laid/JoinedDef.lean: what the shared chain's block "joins" (K14's text,
Johnson/Desc/K14/Text.lean: `joins`) has laid where the shape splits the row over two codes, as one
structure of plain facts on the record in front (d) and the record behind (d'). Two definitions, a
structure of Prop and one small theorem.

Why. A table of this chain's joints wants these facts and nothing else of the block. That the
block's function's yes gives them: Johnson/Desc/Key/Laid/Joined.lean.

  `entered G o k`: the group G with the message o entered behind its smaller members, with the mark
    k: `Slice.withMessageInGroup`'s own literal.
  `noted x gs`: the message x with the groups gs noted behind those that it has noted.
  `Joined d d' GU GO`: GU, GO: the groups G_u and G_omega in front.
  `Joined.msgs`: every message behind is the same record but for its list of groups.

Every field but `order` is an equation, an inequation or a test's yes. Each message is stated whole:
o_omega has noted G_omega; o_sp has noted G_omega, then G_u (a chain's end reads these lists); every
other message is as it was.

It is not meant at a shape that does not split: there the text makes one joining and G_u is G_omega,
and `two` is false.

Limits. Nothing on what a member or a row means. Nothing on soundness or on hiding.
-/
import Johnson.Desc.K14.Text
import Johnson.Desc.Means.Order

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes

namespace VerifiableInference.Desc.Key

/-- The group with one message more, entered behind the smaller members. -/
def entered (G : OnBytes.Group) (o : Nat) (k : Bool) : OnBytes.Group :=
  { G with
    members := G.members.insertIdxIfInBounds (G.members.filter (· < o)).size o
    kept := G.kept.insertIdxIfInBounds (G.members.filter (· < o)).size k }

/-- The message with some groups more noted. -/
def noted (x : OnBytes.Oracle) (gs : List Nat) : OnBytes.Oracle :=
  { x with groups := x.groups ++ gs }

/-- **What the joinings have laid.** -/
structure Joined (d d' : _root_.Desc.K14.St) (GU GO : OnBytes.Group) : Prop where
  loc : d'.loc = d.loc
  book : d'.book = d.book
  roots : d'.roots = d.roots
  opened : d'.opened = d.opened
  codes : d'.st.codes = d.st.codes
  size : d'.st.oracles.size = d.st.oracles.size
  /-- two groups, two messages -/
  two : d.loc.gU ≠ d.loc.gOmega
  apart : d.loc.oOmega ≠ d.loc.oSp
  /-- o_omega has noted G_omega; o_sp G_omega, then G_u; every other message is as it was -/
  omega : ∀ x : OnBytes.Oracle, d.st.oracles[d.loc.oOmega]? = some x →
    d'.st.oracles[d.loc.oOmega]? = some (noted x [d.loc.gOmega])
  sp : ∀ x : OnBytes.Oracle, d.st.oracles[d.loc.oSp]? = some x →
    d'.st.oracles[d.loc.oSp]? = some (noted x [d.loc.gOmega, d.loc.gU])
  rest : ∀ o : Nat, o ≠ d.loc.oOmega → o ≠ d.loc.oSp → d'.st.oracles[o]? = d.st.oracles[o]?
  groups : d'.st.groups.size = d.st.groups.size
  gU : d.st.groups[d.loc.gU]? = some GU
  gO : d.st.groups[d.loc.gOmega]? = some GO
  gU' : d'.st.groups[d.loc.gU]? = some (entered GU d.loc.oSp false)
  gO' : d'.st.groups[d.loc.gOmega]? =
    some (entered (entered GO d.loc.oOmega false) d.loc.oSp false)
  other : ∀ i : Nat, i ≠ d.loc.gU → i ≠ d.loc.gOmega → d'.st.groups[i]? = d.st.groups[i]?
  /-- the block's own test, in the text's own words (Johnson/Desc/Own/Alone.lean): the tree at the
  number that o_omega's place names has o_omega as its one part (in the book, which does not turn).
  It is spent by no row so far: it rides for the rows that open Omega's tree -/
  alone : Own.aloneIn d.book d.loc.oOmega = true
  /-- "in order" (`Means.InOrder`) is kept -/
  order : Means.InOrder d.st → Means.InOrder d'.st

/-- Every message behind is the same record but for its list of groups. -/
theorem Joined.msgs {d d' : _root_.Desc.K14.St} {GU GO : OnBytes.Group} (J : Joined d d' GU GO)
    (o : Nat) (x : OnBytes.Oracle) (h : d.st.oracles[o]? = some x) :
    ∃ gs, d'.st.oracles[o]? = some { x with groups := gs } := by
  by_cases h1 : o = d.loc.oOmega
  · subst h1
    exact ⟨_, J.omega x h⟩
  · by_cases h2 : o = d.loc.oSp
    · subst h2
      exact ⟨_, J.sp x h⟩
    · exact ⟨x.groups, (J.rest o h1 h2).trans h⟩

end VerifiableInference.Desc.Key
