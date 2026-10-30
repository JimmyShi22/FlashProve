-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/Laid/DrawsDef.lean: what the shared chain's three blocks of K14 that draw ("LIN
point", "LOC", "LIN zeta"; Johnson/Desc/K14/Text.lean: `linPoint`, `loc`, `linZeta`) have laid, as
plain facts on the record in front (d) and the record behind (d'). Three structures of Prop. No
theorem.

Why. A table of this chain's joints wants, for the promise behind such a block, these facts and
nothing else of the block. That the block's yes gives them: Johnson/Desc/Key/Laid/Draws.lean.

  `PointLaid p d d' r`: r: the one round. Two new groups, without a member or a row, at the next two
    numbers; the small record notes them and the drawn point. Meant where the shape splits the row
    over two codes: where it does not, the text makes one group.
  `LocLaid p d d' r GU rows`: GU: the group G_u in front. rows: the rows (loc_x) that have been laid,
    one for each location drawn, in order, each of the kind "generator".
  `ZetaLaid d d' r`: the small record notes the drawn point; nothing else turns.

Every field but `order` is an equation or a test's yes.

Limits. NOTHING ON CHANCE: what a drawn point is good for is said nowhere here. Nothing on what a row
means. Nothing on soundness or on hiding.
-/
import Johnson.Desc.Key.Laid.JoinedDef

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes

namespace VerifiableInference.Desc.Key

/-- **What "LIN point" has laid**, where the shape splits. -/
structure PointLaid (p : _root_.Desc.Plain.Par) (d d' : _root_.Desc.K14.St) (r : Fmt.RoundView) : Prop where
  loc : d'.loc = { d.loc with psiSh := _root_.Desc.K14.drawn r, gU := d.st.groups.size,
                              gOmega := d.st.groups.size + 1 }
  book : d'.book = d.book
  roots : d'.roots = d.roots
  opened : d'.opened = d.opened
  codes : d'.st.codes = d.st.codes
  oracles : d'.st.oracles = d.st.oracles
  /-- the two new groups stand behind the elder ones -/
  groups : d'.st.groups = (d.st.groups.push { code := p.S.fold.u.code, maskCode := p.S.sharedMaskCode }).push
    { code := p.S.omega.code, maskCode := p.S.sharedMaskCode }
  /-- the block's own second test, in the verifier program's name for it -/
  lin : linOk d.st.codes p.S = true
  /-- "in order" (`Means.InOrder`) is kept -/
  order : Means.InOrder d.st → Means.InOrder d'.st

/-- **What "LOC" has laid.** -/
structure LocLaid (p : _root_.Desc.Plain.Par) (d d' : _root_.Desc.K14.St) (r : Fmt.RoundView)
    (GU : OnBytes.Group) (rows : List OnBytes.Row) : Prop where
  loc : d'.loc = d.loc
  book : d'.book = d.book
  roots : d'.roots = d.roots
  opened : d'.opened = d.opened
  codes : d'.st.codes = d.st.codes
  oracles : d'.st.oracles = d.st.oracles
  groups : d'.st.groups.size = d.st.groups.size
  gU : d.st.groups[d.loc.gU]? = some GU
  gU' : d'.st.groups[d.loc.gU]? = some { GU with rows := GU.rows ++ rows.toArray }
  other : ∀ i : Nat, i ≠ d.loc.gU → d'.st.groups[i]? = d.st.groups[i]?
  /-- one row a location drawn -/
  count : rows.length = r.drawn.poss.length
  kinds : ∀ x ∈ rows, x.kind = .generator
  order : Means.InOrder d.st → Means.InOrder d'.st

/-- **What "LIN zeta" has laid.** -/
structure ZetaLaid (d d' : _root_.Desc.K14.St) (r : Fmt.RoundView) : Prop where
  is : d' = { d with loc := { d.loc with zFd := _root_.Desc.K14.drawn r } }

end VerifiableInference.Desc.Key
