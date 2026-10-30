-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CarriageHeard.lean: THE CARRIAGE OF Johnson/Road/K4/Carriage.lean AT K4's OWN BLOCK:
its premises said of WHAT K4's HEARING RETURNS, not of a piece's yes. A definition, two
records and three theorems. Bookkeeping: no count is made here.

GENERAL IN THE SEAT L (OnBytes/Desc/First/K4/Steps.lean: how K4's text reads and writes its part T
of the carried record). A piece that holds `below bk`, for a block bk that hears as K4's own block
at the seat L (`HearsAs`: `block L par` itself; or K4's block typed at a part of the record and
lifted), and puts no round behind its own (pc.back = []) says yes only where `hearFl` returns on the
tape of the stretch's transcript, and the record behind is then the record in front with the
hearing's ledger and record laid by the seat's setters and nothing owed (`piece_below_plain`,
Johnson/Desc/Sound/PieceYes.lean; `decide_ok`,
Johnson/Desc/First/K4/BlockLaws.lean). The tests of work pass there, so those of the rounds that the
maps read pass (`Maps.pass_of_passT`, Johnson/Flat/CarrySWhole.lean).

  `behindOf L pc a τ o G`: that statement behind.
  `Yes L par pc a τ fo o G`: what a yes gives, as one record: the lookup's return, every word shown
    is below the prime, the rounds fit K4's table, the hearing's return.
  `yes_of_out`: a yes of such a piece gives the tests of work, a `Yes`, and that statement behind.
  `Plan4.Heard`: three premises, each at every `Yes`: `kept`, `last`, `first`: those of
    `Plan4.Tied` at `behindOf`.
  `Plan4.tied_of_heard`: at such a piece: `Plan4.Tied` from `Plan4.Heard`. The field `work` is paid
  here.
  `Plan4.leads_heard`: the plain law of such a piece, for each m, from `Plan4.Heard`, if the maps
  are as asked (Mp.OK) and the piece's errors bear the carried ones.

Limits. `Plan4.Heard` IS A PREMISE: NOTHING HERE SHOWS THAT IT CAN BE MET. Those of Carriage.lean
and of the two files named above. No law of the seat is asked here (that `L.own` reads what
`L.setOwn` wrote, and the like): whoever pays `Plan4.Heard` at a seat needs them. A sub-proof that
is not the first alone (the value's chain is that one). No premise here says g ≠ 0, and the maps'
type does not bar g = 0 (a written round may be skipped): what cannot be paid there are the fields
`last` and `first` (the embedding's claim stands in no stage of this chain).
-/
import Johnson.Road.K4.Carriage
import Johnson.Desc.Plain.K04Plain
import Johnson.Desc.Sound.PieceYes
import Johnson.Desc.First.K4.BlockLaws
import Johnson.Flat.CarrySWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop OnBytes OnBytes.Model OnBytes.Model.Layer OnBytes.K.Kc
open OnBytes.Flat OnBytes.Maker Cb.Pv.Att Cb.Pv.Lay Cb.Pv.Lay.At
open OnBytes.Desc.First.K4
open _root_.Run (ckP)
open VerifiableInference.Desc (noDigest)
open VerifiableInference.Desc.Sound (Frame Piece below)
open VerifiableInference.Desc.Plain.K04 (HearsAs)
open Inst.Model (Scl)

variable {T Wt Cl : Type} {Fr : Frame}

section Seat
variable (L : Seat T)

/-- The statement behind a yes: the hearing's ledger and record laid by the seat's setters, nothing
owed; the stored table as it was, and what the stage leaves. -/
def behindOf (pc : Piece (ckP .two) Fr T Cl Wt) (a : T × Fr.E.Str)
    (τ : Tr (uLT (ckP .two) pc.ds)) (o : Own) (G : Fork) : T × Fr.E.Str :=
  (L.setOwed (L.setOwn (L.setFork a.1 G) o) none, (a.2.1, sLeft (ckP .two) pc.stage a.2 τ))

/-- What a yes of the piece gives. -/
structure Yes (par : Par) (pc : Piece (ckP .two) Fr T Cl Wt) (a : T × Fr.E.Str)
    (τ : Tr (uLT (ckP .two) pc.ds)) (fo : Forest.Heard) (o : Own) (G : Fork) : Prop where
  look : L.look a.1 = some fo
  small : (((rvT (ckP .two) pc.ds τ).map noDigest).all fun r =>
    r.vals.all OnBytes.Maker.okGot && r.drawn.elems.all fun x => okE (E.ofTriple x)) = true
  fits : fitsAll (rounds par.P par.hp par.g) (entries par.P par.hp par.g)
    ((rvT (ckP .two) pc.ds τ).map noDigest) = true
  hears : hearFl { par.P with tokv := L.tokv a.1 } par.hp par.g fo (L.fork a.1)
    (paired ((rvT (ckP .two) pc.ds τ).map noDigest) (entries par.P par.hp par.g)) = some (o, G, [])

/-- A yes of a piece that holds `below bk`, bk a block that hears as K4's own at the seat L, and
puts no round behind its own, taken apart. -/
theorem yes_of_out {par : Par} {pc : Piece (ckP .two) Fr T Cl Wt}
    {bk : VerifiableInference.Desc.Block T Cl}
    (hk : HearsAs L par bk)
    (hb : pc.b = below bk) (hback : pc.back = []) (a b : T × Fr.E.Str)
    (τ : Tr (uLT (ckP .two) pc.ds)) (h : pc.ior.red.out a τ = some b) :
    passT (ckP .two) pc.ds (rhoT (ckP .two) pc.ds τ) = true ∧
      ∃ fo o G, Yes L par pc a τ fo o G ∧ b = behindOf L pc a τ o G := by
  obtain ⟨h1, h2, h3, cols, h4⟩ :=
    VerifiableInference.Desc.Sound.piece_below_plain pc _ hb hback a b τ h
  obtain ⟨_, e1, _, fo, o, G, e2, e3, e4⟩ := hk _ _ _ _ h4
  exact ⟨h1, fo, o, G, ⟨e2, h3, e1, e3⟩, Prod.ext e4 h2⟩

end Seat

section AtTheValue
variable [scl : Scl] {Mm X : Type}

/-- The premises of `Plan4.Tied`, said of what K4's hearing returns. -/
structure Plan4.Heard (Q : Plan4 Cb.Gl.E Mm X) (L : Seat T) (Ex : ExtSpec) (par : Par)
    (pc : Piece (ckP .two) Fr T Cl Wt) (Mp : Maps pc.ds (Q.full.own.toOwn.ch.R Ex).shape)
    (fa : T × Fr.E.Str → X × Ex.Str) (part : Wt → Mm) (on on' : T × Fr.E.Str → Prop)
    (Front Behind : T × Fr.E.Str → Wt → Prop) : Prop where
  /-- the promise behind holds -/
  kept : ∀ a τ fo o G, on a → Yes L par pc a τ fo o G → on' (behindOf L pc a τ o G)
  /-- what the row opens gives the chain's last claim, at the chain's own output on the
  transcript's image -/
  last : ∀ a τ fo o G w, on a → Yes L par pc a τ fo o G → Behind (behindOf L pc a τ o G) w →
    Q.full.own.toOwn.ch.Last (fun _ _ => True)
      (Q.full.own.toOwn.ch.val Ex (fa a) (Mp.view τ)).1 (part w)
  /-- with what the row opens, what is claimed before the chain's first round gives what the row
  closes -/
  first : ∀ a τ fo o G w, on a → Yes L par pc a τ fo o G → Behind (behindOf L pc a τ o G) w →
    Q.full.own.pT (fa a).1 (part w) → Front a w

/-- **`Plan4.Tied` at K4's own block, from what its hearing returns**, at a piece that puts no round
behind its own. -/
theorem Plan4.tied_of_heard (Q : Plan4 Cb.Gl.E Mm X) (L : Seat T) (Ex : ExtSpec) {par : Par}
    {pc : Piece (ckP .two) Fr T Cl Wt} {Mp : Maps pc.ds (Q.full.own.toOwn.ch.R Ex).shape}
    {fa : T × Fr.E.Str → X × Ex.Str} {part : Wt → Mm} {on on' : T × Fr.E.Str → Prop}
    {Front Behind : T × Fr.E.Str → Wt → Prop}
    {bk : VerifiableInference.Desc.Block T Cl}
    (hk : HearsAs L par bk)
    (hb : pc.b = below bk)
    (hback : pc.back = []) (H : Q.Heard L Ex par pc Mp fa part on on' Front Behind) :
    Q.Tied Ex pc Mp fa part on on' Front Behind where
  work := fun a τ b _ h => Mp.pass_of_passT τ (yes_of_out L hk hb hback a b τ h).1
  kept := fun a τ b ha h => by
    obtain ⟨_, fo, o, G, hy, rfl⟩ := yes_of_out L hk hb hback a b τ h
    exact H.kept a τ fo o G ha hy
  last := fun a τ b w ha h hB => by
    obtain ⟨_, fo, o, G, hy, rfl⟩ := yes_of_out L hk hb hback a b τ h
    exact H.last a τ fo o G w ha hy hB
  first := fun a τ b w ha h hB hp => by
    obtain ⟨_, fo, o, G, hy, rfl⟩ := yes_of_out L hk hb hback a b τ h
    exact H.first a τ fo o G w ha hy hB hp

/-- **The plain law of the piece that holds K4's own block** and puts no round behind its own, the
messages m outside the game; the maps are as asked and the piece's errors bear the carried ones. -/
theorem Plan4.leads_heard (Q : Plan4 Cb.Gl.E Mm X) (L : Seat T) (Ex : ExtSpec) {par : Par}
    {pc : Piece (ckP .two) Fr T Cl Wt} {Mp : Maps pc.ds (Q.full.own.toOwn.ch.R Ex).shape}
    {fa : T × Fr.E.Str → X × Ex.Str} {part : Wt → Mm} {on on' : T × Fr.E.Str → Prop}
    {Front Behind : T × Fr.E.Str → Wt → Prop}
    {bk : VerifiableInference.Desc.Block T Cl}
    (hk : HearsAs L par bk)
    (hb : pc.b = below bk)
    (hback : pc.back = []) (hOK : Mp.OK)
    (herr : Err.le (Mp.err (Q.full.own.toOwn.ch.eps Ex)) pc.err)
    (H : Q.Heard L Ex par pc Mp fa part on on' Front Behind) (m : Mm) :
    pc.ior.red.Leads on
      (fun a b => on' b ∧ ∀ w, part w = m → Behind b w → Front a w) pc.err :=
  Q.leads Ex hOK herr (Q.tied_of_heard L Ex hk hb hback H) m

end AtTheValue
end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.yes_of_out
#print axioms OnBytes.Road.K4.Plan4.tied_of_heard
#print axioms OnBytes.Road.K4.Plan4.leads_heard
