-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/CloseToys.lean: TESTS ON MADE-UP DATA; NO THEOREM: `closeFrame`
(Johnson/Desc/First/Close/Closing.lean) at a made-up frame, statement, plan and rounds: a yes, with
what is handed on; and for each named guard for which such data were found, the same data with ONE
thing turned: a no UNDER THAT GUARD'S OWN NAME. The file does not compile if one of these lines is
false.
The statement, the entries and the rounds are those of Johnson/Desc/First/Close/Law/NotEmpty.lean's
toy (a group of one member and two open rows; k = 2), typed again here so that this file stands over
the text alone; the target 3723 is that file's, reckoned there by hand.
HOW FAR THEY GO. NO LINE FOR: K10.layout (no data found at which the ground's four clauses hold and
the statement has no layout for the group) · three of `spendAsMaskL`'s four clauses (the message is
there · not sampled · no answer): at each such data K10.maskfits refuses first · the two arms
"K10.items" behind a round that `heard` has passed.
-/
import Johnson.Desc.First.Close.Closing

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close.MeansToys
open OnBytes

def el (n : Nat) : E := E.ofTriple (n.toUInt64, 0, 0)

/-- The name under which an answer refuses; "yes" where it does not. -/
def why {α : Type} : Except String α → String
  | .ok _ => "yes"
  | .error e => e

/-- A round of a view that holds these elements and drew these. -/
def rv (vals drawn : List E) : Fmt.RoundView :=
  ⟨vals.map fun v => .e v.triple, ⟨drawn.map (·.triple), [], [], none⟩⟩

def r0 : OnBytes.Row := { units := #[⟨0, .main, 0, el 1⟩], target := el 5 }
def r1 : OnBytes.Row := { units := #[⟨0, .main, 1, el 1⟩], target := el 7 }

/-- The group's one member: three main rows. -/
def member : Oracle :=
  { shape := { code := 0, mainRows := 3, maskRows := 0, maskCode := 0, answers := 0 } }

/-- The fold's fresh mask: one mask row. -/
def maskO : Oracle :=
  { shape := { code := noId, mainRows := 0, maskRows := 1, maskCode := 0, answers := 0 } }

def grp : Group :=
  { code := 0, maskCode := 0, members := #[0], kept := #[false], rows := #[r0, r1] }

def st (G : Group) (m : Oracle) : Statement :=
  { codes := { base := #[⟨4, 8, 3⟩], mask := #[⟨4, 8, 3⟩] }, oracles := #[member, m]
    groups := #[G] }

def S0 : Statement := st grp maskO

def ent (name : String) (items rows : Nat) : Fmt.Entry :=
  { name := name, msg := 24 * items, drawE := 1, rows := rows }

def eB : Fmt.Entry := ent "BAT" 0 2
def eE : Fmt.Entry := ent "FOLD epsilon" 1 0
def eR : Fmt.Entry := ent "FOLD round" 2 0
def es0 : List Fmt.Entry := [eB, eE, eR, eR]

def rB : Fmt.RoundView := rv [] [el 3]
def rE : Fmt.RoundView := rv [el 11] [el 4]
def rR1 : Fmt.RoundView := rv [el 1, el 2] [el 5]
def rR2 : Fmt.RoundView := rv [el 3, el 4] [el 6]
def rs0 : List Fmt.RoundView := [rB, rE, rR1, rR2]

/-- The frame at the end of link 0, which has no message of its own (so no moment). -/
def fr : ReqFrame :=
  { shape := { (default : Params.ReqShape) with
      code := 0, maskCode := 0, link := [{ plain := 0, messages := [] }] }
    groups := #[{ k := 2, h := 0 }], next := .laterOrClose, link := 0, moment := 0, group := 0
    mask := some 1 }

/-- The frame's closing at the toy's data, with these turned. -/
def at_ (f : ReqFrame := fr) (S : Statement := S0) (es : List Fmt.Entry := es0)
    (rs : List Fmt.RoundView := rs0) (owed : Option Nat := none) : String :=
  why (closeFrame owed f S es rs)

/-! ## The yes, and what is handed on -/

#guard at_ == "yes"
#guard ((closeFrame none fr S0 es0 rs0).toOption.map fun x =>
    (x.1.link, x.1.mask, x.1.next == .first, x.1.rows.target.triple,
      x.2.oracles.map (·.spentAsMask), x.2.groups.map (·.inRun)))
  == some (1, none, true, (3723, 0, 0), #[false, true], #[true])

/-! ## The frame's four -/

#guard at_ (owed := some 0) == "K10.owed"
#guard at_ (f := { fr with link := 1 }) == "K10.link"
#guard at_ (f := { fr with groups := #[] }) == "K10.group"
#guard at_ (f := { fr with next := .first }) == "K10.due"
#guard at_ (f := { fr with moment := 1 }) == "K10.due"

/-! ## The closing's -/

#guard at_ (es := []) == "K10.stretch"
#guard at_ (rs := []) == "K10.stretch"
#guard at_ (f := { fr with mask := none }) == "K10.mask"
#guard at_ (f := { fr with groups := #[{ k := 1, h := 0 }] }) == "K10.kh"
#guard at_ (f := { fr with groups := #[{ k := 2, h := 1 }] }) == "K10.kh"

/-! ## The batching's -/

#guard at_ (f := { fr with group := 5 }) == "beginRun: the group is there"
#guard at_ (S := st { grp with inRun := true } maskO) == "beginRun: no test has begun"
#guard at_ (S := st { grp with members := #[], kept := #[] } maskO) == "beginRun: a member"
#guard at_ (S := st { grp with members := #[7] } maskO) == "beginRun: every member is there"
#guard at_ (es := [{ eB with rows := 3 }, eE, eR, eR]) == "K10.rows"
#guard at_ (S := st { grp with rows := #[r0, { r1 with units := #[⟨5, .main, 1, el 1⟩] }] } maskO)
  == "K10.combine"

/-! ## A heard round's, at "BAT" -/

#guard at_ (es := [{ eB with name := "BAD" }, eE, eR, eR]) == "K10.name"
#guard at_ (es := [{ eB with drawNZ := 1 }, eE, eR, eR]) == "K10.nonzero"
#guard at_ (es := [{ eB with msg := 24 }, eE, eR, eR]) == "K10.entry"
#guard at_ (es := [{ eB with count := 2 }, eE, eR, eR]) == "K10.entry"
#guard at_ (es := [{ eB with roots := 1 }, eE, eR, eR]) == "K10.entry"
#guard at_ (rs := [rv [el 1] [el 3], rE, rR1, rR2]) == "K10.items"
#guard at_ (es := [{ eB with drawE := 2 }, eE, eR, eR]) == "K10.draws"
#guard at_ (es := [{ eB with drawE := 2 }, eE, eR, eR]) (rs := [rv [] [el 3, el 3], rE, rR1, rR2])
  == "K10.one"
-- an item that is no element of the field
#guard at_ (rs := [rB, ⟨[.root default], rE.drawn⟩, rR1, rR2]) == "K10.items"

/-! ## The fold's -/

#guard at_ (es := [eB, eE, eR]) (rs := [rB, rE, rR1]) == "K10.stretch"
#guard at_ (rs := [rB, rE, rR1]) == "K10.stretch"
#guard at_ (es := [eB, eE, eR, { eR with rows := 1 }]) == "K10.norows"
#guard at_ (f := { fr with shape := { fr.shape with maskCode := 3 } }) == "K10.shape"
#guard at_ (f := { fr with shape := { fr.shape with code := 3 } }) == "K10.shape"
#guard at_ (f := { fr with mask := some 0 }) == "K10.maskfits"
#guard at_ (f := { fr with mask := some 9 }) == "K10.maskfits"
#guard at_ (S := st grp { maskO with sampled := true }) == "K10.maskfits"
#guard at_ (S := st grp { maskO with spentAsMask := true }) == "spendAsMask: not spent before"
#guard at_ (S := st { grp with maskCode := 9 } maskO) == "K10.rowfits"
#guard at_ (rs := [rB, rv [el 11, el 12] [el 4], rR1, rR2]) == "K10.items"
#guard at_ (rs := [rB, rE, rv [el 1] [el 5], rR2]) == "K10.items"
#guard at_ (es := [eB, eE, { eR with name := "FOLD epsilon" }, eR]) == "K10.name"

end VerifiableInference.Desc.First.Close.MeansToys
