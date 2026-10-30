-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Tape/Tape.lean: the strict way from a view's rounds and the plan's entries to the
tape on which the flat functions of OnBytes/K/Kc/ run; and the run of a flat function on a stretch.
Definitions with code. No theorem.

Why. A flat function (`Fl`, OnBytes/K/Kc/Flat.lean) hears rounds off a `Tape`. The library's maker
of a tape, `paired` (OnBytes/K/Kc/Laws.lean:64), was made for laws in one direction, from the
program's success to the flat value: it lets by what the program's channel refuses (an item of
another kind behind the elements; drawn positions and matrix entries; an entry's number of draws;
rows that are owed; entries that are left over). Here the channel's guards on a round and its entry
are asked first, a clause a round, and with them what the format's rule on a described round asks of
an entry whose message is elements alone.

Main names:
  `TapeRule`: what differs from step to step: which of its entries may count rows, and under which
    kind its routines close a name.
  `kindAsked`: the kind under which `trAnswer`, `trAnswerNotZero`, `trPoint`, `trEmpty` and
    `trBatchOpen` close a name (OnBytes/Model/Rounds.lean:143-176).
  `elemsOf`, `roundT rule r e`, `tapeT rule rs es`: a message's items as elements; a round with its
    entry as a `FlatRound`; **the tape**; each or nothing.
  `flRun rule f es F rs`: **a flat function on a stretch**: the tape, then f, the tape used up.

Limits: of an entry it does not read work and logN. What a round draws has a fourth part, a digest:
neither the program's close nor this file reads it. THAT A SENT WORD IS BELOW THE FIELD'S PRIME IS
NOT ASKED HERE: `elemsOf` lays an element as it stands, as the program's own receipt does
(OnBytes/Iop/Ground.lean:778-781). That test has one home, in front of all that reads a view:
whoever folds asks it of the whole view's sent items and opened columns (`okView`,
OnBytes/Maker/OkView.lean, which says why; so the library's decision on views:
OnBytes/Maker/Decide3.lean:85-87). THAT A DRAWN WORD IS BELOW THE PRIME IS NOT ASKED HERE EITHER:
its home is the same place in front, and `okView` does not yet read what is drawn; it holds where
the draws are made by the format's rule. That an element which the entry draws other than 0 is not 0
hangs on the entry and is asked here: clause 7: a comparison of the raw words with 0, which is right
only behind that test in front (kin in the library, on a view alone and of another type:
`FlatRound.ofRV`, `FlatRound.fits`, OnBytes/G4/Flat.lean; `elemsOf` is the like of its map over the
items). Where a clause fails the whole stretch is refused before a round is heard: the decision is
the program's, the place of the refusal is not. A RULE THAT NAMES AN ENTRY TAKES OVER BOTH GUARDS
FOR IT (Ground.lean:825, :852-857): its rows go into the tape, where `closeRows` holds them
(Flat.lean:119) and `closeN`, `closeOne` do not look at them (:109, :115); `flRun` hands back no
debt: the step that named the entry asks for the rows or hands them on. That the entry closed last
before the stretch owes none is the step's too. THAT es ARE THE PLAN'S NEXT ENTRIES IS ASKED BY
NOBODY HERE: es is an argument: it is the caller's to make them, or to hold them against the plan. A
stretch's first round must come whole: no caller has taken items of it. That the tape is `paired`'s
wherever nothing is refused is not stated here. Of the names that stand in a proof file's three
chains such a tape bears, at the rule {}: BASE lambda, FOLD round, JOIN, LINE, LIN point, LIN zeta,
LKP, LKP shift, PSC epsilon, PSC round, PSC Y, PSC values, ZERO. Only if the rule names the entry
(clause 4): BAT, BAT-sigma. Only at another kind than `kindAsked`'s (clause 5): FOLD epsilon, REPLY,
SPLIT, SEAL. Never: a round with roots or answers (SEND seed, SEND answer), with positions (LOC, CS,
BASE), with matrix entries (RNG). Nothing has been shown of it.

THE GUARDS. A row: the program's file:line · where it stands here · class (V: a turned view can trip
it; P: a turned plan can; T: no input can).
  Ground.lean:781 an item of another kind is taken · elemsOf, third arm · V
  Ground.lean:841 no item unread · elemsOf, with Flat.lean:108-122 (sent = []) · V
  Ground.lean:841 drawn.elems.length = e.drawE · roundT, clause 1 · V, P
  Ground.lean:841 drawn.poss.length = e.poss, and Rounds.lean:96 e.poss = 0 · clause 2 · V, P
  Ground.lean:842 drawn.trits.length = e.trits, and Rounds.lean:96 e.trits = the call's number of
    matrix entries, which is 0 in each close that hears elements · clause 3 · V, P
  Ground.lean:825 settled: where the step's routines ask for no rows none may be owed · clause 4 · P
  Rounds.lean:108 noBatching · clause 4 · T there
  Rounds.lean:93 the format's kind of the name is the call's · clause 5, with the rule's kind · T
    there (the program's two stand on the call's name, these on the entry's: a turned plan can trip
    them, but never alone: the name's guard refuses the same input: no control of their own)
  Fmt/Rules8.lean:210-212 the items' bytes are e.msg; the roots and the answers among them e.roots
    and e.answers; e.count = 1 (asked there of a DESCRIBED round, before there is a view) · clause 6
    · P
  Ground.lean:823, :839 as many entries as rounds · tapeT, last arm (that none lacks when a flat
    function wants one more: Flat.lean:111, :116, on the empty tape) · V, P
  (none in the program's channel) the elements that the entry draws other than 0, the last drawNZ of
    those drawn, are not 0 · clause 7 · V: idle where the draws are made by the format's rule: such
    an element is the first of two that is not 0, else 1 (OnBytes/Params/Planner.lean:701-704). At
    an entry that the format's own test takes, of the kind "elems" (`Entry.fits`,
    Fmt/Rules6Round.lean:72), drawNZ is 0 or drawE: the last drawNZ are then none or all. Where
    drawNZ is more than drawE all that is drawn is asked. In a round of the kind "seeds" the places
    are others: `kindAsked` never says that kind, so clause 5 refuses such a round at the rule {}; a
    rule whose `kind` says it takes that over
  the run's end: entries and rounds used up · flRun, the pattern [] · V, P
  Ground.lean:763, :832 a message that is open in front (`Chan.cur`) is gone on with; :958, :982
    none is open at a run's end · no clause: a stretch is whole rounds: `flRun` is handed no round
    of which items are taken, and leaves none (Flat.lean:108-122: sent = []) · T

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Kc.Flat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Tape
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Fork)

/-- The kind under which the program's routines that hear elements close a round of this name. -/
def kindAsked (name : String) : Fmt.Kind :=
  if name == Model.RoundName.pscEpsilon.name then .join
  else if name == Model.RoundName.pscValues.name then .nothing
  else .elems

/-- What differs from step to step. -/
structure TapeRule where
  /-- this entry of the stretch may count rows, or bear the name of the round that batches rows: the
  step asks for them, or hands them on. A free function: at `fun _ => true` clause 4 is idle -/
  rows : Fmt.Entry → Bool := fun _ => false
  /-- the kind under which the step's routines close a name. A free function: made of the format's
  own `kindOf`, clause 5 is idle -/
  kind : String → Fmt.Kind := kindAsked

/-- A message's items as elements of the extension field; nothing if one is of another kind. -/
def elemsOf : List Fmt.ItemValue → Option (List E)
  | [] => some []
  | .e x :: l => (elemsOf l).map (E.ofTriple x :: ·)
  | _ :: _ => none

/-- A view's round with its entry in the plan, as plain data; nothing unless seven clauses hold. The
seventh: the LAST drawNZ of the drawn elements are not (0, 0, 0): the format's rule draws the plain
elements first, then those that must not be 0 (`drawPlainNZ`, Fmt/Rules6Round.lean:95-107). -/
def roundT (rule : TapeRule) (r : Fmt.RoundView) (e : Fmt.Entry) : Option FlatRound :=
  match elemsOf r.vals with
  | none => none
  | some sent =>
    if r.drawn.elems.length == e.drawE &&
        (r.drawn.poss.isEmpty && e.poss == 0) &&
        (r.drawn.trits.isEmpty && e.trits == 0) &&
        ((e.rows == 0 && e.name != Model.RoundName.batSigma.name) || rule.rows e) &&
        Params.kindOf e.name == some (rule.kind e.name) &&
        (e.msg == 24 * sent.length && e.roots == 0 && e.answers == 0 && e.count == 1) &&
        ((r.drawn.elems.drop (e.drawE - e.drawNZ)).all fun x => !isZeroE (E.ofTriple x)) then
      some { name := some e.name, nz := e.drawNZ, rows := e.rows, sent := sent,
             drawn := r.drawn.elems.map E.ofTriple }
    else none

/-- **The tape**: the stretch's rounds with the stretch's entries, one for one. -/
def tapeT (rule : TapeRule) : List Fmt.RoundView → List Fmt.Entry → Option Tape
  | [], [] => some []
  | r :: rs, e :: es =>
    match roundT rule r e, tapeT rule rs es with
    | some x, some t => some (x :: t)
    | _, _ => none
  | _, _ => none

/-- **A flat function on a stretch.** es: the plan's entries of the stretch. Nothing is left. -/
def flRun {α : Type} (rule : TapeRule) (f : Fl α) (es : List Fmt.Entry) (F : Fork)
    (rs : List Fmt.RoundView) : Option (α × Fork) :=
  match tapeT rule rs es with
  | none => none
  | some t =>
    match f F t with
    | some (a, G, []) => some (a, G)
    | _ => none

end VerifiableInference.Desc.First.Tape
