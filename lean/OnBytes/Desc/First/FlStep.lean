-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Desc/First/FlStep.lean: any plain function of the type `Fl`
(OnBytes/K/Kc/Flat.lean: from a sub-proof's state and the rounds not yet closed to a value, the new
state and the rounds left, or nothing) as a step of a chain's decision. CODE ALONE: no theorem. For
every writer of a step that hears field elements; it names no lot's text.


THE DEBT
OF ROWS IS PLAIN DATA OF THE STEP: it is read off the state in front, asked, and laid into the state
behind; an entry's rows have THREE answers in the place of a Bool.

The type of a step is that of Johnson/Desc/Step.lean: `Step S := S → List Fmt.RoundView → List OpenedColumn → Option
(S × Nat)`, written out here in two abbreviations in the place of an import of that file.

`ofFlWith how es fork owed x put`. es: the plan's entries of the stretch. The rounds are paired with
them by `paired` (OnBytes/K/Kc/Laws.lean) and handed to the function as its tape. The
step refuses unless (0) NOTHING IS OWED IN FRONT (`owed s` is none), if the stretch has a round; (1)
there are as many entries as rounds; (2) every round is PLAIN under its entry (`plainRoundWith`);
(3) the function returns; (4) it has used the tape up. It takes no column. Behind, `put` is handed
what is owed then (`owedBehind`).

THE DEBT. `owed : S → Option Nat`: some n: the round closed last counts n batched rows and nobody
has compared that number (S.rowsOwed and RowsOwed in other files). `how e` says of each entry of the
stretch how its count of rows is answered for: `.no`: it counts none (asked: e.rows == 0) ·
`.inside`: the function itself compares the number (by `closeRows`, through `Fl.batch`) · `.on`: it
is handed on to a later step: allowed at the LAST entry alone; the state behind then owes e.rows.
`.inside` IS THE CALLER's WORD, BY THE ENTRY: what compares is the close that the function calls,
and no code here sees that. The program's guard for it is `noBatching`
(OnBytes/Model/Rounds.lean:108); Flat.lean's `answer` and `point` lack it. SO A CLAIM OVER THIS FILE
NAMES, FOR EACH ENTRY THAT IT CALLS `.inside`, THE `Fl.batch` THAT ASKS IT, BY file:line.
`batSigmaInside`: `.inside` at the name "BAT-sigma", else `.no`: right where every round of that
name in the stretch is closed by `Fl.batch` (the layers' own rounds; by a reading, not shown here,
also attention's three hearing steps and the head's own rounds and merge); WRONG at a batching draw
(its rows are asked in the door's step: `.on`), and it says nothing of "CS" or "BAT".

THE LIST: all that the program's closes ask of a round of this kind · the program's file:line
· where it is asked.
  an entry is left; a round is left · OnBytes/Iop/Ground.lean:822-823, :838-839 · `plainStretchWith`
    (as many entries as rounds) with (4)
  the entry's name; its number of draws that are never 0 · Ground.lean:825 · Flat.lean's `closeN`,
    `closeOne`, `closeRows` (:108-122)
  nothing is owed in front · Ground.lean:825 with :602-605 · (0)
  the format's kind of the name · OnBytes/Model/Rounds.lean:93 · NOT ASKED: a constant of the
    library at each name: no input reaches it
  no bare close of a batching round · Rounds.lean:108 · NOT ASKED IN CODE: the caller's word
    `.inside` (above)
  every item of the message was taken, and each is an element of the extension field ·
    Ground.lean:841 with :778-781 · Flat.lean's closes (`sent` is empty) with `r.vals.all …`
    (`paired` keeps the LEADING elements alone)
  as many drawn elements, positions, matrix entries as the entry says · Ground.lean:841-842 · the
    three comparisons of lengths
  the entry draws the call's number of elements, no position, no matrix entry · Rounds.lean:96 ·
    Flat.lean's closes (the drawn list's length is the call's) with the first comparison; `e.poss ==
    0 && e.trits == 0`
  the entry's own debt · Ground.lean:602-605, asked at the NEXT close · `rowsOk`, and `owedBehind`
Not asked, as in these routines of the program: the entry's work, bytes, roots, answers and logN.

WHAT HAS RUN. Lines of another form of this file, at the layers' own rounds of the two
stored proofs of another form of the release (2 | 12 links) in the skeleton's slot; in the
mode «both» at the small one (the same, whole); seven controls, one for each condition of its
plainRound, each refused at the step and accepted with just that condition left out.
THIS FORM HAS NOT RUN. NOTHING HAS RUN AT AN ATTENTION LINK OR AT THE HEAD's.
It fits a stretch of field elements alone: not SEND, LOC, RNG, REPLY, BAT, FOLD.
Main names (namespace `OnBytes.Desc.First.Kit`): `Col`, `Step`; `RowsHow`, `batSigmaInside`,
`rowsOk`, `owedBehind`; `plainRoundWith`, `plainStretchWith`; `ofFlWith`, `ofFl`, `quietFl`,
`quiet`. Controls: OnBytes/Desc/First/Try/FlStepToy.lean.
-/
import OnBytes.K.Kc.Laws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.Kit
open OnBytes OnBytes.Model OnBytes.K.Kc

/-- An opened column, as a view holds it: the tree's key, the leaf, the words. -/
abbrev Col : Type := Nat × Nat × List UInt64

/-- A step: the state, this stretch's rounds, the opened columns not yet taken; the new state and
how many columns were taken, or a refusal. -/
abbrev Step (S : Type) : Type := S → List Fmt.RoundView → List Col → Option (S × Nat)

/-- How an entry's count of batched rows is answered for. -/
inductive RowsHow where
  /-- it counts none -/
  | no
  /-- the function itself compares the number -/
  | inside
  /-- it is handed on to a later step: at a stretch's last entry alone -/
  | on
  deriving DecidableEq, Repr

/-- The rounds named "BAT-sigma", and they alone, have their rows compared inside. -/
def batSigmaInside (e : Fmt.Entry) : RowsHow :=
  if e.name == RoundName.batSigma.name then .inside else .no

/-- The entry's count of rows is answered for. last: it is the stretch's last entry. -/
def rowsOk (how : Fmt.Entry → RowsHow) (last : Bool) (e : Fmt.Entry) : Bool :=
  match how e with
  | .no => e.rows == 0
  | .inside => true
  | .on => last

/-- What is owed behind a stretch. front: what was owed in front of it. -/
def owedBehind (how : Fmt.Entry → RowsHow) (es : List Fmt.Entry) (front : Option Nat) :
    Option Nat :=
  match es.getLast? with
  | none => front
  | some e =>
    match how e with
    | .on => if e.rows == 0 then none else some e.rows
    | _ => none

/-- A round in which elements of the extension field alone are sent and drawn, under an entry that
says so and whose count of rows is answered for. -/
def plainRoundWith (how : Fmt.Entry → RowsHow) (last : Bool) (e : Fmt.Entry) (r : Fmt.RoundView) : Bool :=
  e.poss == 0 && e.trits == 0 && r.drawn.elems.length == e.drawE &&
    r.drawn.poss.length == e.poss && r.drawn.trits.length == e.trits &&
    rowsOk how last e &&
    r.vals.all fun x => match x with | .e _ => true | _ => false

/-- As many entries as rounds, and every round plain under its entry. -/
def plainStretchWith (how : Fmt.Entry → RowsHow) : List Fmt.Entry → List Fmt.RoundView → Bool
  | [], [] => true
  | e :: es, r :: rs => plainRoundWith how es.isEmpty e r && plainStretchWith how es rs
  | _, _ => false

/-- A flat function as a step. how: how each entry's rows are answered for. es: the plan's entries
of the stretch. fork: the sub-proof's state in the step's state. owed: what is owed in front. x: the
function, which may want something of the state that is not there. put: lays back the result, the
new sub-proof's state and what is owed behind. -/
def ofFlWith {S α : Type} (how : Fmt.Entry → RowsHow) (es : List Fmt.Entry) (fork : S → Fork)
    (owed : S → Option Nat) (x : S → Option (Fl α)) (put : S → α → Fork → Option Nat → S) :
    Step S := fun s rs _ =>
  if (es.isEmpty || (owed s).isNone) && plainStretchWith how es rs then
    match x s with
    | none => none
    | some f =>
      match f (fork s) (paired rs es) with
      | some (a, F, []) => some (put s a F (owedBehind how es (owed s)), 0)
      | _ => none
  else none

/-- The same, under `batSigmaInside`. -/
def ofFl {S α : Type} (es : List Fmt.Entry) (fork : S → Fork) (owed : S → Option Nat)
    (x : S → Option (Fl α)) (put : S → α → Fork → Option Nat → S) : Step S :=
  ofFlWith batSigmaInside es fork owed x put

/-- A flat function that takes no round, as a step. What is owed is neither read nor written. -/
def quietFl {S α : Type} (fork : S → Fork) (x : S → Option (Fl α)) (put : S → α → Fork → S) :
    Step S := fun s rs _ =>
  if rs.isEmpty then
    match x s with
    | none => none
    | some f =>
      match f (fork s) [] with
      | some (a, F, []) => some (put s a F, 0)
      | _ => none
  else none

/-- A function on the state as a step that takes no round and no column. -/
def quiet {S : Type} (f : S → Option S) : Step S := fun s rs _ =>
  if rs.isEmpty then (f s).map fun s' => (s', 0) else none

end OnBytes.Desc.First.Kit
