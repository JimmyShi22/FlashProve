-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Whose.lean: text for printouts. No decision depends on it. OnlineDescriptionFromBlockTables.lean imports
it for one function, `kindWord`, which it uses in the words of its refusals.
The rest makes a table of the places of a chain: for each block one line that says which lot's block
stands there and which named steps of `verify-on-bytes` lie at that place, and two lines of counts.
It imports Johnson/Desc/Block.lean alone.
Limit. "A LOT's" in a line says that a lot's block stands at the place, and no more. Which routines
that block's decision calls cannot be seen from here, and which of the place's steps the lot
replaces is the lot's own statement. A walk over the constants that the blocks reach can show it.
  `Whose`      from a block's name to the name of the lot whose block stands there
  `StepsAt`    `verify-on-bytes`'s steps at a place
  `Share`, `shareOf`   whether a place is a lot's wholly, in part, or not at all, by the lots' own
               statements
  `placeLine`, `countLine`, `stepsLine`, `placeLines`   the lines
A place counts as free of `verify-on-bytes` only if none of its steps is still run by it.

-/
import Johnson.Desc.Block

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile
open VerifiableInference.Desc (KindName Place)

/-- From a block's name to the name of the lot whose block stands there. -/
abbrev Whose : Type := List (String × String)

/-- `verify-on-bytes`'s steps at a place. -/
structure StepsAt where
  /-- the place's name -/
  name : String
  /-- the number of its first step, from 1 -/
  first : Nat
  /-- its steps' full names -/
  steps : List String

/-- The steps at a place; none if the table has no entry for it. -/
def stepsOf (st : List StepsAt) (name : String) : List String :=
  ((st.find? fun x => x.name == name).map (·.steps)).getD []

/-- A kind's name, as a string. -/
def kindWord : KindName → String
  | .K1 => "K1" | .K2 => "K2" | .K3 => "K3" | .K4 => "K4" | .K5 => "K5" | .K6 => "K6" | .K7 => "K7"
  | .K8 => "K8" | .K9 => "K9" | .K10 => "K10" | .K11 => "K11" | .K12 => "K12" | .K13 => "K13"
  | .K14 => "K14" | .K15 => "K15" | .frame => "frame"

/-- A block of the kind `frame` that has no round and at whose place no step lies. -/
def bareFrame (st : List StepsAt) (x : String × Place × Nat) : Bool :=
  x.2.1.kind == KindName.frame && x.2.2 == 0 && (stepsOf st x.1).isEmpty

/-- Whose a place is, by the lots' own statements: no lot's block stands there; a lot's block stands
there, and the lot says of none, of some, or of all of the place's steps that `verify-on-bytes`
still runs them. -/
inductive Share where
  | standIn
  | whole (lot : String)
  | half (lot : String) (mine older : List String)
  | none_ (lot : String)

/-- Whose the place of that name is. `still`: the steps that their lots say are still
`verify-on-bytes`'s. -/
def shareOf (w : Whose) (still : List String) (st : List StepsAt) (name : String) : Share :=
  match w.lookup name with
  | none => .standIn
  | some h =>
    let steps := stepsOf st name
    let older := steps.filter still.contains
    if older.isEmpty then .whole h
    else if older.length == steps.length then .none_ h
    else .half h (steps.filter fun s => !still.contains s) older

/-- The line of one place. `said`: other words for a place at which no lot's block stands. -/
def placeLine (w said : Whose) (still : List String) (st : List StepsAt)
    (x : String × Place × Nat) : String :=
  let steps := stepsOf st x.1
  s!"PLACE = {x.1} ; chain = {x.2.1.chain} ; link = " ++
    (match x.2.1.link with | some l => toString l | none => "-") ++
    s!" ; piece = {x.2.1.piece} ; kind = {kindWord x.2.1.kind} ; rounds = {x.2.2} ; " ++
    s!"steps = {steps.length} {steps} ; text = " ++
    (match shareOf w still st x.1 with
     | .whole h => "A LOT's: " ++ h
     | .half h mine older =>
       s!"A LOT's: {h}: {mine} | STAND-IN, AT THE SAME PLACE (the older program's routines): " ++
         toString older
     | .none_ h =>
       "STAND-IN (the older program's routines: the lot whose block stands here calls every " ++
         "step of the place still the older program's: " ++ h ++ ")"
     | .standIn =>
       if let some t := said.lookup x.1 then t
       else if bareFrame st x then
         "FRAME (a block without a round and without a step: the fold's own text)"
       else if x.2.1.kind == KindName.frame && x.2.2 == 0 then
         "STAND-IN (its step of today still runs inside a neighbouring place's stand-in)"
       else "STAND-IN (the older program's routines)")

/-- Words that stand beside every count of a lot's places or steps. `ok`: `FileDescription.readsOk` of the
description whose places or steps are counted, asked where the line is made. A block that states
fewer reads than its round draws positions would otherwise be counted unseen. -/
def readsWord (ok : Bool) : String :=
  if ok then "readsOk (Block.lean's), asked here of the description that is counted: true"
  else "NOT HELD: readsOk (Block.lean's), asked here of the description that is counted: FALSE"

/-- The counts of the places. -/
def countLine (reads : Bool) (w : Whose) (still : List String) (st : List StepsAt)
    (l : List (String × Place × Nat)) : String :=
  let kind := l.filter fun x => x.2.1.kind != KindName.frame
  let fr := l.filter fun x => x.2.1.kind == KindName.frame
  let bare := (fr.filter fun x => (w.lookup x.1).isNone && bareFrame st x).length
  let count := fun (ps : List (String × Place × Nat)) (p : Share → Bool) =>
    (ps.filter fun x => p (shareOf w still st x.1)).length
  let whole := fun (s : Share) => match s with | .whole _ => true | _ => false
  let half := fun (s : Share) => match s with | .half _ _ _ => true | _ => false
  let older := fun (s : Share) => match s with | .standIn => true | .none_ _ => true | _ => false
  s!"PLACES = {l.length} ; the fold's own (frame) = {fr.length} ; of a kind = {kind.length} ; " ++
    s!"FRAMES WITHOUT A STEP = {bare} ; OF THE PLACES OF A KIND: WHOLE A LOT's = " ++
    s!"{count kind whole} ; HALF = {count kind half} ; WHOLE A STAND-IN's = " ++
    s!"{count kind older} ; " ++
    s!"OF THE OTHER FRAMES: A LOT's = {count fr whole + count fr half} ; A STAND-IN's = " ++
    s!"{count fr older - bare} ; by = the lots' own words ; reads = {readsWord reads}"

/-- The steps that are counted as a lot's own. -/
def ownSteps (w : Whose) (still : List String) (st : List StepsAt)
    (l : List (String × Place × Nat)) : List String :=
  ((l.filter fun x => (w.lookup x.1).isSome).flatMap fun x => stepsOf st x.1).filter fun s =>
    !still.contains s

/-- The number of places that are a lot's in part. -/
def halfPlaces (w : Whose) (still : List String) (st : List StepsAt)
    (l : List (String × Place × Nat)) : Nat :=
  (l.filter fun x => match shareOf w still st x.1 with | .half _ _ _ => true | _ => false).length

/-- The counts of the steps. -/
def stepsLine (reads : Bool) (w : Whose) (still : List String) (st : List StepsAt)
    (l : List (String × Place × Nat)) : String :=
  let at_ := fun (p : String × Place × Nat → Bool) =>
    (l.filter p).flatMap fun x => stepsOf st x.1
  let all := at_ fun _ => true
  let own := ownSteps w still st l
  -- the same without the places of the kind `frame`
  let ownKind := ownSteps w still st (l.filter fun x => x.2.1.kind != KindName.frame)
  s!"STEPS-OF-TODAY = {all.length} ; " ++
    s!"at places of a kind = {(at_ fun x => x.2.1.kind != KindName.frame).length} ; " ++
    s!"at frames = {(at_ fun x => x.2.1.kind == KindName.frame).length} ; " ++
    s!"A LOT's OWN = {own.length} ; A LOT's OWN AT PLACES OF A KIND = {ownKind.length} ; " ++
    s!"reads = {readsWord reads} ; names = {own}"

/-- A line for each name of the table that stands at no place. Such a name is counted nowhere. -/
def strayLines (w : Whose) (l : List (String × Place × Nat)) : List String :=
  (w.filter fun y => !(l.any fun x => x.1 == y.1)).map fun y =>
    "IN THE TABLE AND AT NO PLACE = " ++ y.1 ++ " ; it counts nowhere"

/-- The lines of a list of places, then the counts. -/
def placeLines (reads : Bool) (w said : Whose) (still : List String) (st : List StepsAt)
    (l : List (String × Place × Nat)) : List String :=
  l.map (placeLine w said still st) ++ strayLines w l ++
    [countLine reads w still st l, stepsLine reads w still st l]

end ProofFile
