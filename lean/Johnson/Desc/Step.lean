-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Step.lean: one type for a step of a chain's decision, and the fold of a table of steps.
Definitions alone, all with code; nothing is proved here.

A file's decision is handed three views, one for each hash chain (`Fmt.View`, Fmt/View.lean): the
chain's rounds as a decision sees them, and the opened columns. Here a chain's decision is cut into
steps.

Main names.
  `OpenedColumn`: an opened column, as a view holds it: the tree's key, the leaf, the words. `Step S`: a
    step: from the state, THIS STRETCH's rounds, and the opened columns not yet taken, to the state
    and HOW MANY COLUMNS IT TOOK, or a refusal. A plain function on data: of the file it sees its
    own rounds and the columns not yet taken, and nothing else. `Row S`: a row of the table of
    stretches: the step's name, how many rounds it takes, the step.
  `stepAll`: the fold of a table: it cuts the rounds by `take`, drops the columns that a step says
    it took, threads the state, and names the row that refused.
  `chainEnd`: a chain's decision with its last state: the state, if the table is not empty, no row
    refuses, no round and no column is left over, and the last test `fin` says yes of the state;
    else the reason in words. It hands the state out, so that a later chain's first state can be
    made of it.
  `chainRun`: is `chainEnd` a state. `chainSay`: "yes", or "no: " and the reason.

The plan and the public part of a request are parameters of whoever makes a table, not of a step.

Limits: no step and no table of the protocol is here; nothing says that a table's steps test what
the protocol asks. BY THE FOLD each round goes to just one row, each column is TAKEN by just one
step, in order, and none is left over. A step is handed all the columns that are not yet taken: IT
CAN READ A COLUMN AND NOT TAKE IT, so that a later step reads it again: that a step takes what it
rests on is not asked. Nor that it reads what it takes: a step can take columns unread. The last
test `fin` is the caller's: at `fun _ => true` what a table still carries in its state is forgiven.
A step that folds from the right over its own stretch can still exhaust the evaluator's stack: the
fold does not shield it. Controls: Johnson/Desc/StepToy.lean.
Terms: lean/GLOSSARY.md.

-/
import Fmt.View

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

/-- An opened column, as a view holds it: the tree's key, the leaf, the words. -/
abbrev OpenedColumn : Type := Nat × Nat × List UInt64

/-- A step of a chain's decision: from the state, this stretch's rounds and the opened columns not
yet taken: `some` of the state and the number of columns that it took (the first so many of those
handed to it), or `none`: a refusal. -/
abbrev Step (S : Type) : Type := S → List Fmt.RoundView → List OpenedColumn → Option (S × Nat)

/-- A row of the table of stretches. -/
structure Row (S : Type) where
  /-- the step's name, for a refusal's words -/
  name : String
  /-- how many rounds the step takes -/
  take : Nat
  step : Step S

/-- The fold of a table of steps. At the table's end: `.ok` of the state, the rounds left and the
columns left. Where fewer rounds are left than a row takes: `.error` of the row's name and ": the
stretch is short". Where a row's step refuses: `.error` of the row's name. Where it says that it
took more columns than are left: `.error` of the row's name and ": it took more columns than are
left". -/
def stepAll {S : Type} : List (Row S) → S → List Fmt.RoundView → List OpenedColumn →
    Except String (S × List Fmt.RoundView × List OpenedColumn)
  | [], s, rs, cols => .ok (s, rs, cols)
  | r :: l, s, rs, cols =>
    let (mine, rest) := rs.splitAt r.take
    if mine.length ≠ r.take then .error (r.name ++ ": the stretch is short") else
    match r.step s mine cols with
    | none => .error r.name
    | some (s', k) =>
      if k ≠ 0 && (cols.drop (k - 1)).isEmpty then
        .error (r.name ++ ": it took more columns than are left") else
      stepAll l s' rest (cols.drop k)

/-- A chain's decision with its last state. `.error` with the reason in words: at an empty table;
where `stepAll` refuses; where a round or a column is left over; where `fin` says no of the last
state. Else `.ok` of the last state. -/
def chainEnd {S : Type} (tbl : List (Row S)) (s₀ : S) (fin : S → Bool) (v : Fmt.View) :
    Except String S :=
  if tbl.isEmpty then .error "the table of stretches is empty" else
  match stepAll tbl s₀ v.rounds v.opened with
  | .ok (s, [], []) => if fin s then .ok s else .error "the last state fails the last test"
  | .ok (_, rs, cols) => .error s!"left over: {rs.length} rounds, {cols.length} columns"
  | .error n => .error ("refused at " ++ n)

/-- A chain's decision: true where `chainEnd` gives a state, false where it gives a reason. The
state is dropped. -/
def chainRun {S : Type} (tbl : List (Row S)) (s₀ : S) (fin : S → Bool) (v : Fmt.View) : Bool :=
  match chainEnd tbl s₀ fin v with
  | .ok _ => true
  | .error _ => false

/-- The same in words: "yes" where `chainEnd` gives a state; else "no: " and its reason. -/
def chainSay {S : Type} (tbl : List (Row S)) (s₀ : S) (fin : S → Bool) (v : Fmt.View) : String :=
  match chainEnd tbl s₀ fin v with
  | .ok _ => "yes"
  | .error e => "no: " ++ e

end VerifiableInference.Desc
