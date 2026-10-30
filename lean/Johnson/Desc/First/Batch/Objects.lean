-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Objects.lean: DEFINITIONS WITH CODE; NO THEOREM: ONE STEP OF ADDING, WHOLE,
AS A BLOCK WITHOUT A ROUND: THE SMALLNESS TEST's CLAIMS ARE MADE AND ADDED.

Where it stands. Behind the batching draw a segment's claims are added to one equation, group by
group. This step adds the group of the smallness test: the claims of the lookup on the digits; the
claim on that lookup's key vectors and the three on its planes; a tie for each matrix; the reads.
WHOSE TEXT IS WHAT. The claims are OTHER KINDS' NAMED RUNS: a parameter: a list of runs, called in
the list's order, each handed the number of claims gathered so far IN THIS CALL. K9's own: the
gathering (`gather`), the adding (`K9.adds`, Johnson/Desc/First/Batch/Kind.lean, by name), and the
order: the sort's own counts in front (a parameter, each under one name) · the runs · the adding ·
what is read off the ledger behind the adding (a parameter).

Main names:
  `gather ws cut runs t`: the runs' claims in a row, each run's held against the windows, and the
    state behind the last run.
  `runsBy states cut`: a stretch of the driver's table of the order as a list of runs, by name.
  `addsStep X p what counts ws cut runs behind`: **the step as a block.**

AGAINST THE PROGRAM `verify-on-bytes` (OnBytes/Model/Tail.lean: objectsF, called at Layer.lean:622 ·
Attention.lean:230 · Head.lean:257): that routine makes a claim and adds it at once; here all claims
of the step are made first and then added, in the same order: so a run that wants a claim's number
reckons it of the ledger's count and the number that it is handed.
THE CONDITION UNDER WHICH "MADE FIRST, THEN ADDED" EQUALS THAT ROUTINE's "MADE AND ADDED": an adding
writes four things of the ledger: the sums (on the slots; the constant) · the rows' weights · the
marks of the weights handed out · the count of claims. NO RUN READS THE FIRST THREE, AND EVERY RUN
THAT READS THE COUNT TAKES THE COUNT PLUS THE NUMBER GATHERED. Whoever reads the sums stands in
`behind`. It is a condition on the runs that it is given: nothing here asks it; it is held by runs
(the ledger whole, by value), not by a reading of the runs' texts.

Limits: no round, no view, no column. No law is stated. Nothing on soundness.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Batch.Kind
import Johnson.Desc.First.Batch.Tests
import Johnson.Desc.First.Batch.Window

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model

variable {T Cl : Type}

/-- A named run of claims: from the number gathered so far and the state. -/
abbrev RunOf (T : Type) : Type := String × (Nat → T → Except String (List Claim × T))

/-- The runs' claims in a row. ws: the windows of slots that some runs state as their own, read off
the state in front of a run: behind each run its claims are held against them (`windowsOk`,
Johnson/Desc/First/Batch/Window.lean, by name: "K9.window"). cut: the stretch of the order that
these runs are: a run is known to a window by its block's number there and its name; a run that the
stretch does not name is nobody's owner (block 0 states no run). A refusal bears the run's name in
front. -/
def gather (ws : T → List Window) (cut : List (Nat × String)) (runs : List (RunOf T)) (t : T) :
    Except String (List Claim × T) :=
  runs.foldlM (fun (x : List Claim × T) r =>
    let who := (cut.find? fun o => o.2 == r.1).getD (0, r.1)
    match (r.2 x.1.length x.2).bind fun y => (windowsOk (ws x.2) who y.1).map fun _ => y with
    | .ok y => .ok (x.1 ++ y.1, y.2)
    | .error e => .error (r.1 ++ ": " ++ e)) ([], t)

/-- **The runs of a stretch of the order.** cut: entries (a block's number in its segment, from 0 ·
the name of one of its runs): a stretch of the one table of the protocol's order (the driver's
`First.orderCuts`). states b: what block number b states. Each entry is looked up BY NAME; nothing
where a name lacks. -/
def runsBy (states : Nat → List (RunOf T)) (cut : List (Nat × String)) : Option (List (RunOf T)) :=
  cut.mapM fun o => (states o.1).find? fun r => r.1 == o.2

/-- A run laid right behind the first run of that name; nothing where the name lacks. -/
def behindRun (name : String) (x : RunOf T) : List (RunOf T) → Option (List (RunOf T))
  | [] => none
  | r :: l => if r.1 == name then some (r :: x :: l) else (behindRun name x l).map (r :: ·)

/-- **A step of adding.** counts: the sort's own tests in front. ws: the windows. cut: the stretch
of the order. runs: the kinds' runs. behind: what is read off the ledger behind the adding. -/
def addsStep (X : Lens T) (p : Where) (what : String) (counts : List (String × (T → Bool)))
    (ws : T → List Window) (cut : List (Nat × String)) (runs : List (RunOf T))
    (behind : T → Except String T) : Block T Cl :=
  let a : Block T Cl := adds X p p.piece what (gather ws cut runs)
  { a with
    decide := fun t rs gs => do
      countsHold counts t
      let t₁ ← a.decide t rs gs
      behind t₁ }

end VerifiableInference.Desc.K9
