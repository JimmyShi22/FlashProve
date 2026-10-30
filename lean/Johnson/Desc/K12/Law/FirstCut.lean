-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/FirstCut.lean: a test on the plan alone: the first switch's cut of the declared
rounds of the proximity test (the kind K12) is two rounds, of which the first opens nothing and
neither reads a stored table.

Definitions with code alone and no theorem, so that the test can be compiled and run.
first_half_of_step (Johnson/Desc/K12/Law/StepGroups.lean) asks just this of the cut.
Main names:
  `cutAt`: the frame's own cut: the place's declared rounds, zipped with its oracle messages; drop
    1; drop (1 + k); take 2.
  `cutL`, `cutOk`, `cutNo`: the clauses, named: two; seed.stored; seed.opens; cs.stored; cs.range
    (the second round's declared range is the stage's); cs.draws (it draws a position).
  `labelsL`, `labelsOk`: one clause more, on the record: opens.tree: the declared openings carry, in
    turn, the numbers of the book's trees, uncut (where firstTree is above them all keys are 0).
    The labels tell two trees apart only where their numbers differ: at the full size's last chain
    two of the three opened trees bear the number 1, and there `gpL`'s clauses opens.a and opens.W,
    on depth and width, part them. No clause of `gpL` or `labelsL` reads the source of a declared
    opening (the chain's own tree, or taken over from which chain): two trees of one number, depth
    and width would not be told apart.
  `cutLines`: the lines that a run prints: cutOk at the stage's own k, with two controls, each due
    false (the cut one round later; the cut one round earlier); labelsOk at the record behind the
    batching, with one control (member 0's tree has another number).
Limits: Evaluated is not proved. No soundness is claimed, and nothing is said on hiding.
The clause cs.draws is spent by no theorem. The clauses seed.stored and cs.stored are theorems
(roundsOfNums_stored, Johnson/Desc/K12/Law/StepAt.lean), so they are idle.

-/
import Johnson.Desc.K12.Law.FirstOk

set_option autoImplicit false
namespace H2K.First
open VerifiableInference.Desc VerifiableInference.Desc.K12

def cutAt (p : P12) (k : Nat) : List Fmt.DeclaredRound :=
  ((((((H2U.roundsOfNums p.nums).getD []).zip p.oracles).drop 1).drop (1 + k)).take 2).map (·.1)

def cutL (p : P12) (a : Fmt.M1.Stage) (k : Nat) : Clauses :=
  match cutAt p k with
  | [dS, dC] =>
    [("two", true), ("seed.stored", dS.stored.isEmpty), ("seed.opens", dS.opens.isEmpty),
     ("cs.stored", dC.stored.isEmpty), ("cs.range", dC.entry.logN == a.C.a),
     ("cs.draws", decide (0 < dC.entry.poss))]
  | _ => [("two", false)]

def cutOk (p : P12) : Bool :=
  match p.nums.stages with
  | a :: _ => ok (cutL p a a.k)
  | [] => false

def cutNo (p : P12) (a : Fmt.M1.Stage) (k : Nat) : List String := ((cutL p a k).filter (!·.2)).map
    (·.1)

def numAt (book : OnBytes.TreeBook) (t : Nat) : Nat := ((book.trees[t]?).map (·.number)).getD 0

def labelsL (p : P12) (t : T12) : Clauses :=
  match p.nums.stages, t.pass with
  | a :: _, .claim _ L =>
    match gpOf p t a L with
    | some D => [("opens.tree", D.opens.map (·.1.tree) == D.ts.map (numAt D.book))]
    | none => [("the plain data cannot be made", false)]
  | _, _ => [("no stage, or no claim passes", false)]

def labelsOk (p : P12) (t : T12) : Bool := ok (labelsL p t)

def cutLines (tagS : String) (p : P12) (tG : T12) : List String :=
  let m0 : Nat := match tG.pass with
    | .claim _ L => ((tG.book.place[L.members.getD 0 0]?).map (·.1)).getD 0
    | _ => 0
  let spoiled : T12 := { tG with book := { tG.book with
    trees := tG.book.trees.modify m0 fun T => { T with number := T.number + 1 } } }
  let labels : List Nat := match p.nums.stages with
    | a :: _ => (opensOf p a.k).map (·.1.tree)
    | [] => []
  [s!"{tagS}.LABELS\tlabelsOk {labelsOk p tG}\tdeclared labels {labels}",
   s!"{tagS}.LABELS.control\tmember 0's tree has another number\t{labelsOk p spoiled}"] ++
  match p.nums.stages with
  | a :: _ =>
    [s!"{tagS}.CUT\tcutOk {cutOk p}\trefusing: {cutNo p a a.k}\tthe two rounds: {(cutAt p a.k).map
        fun d => (d.entry.name, d.stored.length, d.opens.length, d.entry.logN, d.entry.poss)}",
     s!"{tagS}.CUT.control\tthe cut one round later\t{ok (cutL p a (a.k + 1))}\trefusing: {cutNo p a
         (a.k + 1)}",
     s!"{tagS}.CUT.control\tthe cut one round earlier\t{ok (cutL p a (a.k - 1))}\trefusing: {cutNo p
         a (a.k - 1)}"]
  | [] => [s!"{tagS}.CUT\tno stage"]

end H2K.First
