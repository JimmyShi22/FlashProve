-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Add.lean (kind K9): DEFINITIONS WITH CODE; NO THEOREM: HOW THE BATCHING
ADDS A CLAIM TO THE ONE EQUATION, IN THE KIND's OWN WORDS. Every test bears a name; no function of
the program `verify-on-bytes` that can refuse is called.

The sums are kept in the plain record Fork: the weights on the entries of the arrays' virtual rows
(trees), the coefficients on the slots (LS), the constant (c0); with them chi (theta), the number of
claims added (nClaim), the plan's number of claims (planClaimsF) and a mark for each number that has
been handed out (kapMapF).
THE WEIGHT. Claim number c gets chi^c. A tie or a read of the smallness test takes a number like any
claim, but its weight is chi^(n + first): n the plan's number of claims, first the number of its
first equation (Johnson/Desc/Claim.lean).

Main names:
  weightNext F   the next number's weight chi^c, and the record with the number marked and counted.
                 "K9.equation-open": the one equation has not been made yet. "K9.chi-drawn".
                 "K9.number-free": c is below the plan's number, there is one mark for each number
                 of the plan, and c's is not set.
  addForm F w a  w times the form a. "K9.entry-there": the arrays have the entry that the form
                 names. "K9.slot-there": the slot is below the number of slots.
  addRuns F w rs w times each run. "K9.run-fits": the arrays have the row; the run lies inside the
                 row's columns, and its weights inside the vector that it names.
  addOne F cl    the claim under its weight. addList: a list of claims, in order.

AGAINST `verify-on-bytes` (OnBytes/Model/Hide.lean: Fork.kap, Fork.push; OnBytes/Model/Trees.lean:
Fork.pushRuns; called one after the other by t2Lin, and by Johnson/Desc/Claim.lean's addClaim): the
same tests and the same sums, but for one thing: WHILE THERE ARE NO MARKS AT ALL its Fork.kap
hands out chi^c for any c; here a number without a mark is refused. The batching draw sets up the
marks, and the plan's number is not 0 there. HOW THAT IS KNOWN: by reading, and on a made-up record
(Johnson/Desc/First/Batch/AddToys.lean [not in this library; so here read: not tested in this
library]); a theorem of agreement is another file's. runLoop, the loop that adds a run's weights to
a row, cannot refuse and is called by name.
THE ARRAYS ARE TAKEN OUT OF THE RECORD WHILE THEY ARE CHANGED, and what is read of the record is
read in front, so that the compiled program changes them in place.

-/
import Johnson.Desc.Claim
import Johnson.Desc.First.Batch.Text

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model

/-- The next number's weight; the record with that number marked and counted. -/
def weightNext (F : Fork) : Ans (E × Fork) := do
  need "K9.equation-open" !F.doorShutF
  need "K9.chi-drawn" F.thetaDrawnF
  need "K9.number-free" (decide (F.nClaim < F.planClaimsF) && F.kapMapF.size == F.planClaimsF &&
    !F.kapMapF.getD F.nClaim true)
  let c := F.nClaim
  let k := powE F.theta c
  pure (k, { F with kapMapF := F.kapMapF.set! c true, nClaim := c + 1 })

/-- The arrays have the entry that x names, inside the columns that the row's weights hold. -/
def entryThere (trees : Array HTree) (x : Ent) : Bool :=
  match trees[x.tree]? with
  | none => false
  | some X =>
    match X.rows[x.row]? with
    | none => false
    | some r => decide (r.L0 ≤ x.idx) && decide (x.idx - r.L0 < r.L.size)

/-- w times x's coefficient, added to the weight on the entry that x names. -/
def addEntry (w : E) (trees : Array HTree) (x : Ent) : Ans (Array HTree) := do
  need "K9.entry-there" (entryThere trees x)
  pure (trees.modify x.tree fun X =>
    { X with rows := X.rows.modify x.row fun r =>
      { r with L := r.L.modify (x.idx - r.L0) fun v => addE v (mulE w x.coef) } })

/-- w times the coefficient x.2, added to the coefficient on slot x.1. ns: the number of slots. -/
def addSlot (w : E) (ns : Nat) (LS : Array E) (x : Nat × E) : Ans (Array E) := do
  need "K9.slot-there" (decide (x.1 < ns))
  pure (LS.modify x.1 fun v => addE v (mulE w x.2))

/-- w times the form a, added to the sums. -/
def addForm (F : Fork) (w : E) (a : Aff) : Ans Fork := do
  let ns := F.ns
  let trees := F.trees
  let LS := F.LS
  let G := { F with trees := #[], LS := #[] }
  let trees' ← a.ents.foldlM (addEntry w) trees
  let LS' ← a.slots.foldlM (addSlot w ns) LS
  pure { G with trees := trees', LS := LS', c0 := addE G.c0 (mulE w a.const) }

/-- The arrays have the virtual row that r names; the run lies inside the columns that the row's
weights hold; the run's weights lie inside r.w. -/
def runFitsRow (trees : Array HTree) (r : Run2) : Bool :=
  match trees[r.tree]? with
  | none => false
  | some X =>
    match X.rows[r.row]? with
    | none => false
    | some R =>
      decide (r.w0 ≤ r.w.size) && decide (r.n ≤ r.w.size - r.w0) && decide (R.L0 ≤ r.first) &&
        decide (r.first - R.L0 ≤ R.L.size) && decide (r.n ≤ R.L.size - (r.first - R.L0))

/-- w times the run r, added to the weights on the row that r names. -/
def addRun (w : E) (trees : Array HTree) (r : Run2) : Ans (Array HTree) := do
  need "K9.run-fits" (runFitsRow trees r)
  pure (trees.modify r.tree fun X =>
    { X with rows := X.rows.modify r.row fun R =>
      { R with L := runLoop (mulE w r.coef) r.w r.w0 (r.first - R.L0) r.n 0 R.L } })

/-- w times each of the runs, added to the sums. -/
def addRuns (F : Fork) (w : E) (runs : Array Run2) : Ans Fork := do
  let trees := F.trees
  let G := { F with trees := #[] }
  let trees' ← runs.foldlM (addRun w) trees
  pure { G with trees := trees' }

/-- **The record with the claim added under its weight.** The claim takes the next number. -/
def addOne (F : Fork) (cl : Claim) : Ans Fork := do
  let other := cl.eqFirst.map fun first => powE F.theta (F.planClaimsF + first)
  let x ← weightNext F
  let w := other.getD x.1
  let G ← addForm x.2 w cl.form
  addRuns G w cl.runs

/-- **A list of claims, in order.** -/
def addList (F : Fork) (cls : List Claim) : Ans Fork := cls.foldlM addOne F

end VerifiableInference.Desc.K9
