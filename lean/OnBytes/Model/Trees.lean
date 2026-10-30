-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/Trees.lean: the committed arrays of a sub-proof, and the one equation that it hands
to the request's chain.

A sub-proof runs as one link of a request's chain. Commitments, samples, positions and proximity
tests belong to the chain (OnBytes/Model/ReqChain.lean). The sub-proof keeps a list of its arrays,
adds up its linear claims as weights on these arrays (OnBytes/Model/Hide.lean), and at its end
hands the chain one equation. This file follows verifier/src/vf_subproof_segment.h of the C++
verifier, routine by routine, as far as a run of the verifier uses it.

   N2, Tail2                   what the list keeps of each array; the list
   t2AddN, t2AddP, t2Plan      make the list, before any of the proof is read
   LinkCtx, LinkM              the link in which a sub-proof runs; the type of its routines
   rootInH                     the chain receives the link's next commitment
   t2Batch                     the element whose powers are the weights of the claims
   Run2, t2Lin                 a claim on long runs of an array's entries
   rowWeights, doorH           the one equation goes to the chain, and the link is closed

Terms and names. A moment is one commitment of a link. The shape says which oracle messages each
link sends and at which moment, the layout which arrays they hold (OnBytes/Model/ReqChain.lean). ns
is the number of a sub-proof's slots. Slot, mask row, claim, virtual row, Fork (the state of one
sub-proof's check), kap (the weight of a claim), LS and c0 are explained in OnBytes/Model/Hide.lean;
dry run, view, oracle message and group in OnBytes/Iop/Ground.lean; smallness test, cell and symbol
at t2AddP. In names, tree means a committed array. The names t2.., N2, Tail2, Run2, LinkCtx, rootInH
and doorH are those of the C++ file.

The docstring of doorH writes the equation out. That of Trees.names says how a failure gets its name
and which three conditions only this file has, that of Tail2 what only the C++ file has.

What this file does not claim. No theorem is stated here; OnBytes/Model/TreesLaws.lean states what
pushRun and t2Lin add to the one equation.
-/
import OnBytes.Model.Hide
import OnBytes.Model.FormF
import OnBytes.Model.ReqChain

namespace OnBytes.Model

/-- The names that this file passes to a refusal. They are the C++ verifier's own names
(vf_rejection_names.txt), kept so that the two programs can be compared. A name that begins with
internal marks a test of the program on itself. OnBytes/Model/StagesNames.lean gathers these lists.
Two steps of this file fail under another name, and their docstrings give the C++ name: LinkM.call
(chain-refused) and Fork.pushRuns (internal-L-row, internal-L-index). The draw in t2Batch
(SubM.batchOpen) and the count in doorH (SubM.batchRows) fail under refused or under the channel's
names plan and view-shape (planName, shapeName, OnBytes/Iop/Ground.lean); where a round's name or
its number of rows is not the plan's, the C++ channel ends the process (BLK_REQUIRE, blocks/base.h).
For Fork.batchBy, kapTake, push, kapAllTakenF and settle, which are called here,
OnBytes/Model/Hide.lean gives the C++ names.

The functions that make the list of arrays (t2AddN, t2AddP, t2Plan) read no proof. Where the C++
verifier refuses, they return its name for the refusal. The routines that run on a proof are written
in SubM and LinkM. A condition written with mustAs or testAs fails under the C++ name, and the
failure carries that name out of the run (OnBytes/Model/Frame.lean). A condition written with must,
and a step on the state that returns none, fail under the general name refused (unnamed,
OnBytes/Iop/Ground.lean). A call of the chain (LinkM.call) fails under the name that the called
block gives. Names are given without the sub-proof's prefix, which the C++ puts before most of them,
and without the array's name, which it appends to internal-coef. Three conditions of this file have
no line in the C++ file and therefore no name of their own; they are written with must: the link's
number in LinkM.call, and in doorH that the list of arrays is not longer than Fork.trees and that
each array has the size that the layout gives it. -/
def Trees.names : List String :=
  ["internal-coef", "internal-f-door", "internal-f-draws", "internal-row-form",
    "internal-slot-count", "internal-t2-order", "plan-link", "plan-w-zero"]

/-! ## The list of a sub-proof's arrays -/

/-- What the list records about an array besides its HTree. -/
structure N2 where
  /-- 1 for an array over the base field, 3 for one over the extension field -/
  ec : Nat := 1
  /-- 1 + the number of sub-proofs that read the array besides its owner -/
  a : Nat := 1
  /-- an earlier sub-proof, the owner, has committed to the array -/
  foreign : Bool := false
  /-- the shape, if this is the symbol array of a matrix of the smallness test -/
  p : Option ShP := none
  deriving DecidableEq, Repr, Inhabited

/-- True if a reader's list and the owner's list agree on an array: rows, columns, ec, a and p. Both
lists are made from public numbers, so a mismatch is a fault in the plans, not in a proof. -/
def t2SameShape (a : N2) (A : HTree) (b : N2) (B : HTree) : Bool :=
  A.R == B.R && A.K == B.K && a.ec == b.ec && a.a == b.a && a.p == b.p

/-- The list of a sub-proof's arrays, with flags that enforce part of the order of the calls.

Some parts of the C++ file (vf_subproof_segment.h) have no counterpart in this file: what serves
only tests (a prover's coefficient vectors and values, read from files or handed in), what serves
only the log (counts of terms and weights, times), a mark on an array that no routine sets, tests
that a pointer is not null, and the handling of a failed allocation in t2FillL. The stepper for
equality weights, EqRun, has its counterpart of that name in OnBytes/Model/FormF.lean. -/
structure Tail2 where
  /-- true once HTailF2.addTreesF has begun the list; t2AddN, t2AddP, t2Plan, t2Batch and doorH
  require it -/
  link : Bool := false
  /-- one record for each array, in the order of Fork.trees -/
  nt : Array N2 := #[]
  /-- the number of slots that the sub-proof's messages have taken (set by t2Batch) -/
  used : Nat := 0
  /-- the list is closed -/
  planned : Bool := false
  /-- doorH has run -/
  walked : Bool := false
  deriving Inhabited

/-- True while arrays can be added to the list. -/
def t2Open (F : Fork) (T : Tail2) : Bool := T.link && !T.planned && F.trees.size == T.nt.size

/-- Adds an array of R rows and K columns with nv virtual rows. Returns the array's number. The
sub-proof's check sets the row weights (coef) of the virtual rows later. Their column weights (L)
are not allocated here: a plan needs no memory for them. Fork.fillL or, at the latest, t2FillL in
t2Batch allocates them. ec, a, foreign: as in N2. For an array to which an earlier sub-proof has
committed, the caller passes the a of the owner's list. -/
def t2AddN (F : Fork) (T : Tail2) (name : String) (R K ec a : Nat) (foreign : Bool) (nv : Nat) :
    Except String (Nat × Fork × Tail2) :=
  if !t2Open F T then .error "internal-t2-order"
  else
    let X : HTree :=
      { name := name, kind := .table, R := R, K := K, owner := !foreign,
        rows := Array.replicate nv ({} : HRow) }
    .ok (F.trees.size, { F with trees := F.trees.push X },
      { T with nt := T.nt.push { ec := ec, a := a, foreign := foreign } })

/-- Adds the symbol array of one matrix of the smallness test, with m rows of cells and k columns.
The smallness test is the last part of every sub-proof (OnBytes/Model/Tail.lean). A cell is an entry
of one of its integer matrices; three cells of a column are packed into one field element, a symbol
(OnBytes/Model/FormF.lean). The array has ceil(m / 3) rows, k columns and one virtual row, for the
matrix's tie (HTailF2.coefficientsF, OnBytes/Model/Tail.lean, sets its row weights). Returns the
array's number. w is the number that TMat.wp holds. No line of the parameter file sets it, so it is
0; another value is refused. -/
def t2AddP (F : Fork) (T : Tail2) (name : String) (m k w a : Nat) (foreign : Bool) :
    Except String (Nat × Fork × Tail2) :=
  if !t2Open F T then .error "internal-t2-order"
  else if w != 0 then .error "plan-w-zero"
  else
    let q := ShP.of m k a
    let X : HTree :=
      { name := name, kind := .symbols, R := q.Rr, K := q.Kc, owner := !foreign,
        rows := Array.replicate 1 ({} : HRow) }
    .ok (F.trees.size, { F with trees := F.trees.push X },
      { T with nt := T.nt.push { ec := 1, a := a, foreign := foreign, p := some q } })

/-- Closes the list: no array is added after this call. -/
def t2Plan (F : Fork) (T : Tail2) : Except String Tail2 :=
  if !t2Open F T then .error "internal-t2-order" else .ok { T with planned := true }

/-- Gives every virtual row of every listed array its K column weights, all 0. A row whose L has K
entries already (Fork.fillL) stays as it is. In a sub-proof's check Fork.lin and t2Lin can have
added no claim before: each takes a power of the batching element, and t2Batch draws that element
only after it has called t2FillL. -/
def t2FillL (F : Fork) (T : Tail2) : Fork :=
  let fill (X : HTree) : HTree :=
    { X with rows := X.rows.map fun r =>
        if r.L.size != X.K then { r with L := Array.replicate X.K zeroE } else r }
  let trees := (List.range T.nt.size).foldl (fun trees ti => trees.modify ti fill) F.trees
  { F with trees := trees }

/-! ## The link in which a sub-proof runs -/

/-- The link of the request's chain in which a sub-proof runs. runLinkH
(OnBytes/Model/StagesLinks.lean), which runs one link for runLinksH, the routine that drives the
links, makes it. The fields link, arrayOf and list are public. The field check holds the request's
shape and layout. Against them this file tests: the link's number (LinkM.call), that the arrays
committed to at a moment are the layout's arrays of that moment (rootInH), that all moments of the
link have passed (t2Batch), and the size of each listed array (doorH). The rest is the driving
routine's task. Whoever makes check (ChainCheck.start) must take shape and layout from the bytes
that the chain's reader has hashed. -/
structure LinkCtx where
  /-- the state of the calls over the request's links; the present link is this sub-proof's -/
  check : ChainCheck
  /-- the link's number, counted from 0 -/
  link : Nat := 0
  /-- for each array of the list: the link that committed to it, this one or an earlier one, and
  the array's name in that link's layout -/
  arrayOf : Array (Nat × String) := #[]
  /-- the sub-proof's list of arrays -/
  list : Tail2 := {}
  /-- the number of the link's moments so far; the first has passed when the sub-proof's routine
  starts -/
  moments : Nat := 1
  /-- t2Batch has run: the sub-proof's last challenge is drawn -/
  handed : Bool := false
  /-- the link is closed -/
  done : Bool := false

/-- A routine of a sub-proof that also calls the chain. LinkM.sub lifts a routine of SubM. get, set
and modify in this file act on LinkCtx, never on the context of Blk. -/
abbrev LinkM : Type → Type := StateT LinkCtx SubM

namespace LinkM

/-- A routine of the sub-proof's engine, used inside a link. -/
def sub {α : Type} (x : SubM α) : LinkM α := fun L => do
  let a ← x
  pure (a, L)

/-- A public condition: fails unless b is true, in the dry run and on a view. -/
def must (b : Bool) : LinkM Unit := sub (SubM.must b)

/-- A public condition, with the name under which the C++ verifier refuses at this place. -/
def mustAs (name : String) (b : Bool) : LinkM Unit := sub (liftM (Model.mustAs name b))

/-- A condition on values, with the name under which the C++ verifier refuses at this place. -/
def testAs (name : String) (b : Bool) : LinkM Unit := sub (liftM (Model.testAs name b))

/-- The state of the sub-proof's engine. -/
def fork : LinkM Fork := sub (SubM.ask fun F => some F)

/-- A call of ChainCheck: it fails if that call fails, and keeps the new state. The C++ verifier
refuses there under the name chain-refused. The link's number must be that of the present link of
check. -/
def call (f : ChainCheck → Blk ChainCheck) : LinkM Unit := fun L => do
  SubM.must (L.link == L.check.link)
  let check ← (liftM (f L.check) : SubM ChainCheck)
  pure ((), { L with check := check })

end LinkM

/-- Called where the sub-proof's prover commits to further arrays. The chain receives the roots of
the link's next moment, with their samples (ChainCheck.later). trees: the numbers of the arrays that
are committed to here. They must be exactly the arrays that the layout puts at that moment.
Otherwise a challenge that should follow an array's commitment could be drawn before it. -/
def rootInH (trees : List Nat) : LinkM Unit := do
  let L ← get
  LinkM.mustAs "plan-link" (!L.handed && !L.done)
  let moment := L.moments
  LinkM.call ChainCheck.later
  modify fun L => { L with moments := L.moments + 1 }
  let laidHere : List (String × Nat) :=
    (L.check.arraysOf L.link).filter fun a => L.check.momentOfMessage L.link a.2 == some moment
  for t in trees do
    let F ← LinkM.fork
    let committed := ((F.trees[t]?).map (·.root.isSome)).getD true
    let here : Bool :=
      match L.arrayOf[t]? with
      | some (born, name) => born == L.link && laidHere.any fun a => a.1 == name
      | none => false
    LinkM.mustAs "plan-link" (!committed && here)
    -- The chain keeps the root. The mark only records that the array is committed.
    LinkM.sub (SubM.rootTaken t 0)
  LinkM.mustAs "plan-link" (trees.length == laidHere.length)

/-- Draws the element whose powers are the weights of the sub-proof's linear claims. The caller must
call it after the sub-proof's last message. Tested here: the list is closed, all moments of the link
have passed, this routine has not run before, and used = ns. It is meant to be the sub-proof's last
draw. The channel enforces that only where the plan's entry of this draw's round counts rows: it
then closes no further round until SubM.batchRows has been called, which doorH does. used: the
number of slots that the messages have taken, as the caller gives it (it is not compared with
Fork.next); it must be all that the sub-proof has. The number of claims in the plan,
Fork.planClaimsF, must have been set before this call: 0 is refused. -/
def t2Batch (used : Nat) : LinkM Unit := do
  let L ← get
  let (ns, planClaims) ← LinkM.sub (SubM.ask fun F => some (F.ns, F.planClaimsF))
  LinkM.mustAs "internal-slot-count" (L.list.planned && used == ns)
  LinkM.mustAs "plan-link"
    (L.list.link && !L.handed && L.moments == L.check.momentsOf L.link)
  LinkM.sub (SubM.change fun F => some (t2FillL F L.list))
  let drawn ← LinkM.sub SubM.batchOpen
  LinkM.sub (SubM.batchBy drawn)
  LinkM.mustAs "internal-f-draws" (planClaims != 0)
  LinkM.sub (SubM.change fun F =>
    some { F with kapMapF := Array.replicate F.planClaimsF false })
  set { L with list := { L.list with used := used }, handed := true }

/-! ## A claim on long runs of entries -/

/-- One run of a claim: coef * w[w0 + i] on entry first + i of a virtual row, for i below n. -/
structure Run2 where
  /-- the array's number in the list -/
  tree : Nat := 0
  /-- the virtual row's number among the array's -/
  row : Nat := 0
  /-- the first entry of the run -/
  first : Nat := 0
  /-- the factor of the whole run -/
  coef : E := oneE
  /-- the vector that holds the run's weights -/
  w : Array E := #[]
  /-- the run's first weight in w -/
  w0 : Nat := 0
  /-- the length of the run -/
  n : Nat := 0
  deriving Inhabited

/-- True if the arrays have the virtual row that r names, the run lies inside the columns that the
row's L holds, and the run's weights lie inside r.w. -/
def runFits (trees : Array HTree) (r : Run2) : Bool :=
  match trees[r.tree]? with
  | none => false
  | some X =>
    match X.rows[r.row]? with
    | none => false
    | some R =>
      decide (r.w0 ≤ r.w.size) && decide (r.n ≤ r.w.size - r.w0) && decide (R.L0 ≤ r.first) &&
        decide (r.first - R.L0 ≤ R.L.size) && decide (r.n ≤ R.L.size - (r.first - R.L0))

/-- Adds kc * w[w0 + j] to L[first + j] for j = i, .., i + count - 1. -/
def runLoop (kc : E) (w : Array E) (w0 first : Nat) : (count i : Nat) → Array E → Array E
  | 0, _, L => L
  | count + 1, i, L =>
    let x := w.getD (w0 + i) zeroE
    runLoop kc w w0 first count (i + 1)
      (if isZeroE x then L else L.modify (first + i) fun v => addE v (mulE kc x))

/-- Adds k times the run r to the column weights of the virtual row that r names. -/
def pushRun (k : E) (trees : Array HTree) (r : Run2) : Option (Array HTree) :=
  if runFits trees r then
    some (trees.modify r.tree fun X =>
      { X with rows := X.rows.modify r.row fun R =>
        { R with L := runLoop (mulE k r.coef) r.w r.w0 (r.first - R.L0) r.n 0 R.L } })
  else none

/-- Adds k times each of the runs to the one equation. Returns none if a run does not fit; the
C++ verifier refuses there under internal-L-row or internal-L-index. The arrays are taken out of the
state while they are changed, so that the compiled program changes them in place. -/
def Fork.pushRuns (F : Fork) (k : E) (runs : Array Run2) : Option Fork :=
  let trees := F.trees
  let G := { F with trees := #[] }
  (runs.foldlM (pushRun k) trees).map fun trees' => { G with trees := trees' }

/-- Adds one claim: the form a plus the runs is 0. The whole claim has one weight. -/
def t2Lin (a : Aff) (runs : Array Run2) : SubM Unit := do
  let k ← SubM.kap
  SubM.push k a
  SubM.change (·.pushRuns k runs)

/-! ## The one equation -/

/-- True if a virtual row's product form (HRow, Hide.lean) is well formed for X. -/
def rowFormOK (X : HTree) (r : HRow) : Bool :=
  let bits := clog2 X.R
  let np := r.rowPoint.size
  let given := !r.rowLo.isEmpty || !r.rowHi.isEmpty
  decide (np ≤ bits) && !((r.rowOnes || given) && (np != 0 || r.rowFirst != 0)) &&
    r.rowFirst % 2 ^ np == 0 && decide (r.rowFirst < X.R) &&
    !(given && (r.rowOnes || r.rowLo.size != bits || r.rowHi.size != bits))

/-- The pair of factors for bit t of a row's number: the first if the bit is 0, the second if it
is 1. -/
def rowFactors (r : HRow) (t : Nat) : E × E :=
  let np := r.rowPoint.size
  if !r.rowLo.isEmpty || !r.rowHi.isEmpty then (r.rowLo.getD t zeroE, r.rowHi.getD t zeroE)
  else if r.rowOnes then (oneE, oneE)
  else if t < np then
    let z := r.rowPoint.getD (np - 1 - t) zeroE
    (subE oneE z, z)
  else if r.rowFirst.testBit t then (zeroE, oneE)
  else (oneE, zeroE)

/-- The product form of a virtual row's weights on the rows of X, bit 0 of a row's number first. -/
def rowProduct (X : HTree) (r : HRow) : IndexWeights :=
  let pairs := (Array.range (clog2 X.R)).map (rowFactors r)
  { lo := pairs.map (·.1), hi := pairs.map (·.2) }

/-- A product form written out: entry i is the product over the bits t of i of hi[t] if the bit is
set and lo[t] if not. -/
def productWritten (w : IndexWeights) : Array E :=
  (List.range w.lo.size).foldl
    (fun all t =>
      let lo := w.lo.getD t zeroE
      let hi := w.hi.getD t zeroE
      all.map (fun x => mulE x lo) ++ all.map (fun x => mulE x hi))
    #[oneE]

/-- The weights of a virtual row on the rows of X as the chain takes them: a product over the bits
of the row's number. The written-out vector coef must be the same function: on a view each of its R
entries is compared. The dry run skips the comparison. -/
def rowWeights (X : HTree) (r : HRow) : SubM IndexWeights := do
  mustAs "internal-row-form" (rowFormOK X r)
  let w := rowProduct X r
  let all := productWritten w
  testAs "internal-row-form"
    (allBelow X.R fun i => all.getD i zeroE == r.coef.getD i zeroE)
  pure w

/-- The product form over 2^bits indices that is 1 at index i and 0 elsewhere. -/
def pickIndex (bits i : Nat) : IndexWeights :=
  let ones := (Array.range bits).map fun b => i.testBit b
  { lo := ones.map fun one => if one then zeroE else oneE,
    hi := ones.map fun one => if one then oneE else zeroE }

/-- The terms of the equation on one array. born, array: the link that committed to it and its name
there. A virtual row with a product form gives one term. Any other row has both weight vectors
written out, and a term can carry only one written-out vector (ReqTerm), so it gives R terms, one
for each row of the array; the C++ leaves out rows whose weight is 0, which does not change the sum.
-/
def doorTerms (born : Nat) (array : String) (X : HTree) : SubM (Array ReqTerm) := do
  let mut terms : Array ReqTerm := #[]
  for r in X.rows do
    mustAs "internal-coef" (r.coef.size == X.R && r.L.size == X.K && r.L0 == 0)
    let onColumns : IndexWeights := { values := some r.L }
    if r.rowForm then
      let onRows ← rowWeights X r
      terms := terms.push { born := born, array := array, onRows := onRows, onColumns := onColumns }
    else
      for i in List.range X.R do
        terms := terms.push
          { born := born, array := array, scale := r.coef.getD i zeroE,
            onRows := pickIndex (clog2 X.R) i, onColumns := onColumns }
  pure terms

/-- True if the layout has an array of this name in link born, with R rows and K columns. -/
def laidAs (c : ChainCheck) (born : Nat) (name : String) (R K : Nat) : Bool :=
  ((c.rows.layout.link.getD born []).find? fun A => A.name == name).any fun A =>
    A.sizeI == R && A.sizeC == K

/-- Called when all claims of the sub-proof have been added. Passes the one equation to the chain,
which adds it as a row to the link's group of oracle messages and closes the link
(ChainCheck.close). From the start of this call on Fork.push and Fork.kapTake refuse, so Fork.lin
and t2Lin add no further claim. equationsLaid: the number of indices that the equations of the
smallness test take, as HTailF2.equationsLaidF (OnBytes/Model/Tail.lean) gives it; doorH takes it as
the caller passes it.

The equation. Fork.trees[i].R and .K are the numbers of rows and of columns of array i. Each of its
virtual rows v has weights coef on the array's rows and weights L on its columns. When all claims
are added,
   sum over the virtual rows of <coef (x) L, array> + <maskCoef, the link's mask row> + constant = 0
is what remains to be tested. coef (x) L is the matrix with entries coef[r] * L[c]. maskCoef and
constant are what Fork.settle (Hide.lean) makes of LS, c0 and the shown values. doorH writes the
equation as terms of rank one on named arrays, the coefficients maskCoef on the first entries of the
mask row, and the public target -constant. -/
def doorH (equationsLaid : Nat) : LinkM Unit := do
  let L ← get
  LinkM.mustAs "internal-t2-order" (L.list.link && !L.list.walked && !L.done)
  LinkM.sub (SubM.change fun F => some { F with doorShutF := true })
  LinkM.mustAs "internal-t2-order" L.handed
  let F ← LinkM.fork
  LinkM.mustAs "internal-f-door" (F.planClaimsF != 0 && F.nClaim == F.planClaimsF)
  LinkM.sub SubM.allTaken
  -- What is passed on is the weights on the listed arrays. A weight elsewhere would be dropped.
  LinkM.testAs "internal-f-door" ((F.trees.extract L.list.nt.size F.trees.size).all fun X =>
    X.rows.all fun r => r.L.all isZeroE)
  LinkM.mustAs "plan-link" (L.arrayOf.size == L.list.nt.size)
  LinkM.must (decide (L.list.nt.size ≤ F.trees.size))
  let mut terms : Array ReqTerm := #[]
  for ti in List.range L.list.nt.size do
    let (born, array) := L.arrayOf.getD ti (0, "")
    let X := F.trees.getD ti {}
    -- The weights have the array's size in the layout: none is cut off or left without an entry.
    LinkM.must (laidAs L.check born array X.R X.K)
    terms := terms ++ (← LinkM.sub (doorTerms born array X))
  let (onMasks, constant) ← LinkM.sub (SubM.settle L.list.used)
  -- The plan fixes how many rows the batching element's round combines. It must be the number added
  -- here; batchRows compares the two on a view, not in the dry run. That number is a count only in
  -- part: the claims (nClaim) and the reads of the smallness test are counted as they are added,
  -- but the number of the matrices' equations is computed from the matrices' shapes, as in the
  -- plan. batchRows looks at the entry of the round that was closed last, so the caller must close
  -- no round between t2Batch and this line.
  LinkM.sub (SubM.batchRows (F.nClaim + equationsLaid))
  LinkM.call fun c => c.close { terms := terms, onMasks := onMasks, target := subE zeroE constant }
  modify fun L => { L with list := { L.list with walked := true }, done := true }

end OnBytes.Model
