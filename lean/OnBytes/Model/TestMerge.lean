-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestMerge.lean: tests of OnBytes/Model/Merge.lean and OnBytes/Model/Pending.lean, run
when this file compiles.

The program does not import this file.

A small world is made up: a layout, a matrix W, some claims with made-up factors on several units,
a mask row, one further mask entry c, and all the verifier's draws. An honest prover is written here
from the definition of the masked sumcheck. It shows each claim's value and runs the merge
on the map F(X) = sum_a rho_a eps_a(X) < gamma_a, W[., X] >. Here eps_a(X) is the value of claim a's
factors on the columns (wsEpsT) and gamma_a its coefficients on the rows (wsGamma). Both are taken
from OnBytes/Model/Weights.lean, on the prover's side too: that they mean what a claim says is
tested in OnBytes/Model/TestWeights.lean, not here. The verifier's routines then walk over the
prover's messages. What is tested:
 1. The dry run gives the expected rounds: their names and the numbers of elements.
 2. The walk succeeds, uses all rounds and takes the announced number of slots.
 3. (U) The sub-proof's one equation holds on the mask row, and the mask entry under the slot of fv'
    has the coefficient 0.
 4. (E) The row that leaves the sub-proof is true of the matrix:
    < Gamma (x) eq(rm, .), W > + beta c = fv'.
 5. Caught: a false value of a claim, by (U); a different c, or a different matrix on the verifier's
    side, by (E); any one sent element raised by 1, by (U) or (E).
 6. Refusals: a claim with a factor of another length than its group's; each test of wsForkEnd,
    under its name; eight inputs of wsPending (listed at their guard), compared by name alone.
verifier/tests/pending_row_test.cpp tests property 4 on made-up records, and four of the refusals
of wsPending in 6, on the C++ verifier.
-/
import OnBytes.Model.Pending
import OnBytes.Model.TestWeights

namespace OnBytes.Model.TestMerge

open TestWeights (madeUp madeUpList claimOn)

/-- The number of column bits. -/
def lk : Nat := 3

/-- The layout of the made-up world. -/
def lay : WsLay := (WsLay.build TestWeights.oddParts lk).toOption.getD {}

/-- The units that the claims are about, in the claims' order. -/
def unitsOf : List Nat := [1, 0, 8, 17, 4]

/-- The claims. -/
def claims : Array WsClaim := (unitsOf.map fun ui => claimOn (lay.U.getD ui {}) ui).toArray

/-- The number of claims. -/
def ncl : Nat := unitsOf.length

/-- The number of slots: one for each claim's value, then the merge's. -/
def ns : Nat := ncl + wsForkSlots lk

/-- What can be altered in a world. -/
structure World where
  /-- added to the matrix's entry (5, 2) on the verifier's side -/
  otherCell : E := zeroE
  /-- added to c on the verifier's side -/
  otherC : E := zeroE
  /-- added to the value of claim 1 that the prover shows -/
  falseValue : E := zeroE
  /-- the number of a sent element that is raised by 1, in the order of sending -/
  raised : Option Nat := none

/-- The matrix's entry in row y and column col: a small number, as a digit is. -/
def cell (y col : Nat) : E := ofNat ((y * 37 + col * 11 + y * col) % 256)

/-- Entry j of the sub-proof's mask row. -/
def mask (j : Nat) : E := madeUp (50000 + j)

/-- The entry of the index-mask message. -/
def maskC : E := madeUp 60000

/-- The drawn elements: the batching element, eps, the challenges of the rounds, beta, theta. theta
is passed to SubM.batchBy. The check adds one claim by SubM.lin, whose weight is theta^0, so the
value of theta does not matter. -/
def drawX : E := madeUp 70000
/-- See drawX. -/
def drawEps : E := madeUp 70001
/-- See drawX. -/
def drawR : Array E := madeUpList 70002 lk
/-- See drawX. -/
def drawBeta : E := madeUp 70003
/-- See drawX. -/
def drawTheta : E := madeUp 70004

/-- For claim a: < gamma_a, W[., col] > for each column, gamma_a the claim's weights on the rows. -/
def onColumns (a : Nat) : Array E :=
  let c := claims.getD a {}
  let u := lay.U.getD c.ui {}
  let gamma := wsGamma u (wsRowPart lay c oneE) oneE
  Array.ofFn (n := 2 ^ lk) fun col =>
    (List.range u.rows).foldl
      (fun s y => maddE s (gamma.getD y zeroE) (cell (u.off + y) col.val)) zeroE

/-- What the prover computes once. It is passed to the functions below that need it: the layout,
the claims, the tables of onColumns, the claims' true values, and the coefficients rho. -/
structure Made where
  lay : WsLay
  claims : Array WsClaim
  tables : Array (Array E)
  values : Array E
  rho : Array E

/-- The true value of a claim: the sum over the columns. -/
def valueOf (c : WsClaim) (table : Array E) : E :=
  (List.range (2 ^ lk)).foldl
    (fun s col =>
      maddE s (wsEpsT lay c (TestWeights.pointOf lk col)) (table.getD col zeroE))
    zeroE

/-- See Made. -/
def made : Made :=
  let tables := Array.ofFn (n := ncl) fun a => onColumns a.val
  { lay := lay
    claims := claims
    tables := tables
    values := Array.ofFn (n := ncl) fun a =>
      valueOf (claims.getD a.val {}) (tables.getD a.val #[])
    rho := powers drawX ncl }

/-- The map F at a point z, the highest column bit first. -/
def mapF (m : Made) (z : Array E) : E :=
  let eq := eqTab z
  (List.range ncl).foldl
    (fun s a =>
      maddE s (mulE (m.rho.getD a zeroE) (wsEpsT m.lay (m.claims.getD a {}) z))
        (wsDot (2 ^ lk) (m.tables.getD a #[]) eq))
    zeroE

/-- Coefficient number i of the hiding polynomial: the mask entry under the sumcheck's slot i. -/
def hidingCoef (i : Nat) : E := mask (ncl + i)

/-- The hiding polynomial at the point (z, y): the sum over the variables l of w_l(X_l) times X_j
for each later variable j among the lk first. The polynomial w_l of the first lk variables has the
degrees 1 and 2. That of the last variable, Y, has the degrees 0 and 1. -/
def hidingAt (z : Array E) (y : E) : E :=
  let later := fun l => (List.range (lk - 1 - l)).foldl
    (fun p j => mulE p (z.getD (l + 1 + j) zeroE)) oneE
  let first := (List.range lk).foldl
    (fun s l =>
      let x := z.getD l zeroE
      maddE s (later l)
        (addE (mulE (hidingCoef (2 * l)) x) (mulE (hidingCoef (2 * l + 1)) (mulE x x))))
    zeroE
  addE first (addE (hidingCoef (2 * lk)) (mulE (hidingCoef (2 * lk + 1)) y))

/-- What the prover shows for the claims' values. -/
def shownValues (m : Made) (w : World) : Array E :=
  Array.ofFn (n := ncl) fun a =>
    addE (addE (m.values.getD a.val zeroE) (mask a.val))
      (if a.val == 1 then w.falseValue else zeroE)

/-- The public target of the sumcheck: the sum of rho[a] times what was shown for claim a. -/
def target (m : Made) (w : World) : E := wsDot ncl m.rho (shownValues m w)

/-- The public target of the sumcheck minus its true sum. -/
def shift (m : Made) (w : World) : E := subE (target m w) (wsDot ncl m.rho m.values)

/-- The polynomial on which the sumcheck runs, at the point (z, y). sh is the value of shift. -/
def whole (m : Made) (sh : E) (z : Array E) (y : E) : E :=
  let psi := z.foldl mulE oneE
  addE (hidingAt z y)
    (mulE drawEps (addE (addE (mapF m z) (mulE y maskC)) (mulE sh psi)))

/-- The sum of whole over all bit values of the next n variables (n is the last argument), with the
earlier variables at head and Y at 0. -/
def sumFrom (m : Made) (sh : E) (head : Array E) : Nat → E
  | 0 => whole m sh head zeroE
  | n + 1 => addE (sumFrom m sh (head.push zeroE) n) (sumFrom m sh (head.push oneE) n)

/-- The coefficients of the polynomial of degree 2 with the values v0, v1, v2 at 0, 1, 2. -/
def fromValues (v0 v1 v2 : E) : E × E × E :=
  let half := invE (ofNat 2)
  let c2 := mulE half (addE (subE v2 (addE v1 v1)) v0)
  (v0, subE (subE v1 v0) c2, c2)

/-- The elements that the prover sends, round by round, before any is altered. -/
def sent (m : Made) (w : World) : List (List E) :=
  let sh := shift m w
  let rounds := (List.range lk).map fun i =>
    let head := drawR.extract 0 i
    let q := fromValues (sumFrom m sh (head.push zeroE) (lk - 1 - i))
      (sumFrom m sh (head.push oneE) (lk - 1 - i))
      (sumFrom m sh (head.push (ofNat 2)) (lk - 1 - i))
    [q.1, q.2.2]
  [(shownValues m w).toList, [subE (sumFrom m sh #[] lk) (mulE drawEps (target m w))]] ++
    rounds ++
    [[subE (whole m sh drawR oneE) (whole m sh drawR zeroE)],
     [addE (mapF m drawR) (mulE drawBeta maskC)]]

/-- Raises element number k of the lists, counted through, by 1. -/
def raise : List (List E) → Nat → List (List E)
  | [], _ => []
  | l :: ls, k =>
    if k < l.length then (l.zipIdx.map fun (x, i) => if i == k then addE x oneE else x) :: ls
    else l :: raise ls (k - l.length)

/-- What the verifier draws, round by round. -/
def drawn : List (List E) :=
  [[drawX], [drawEps]] ++ drawR.toList.map (fun r => [r]) ++ [[drawBeta], []]

/-- The rounds of the view. -/
def view (m : Made) (w : World) : List Fmt.RoundView :=
  let s := match w.raised with
    | some k => raise (sent m w) k
    | none => sent m w
  (s.zip drawn).map fun (v, d) =>
    ({ vals := v.map fun x => Fmt.ItemValue.e x.triple
       drawn := { elems := d.map E.triple, poss := [], trits := [], digest := none } } : Fmt.RoundView)

/-- A plan's entry: the round's name, the elements sent, the elements drawn, how many of these are
not 0, and the rows that the round batches. -/
def entryOf (name : String) (elems drawE : Nat) (drawNZ : Nat := 0) (rows : Nat := 0) : Fmt.Entry :=
  { name := name, msg := 24 * elems, drawE := drawE, drawNZ := drawNZ, rows := rows }

/-- The plan's entries of these rounds. -/
def entries : List Fmt.Entry :=
  [entryOf "BAT-sigma" ncl 1 0 ncl, entryOf "PSC epsilon" 1 1] ++
  List.replicate lk (entryOf "PSC round" 2 1) ++
  [entryOf "PSC Y" 1 1 1, entryOf "PSC values" 1 0]

/-- What the block starts from, for given entries of a plan: no code, no oracle message, no tree. -/
def startOf (es : List Fmt.Entry) : Start := { entries := es, st := {} }

/-- What the verifier's side of the test returns. -/
structure Result where
  out : WsForkOut
  maskCoef : Array E
  constant : E
  slotsTaken : Nat

/-- The verifier's side: the claims' values are received, the merge is run, its claim is added, and
the one equation is settled. -/
def check (cl : Array WsClaim) : SubM Result := do
  SubM.slots ns
  SubM.batchBy drawTheta
  let s ← SubM.claimsIn ncl
  let out ← wsForkEnd lay cl (Array.ofFn (n := ncl) fun a => s + a.val)
  wsForkLin out.toWsMerged
  let taken ← SubM.slot
  let (maskCoef, constant) ← SubM.settle taken
  pure { out := out, maskCoef := maskCoef, constant := constant, slotsTaken := taken }

/-- The check as a block. -/
def block (cl : Array WsClaim) : Blk Result := (check cl).run' {}

/-- The walk on a world's view: the result if the walk succeeds and uses all rounds. -/
def walked (m : Made) (w : World) : Option Result :=
  match (block m.claims).walk (startOf entries) [] (view m w) with
  | some (r, []) => some r
  | _ => none

/-- (U): the one equation on the mask row. -/
def holdsU (r : Result) : Bool :=
  isZeroE ((List.range ns).foldl (fun s j => maddE s (r.maskCoef.getD j zeroE) (mask j)) r.constant)

/-- A shape of the test on the matrix with only the number of rows set. wsPending reads nothing else
of it. -/
def linShape : Params.LinShape := { (default : Params.LinShape) with matrixRows := lay.m0 }

/-- (E): the row that leaves the sub-proof, on the matrix. -/
def holdsE (w : World) (r : Result) : Bool :=
  match wsPending lay r.out ncl linShape with
  | .error _ => false
  | .ok p =>
    let weights := p.g.foldl (fun o t => t.addTo o) (Array.replicate (2 ^ linShape.kRow) zeroE)
    let eq := eqTab p.psi.reverse.toArray
    let other := fun y col => if y == 5 && col == 2 then w.otherCell else zeroE
    let sum := (List.range lay.m0).foldl
      (fun s y =>
        if isZeroE (weights.getD y zeroE) then s
        else
          maddE s (weights.getD y zeroE)
            ((List.range (2 ^ lk)).foldl
              (fun t col => maddE t (eq.getD col zeroE) (addE (cell y col) (other y col))) zeroE))
      zeroE
    addE sum (mulE p.beta (addE maskC w.otherC)) == p.target

/-- Both (U) and (E) on a world; none if the walk fails. -/
def both (m : Made) (w : World) : Option (Bool × Bool) :=
  (walked m w).map fun r => (holdsU r, holdsE w r)

-- 1. the dry run
#guard ((block claims).rounds (startOf entries)).map
    (·.map fun x => (x.1.entry.name, x.1.items.length))
  == some ([("BAT-sigma", ncl), ("PSC epsilon", 1)] ++ List.replicate lk ("PSC round", 2) ++
    [("PSC Y", 1), ("PSC values", 1)])
-- 2. the walk, the slots
#guard wsForkSlots lk == 1 + 2 * lk + 1 + 1
-- 2, 3, 4. the walk and the slots; (U) and (E); the mask entry under the slot of fv' masks nothing
#guard (walked made {}).map (fun r =>
    (r.slotsTaken, r.out.rm, r.out.beta, holdsU r, holdsE {} r, r.out.sFv,
      r.maskCoef.getD r.out.sFv oneE,
      (List.range (ns - 1)).all fun j => !isZeroE (r.maskCoef.getD j zeroE)))
  == some (ns, drawR, drawBeta, true, true, ns - 1, zeroE, true)
-- 5. what is caught
#guard
  let m := made
  both m { falseValue := oneE } == some (false, true) &&
  both m { otherC := oneE } == some (true, false) &&
  both m { otherCell := oneE } == some (true, false) &&
  (List.range ns).all fun k =>
    match both m { raised := some k } with
    | some (u, e) => !(u && e)
    | none => false
-- a view without its last round; a plan without its first entry
#guard ((block claims).walk (startOf entries) [] ((view made {}).dropLast)).isNone
#guard ((block claims).rounds (startOf (entries.drop 1))).isNone
-- 6. the refusals of wsForkEnd and wsPending
/-- The claim with one element more in the member HV of each factor. -/
def longer (c : WsClaim) : WsClaim :=
  { c with f := c.f.map fun (x : WsFac) => { x with HV := x.HV.push oneE } }

/-- The beginning of the check, up to the end of wsForkEnd, with the slots sv. -/
def checkWith (cl : Array WsClaim) (sv : Array Nat) : SubM Unit := do
  SubM.slots ns
  SubM.batchBy drawTheta
  let _ ← SubM.claimsIn ncl
  let _ ← wsForkEnd lay cl sv
  pure ()

/-- The name under which the dry run of checkWith fails. -/
def refusedAs (cl : Array WsClaim) (sv : Array Nat) : Option String :=
  match ((checkWith cl sv).run' {} : Blk Unit).dryRunNamed (startOf entries) with
  | .error e => some e.name
  | .ok _ => none

-- the claims as they are, with one slot each, are not refused
#guard refusedAs claims (Array.range ncl) == none
-- no claim; too many claims; fewer slots than claims
#guard refusedAs #[] #[] == some "internal-claim-count"
#guard refusedAs (Array.replicate 4097 (claims.getD 0 {})) (Array.replicate 4097 0)
  == some "internal-claim-count"
#guard refusedAs claims (Array.range (ncl - 1)) == some "internal-claim-count"
-- a unit that is not in the layout; a factor of the wrong length
#guard refusedAs (claims.modify 1 fun c => { c with ui := lay.U.size }) (Array.range ncl)
  == some "internal-claim-unit"
#guard refusedAs (claims.modify 2 longer) (Array.range ncl) == some "internal-claim-factors"

/-- The name under which wsPending refuses; none if it does not. -/
def pendingName (x : Except String WsPending) : Option String :=
  match x with
  | .error e => some e
  | .ok _ => none

-- wsPending: as it is; another number of rows in the test's shape; no claim; another number of
-- claims than the plan's; a point with a coordinate too few; units beyond the layout's last row; a
-- unit that is not in the layout; a factor too few in each claim; 63 bits in a row's number
-- All refusals on rows have the one name "internal-gamma-rows", so the name does not tell which
-- test refused. For three inputs a later test would refuse under that name if the first were
-- missing: units beyond the last row and 63 bits (memberWeightsOnRows); the unknown units, which
-- are all units here (the test that the stretch of rows is not empty). A factor too few is refused
-- by wsGammaAdd at the first claim, for its number of coefficients.
#guard (walked made {}).map (fun r =>
    let o := r.out
    [pendingName (wsPending lay o ncl linShape),
     pendingName (wsPending lay o ncl { linShape with matrixRows := lay.m0 + 1 }),
     pendingName (wsPending lay { o with recs := [] } 0 linShape),
     pendingName (wsPending lay o (ncl + 1) linShape),
     pendingName (wsPending lay { o with rm := o.rm.pop } ncl linShape),
     pendingName (wsPending { lay with m0 := 1 } o ncl { linShape with matrixRows := 1 }),
     pendingName (wsPending lay { o with recs := o.recs.map fun c => { c with ui := lay.U.size } }
       ncl linShape),
     pendingName (wsPending lay { o with recs := o.recs.map fun c => { c with f := c.f.dropLast } }
       ncl linShape),
     pendingName (wsPending { lay with m0 := 2 ^ 63 } o ncl
       { linShape with matrixRows := 2 ^ 63 })])
  == some [none, some "internal-gamma-rows", some "link-claim-count", some "link-claim-count",
    some "link-claim-count", some "internal-gamma-rows", some "internal-gamma-rows",
    some "internal-gamma-rows", some "internal-gamma-rows"]

-- every name that a test above expects is in the two files' lists, and these have no other name
#guard Merge.names == ["internal-claim-count", "internal-claim-unit", "internal-claim-factors"]
#guard Pending.names == ["internal-gamma-rows", "link-claim-count"]

end OnBytes.Model.TestMerge
