-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Plan/PlaceShape.lean: the written list of a sub-proof's arrays and its number of
slots (Shape, OnBytes/Tie/Pv/Led/LedJoint.lean), at every link of the proof's first chain, from the
records that the verifier's own reader makes.

A lay of entries gives each entry an address: a cell of an array, by the array's number in the
sub-proof's list, or an entry of the mask row. Shape.lay is the lay of all cells and all mask
entries of a written list. Here that list is read off the plan's state of arrays (Fp, a Fork of
OnBytes/Model/Hide.lean): of each array its name, rows, columns and whether this sub-proof commits
it, in the order of the list.

Main names:
  shapeOfFork F ns: the list of the arrays of F, with ns slots.
  forkAt c n: the plan's state of arrays at link n: of the group of layers, of the attention plan or
    of the head.
  shapeAt c n: the Shape of link n. The number of slots is the number of scalars that the link's
    planned rounds send.
  shapeTests c n (shapeCmp): by evaluation: (1) the list is not empty, and the record of the
    smallness test counts as many arrays; (2) the array of each matrix's symbols is in the list, is
    marked as symbols, and has the rows of symbols and the columns of that matrix; (3) the vector of
    reads that holds all tables is in the list, with one row and as many columns as the record's
    number of entries; (4) the two arrays of the lookup on digits are in the list; (5) no two arrays
    have one name; (6) the list and the number of slots are those of the planned state and number of
    scalars of link n in the list of links that the verifier runs (Verify.linksOf; LinkH.Fp,
    LinkH.ns).
  shapeFaults, shapeControl: four faults on the list alone; under each the test at its place, (2) to
    (5), is false.
Limits: definitions and tests by evaluation, no theorem. forkAt picks the state by a match of its
own; that its list of arrays (names, rows, columns, owners) and the number of slots are those of the
verifier's own link is test (6), an evaluation. The arrays' kinds, which (2) reads, are not
compared. Tests (1) and (6) have no control. That the verifier's run keeps this list is not said
here. A cell's row is a row of the array, not a virtual row.
The program does not import this file.

-/
import OnBytes.Tie.Pv.Plan.PlaceNums
import OnBytes.Tie.Pv.Led.LedJoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Plan

open OnBytes.Model (Fork)
open OnBytes.Road.Rows (Shape)

/-- The arrays of a state, as a written list. -/
def shapeOfFork (F : Fork) (ns : Nat) : Shape :=
  ⟨F.trees.toList.map fun t => ⟨t.name, t.R, t.K, t.owner⟩, ns⟩

/-- The plan's state of arrays at a link. -/
def forkAt (c : Chain1) (n : LinkNums) : Except String Fork :=
  match n.att, n.head with
  | some a, _ => pure a.seam.Fp
  | none, some _ => pure c.X.H.Fp
  | none, none => do pure (← OnBytes.Params.orRefuse c.X.G[n.group]?).Fp

/-- The Shape of a link. -/
def shapeAt (c : Chain1) (n : LinkNums) : Except String Shape := do
  pure (shapeOfFork (← forkAt c n) (sentBy (n.l0 ++ n.l1 ++ n.l2)))

/-- The first five tests: a list of arrays against a state of arrays and a smallness test's
record. -/
def shapeCmp (F : Fork) (S : Shape) (tl : OnBytes.Model.HTailF2) : List Bool :=
  let N := S.arrays.length
  let u3 := (tl.ix.U.getD 2 none).getD N
  [N != 0 && tl.ix.count == N,
   (List.range tl.NM).all fun mu =>
     let t := tl.gtTree.getD mu N
     (S.arrays[t]?).any (fun a => a.R == (tl.shp.getD mu {}).mS &&
       a.K == (tl.mats.getD mu {}).k) &&
     (F.trees[t]?).any (fun x => x.kind == .symbols),
   (S.arrays[u3]?).any fun a => a.R == 1 && a.K == tl.nUF.getD 2 0,
   decide (tl.ix.ZZ < N) && decide (tl.ix.BZ < N) && tl.ix.ZZ != tl.ix.BZ,
   (S.arrays.map (·.name)).Nodup]

/-- The six tests at a link. -/
def shapeTests (c : Chain1) (n : LinkNums) : Except String (List Bool) := do
  let S ← shapeAt c n
  let L ← OnBytes.Model.Verify.linksOf c.X default
  pure (shapeCmp (← forkAt c n) S n.tail ++ [(L[n.link]?).any fun x => shapeOfFork x.Fp x.ns == S])

/-- Four faults on the list alone, each with the place of the test that must fall: the first
symbols' array with a row less (2); the vector of reads with a column more (3); the list cut before
the later of the two arrays of the lookup on digits (4); the first array laid twice (5). -/
def shapeFaults (S : Shape) (tl : OnBytes.Model.HTailF2) : List (Nat × Shape) :=
  let on := fun (t : Nat) (f : OnBytes.Road.Rows.Arr → OnBytes.Road.Rows.Arr) =>
    { S with arrays := S.arrays.modify t f }
  [(1, on (tl.gtTree.getD 0 0) fun a => { a with R := a.R - 1 }),
   (2, on ((tl.ix.U.getD 2 none).getD 0) fun a => { a with K := a.K + 1 }),
   (3, { S with arrays := S.arrays.take (max tl.ix.ZZ tl.ix.BZ) }),
   (4, { S with arrays := S.arrays ++ S.arrays.take 1 })]

/-- Whether under each fault the test at its place is false. -/
def shapeControl (c : Chain1) (n : LinkNums) : Except String Bool := do
  let F ← forkAt c n
  let S ← shapeAt c n
  pure ((shapeFaults S n.tail).all fun (i, S') => (shapeCmp F S' n.tail)[i]? == some false)

end OnBytes.Tie.Pv.Plan
