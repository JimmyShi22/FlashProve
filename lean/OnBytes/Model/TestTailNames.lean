-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestTailNames.lean: conditions inside routines of Trees.lean and Tail.lean, by the
name under which each fails.

A routine in SubM or LinkM fails under a name. This file runs eight routines on small states without
a proof and without rounds: objectsF, linRead (after weightsF), drawMatrixF and transcriptF of
Tail.lean, and doorH, t2Batch, rootInH and LinkM.call of Trees.lean. On the unchanged state
objectsF, linRead and LinkM.call do not fail. transcriptF fails there under internal-f-matrix-order.
drawMatrixF, doorH and t2Batch are meant to run as far as their first call of the channel and to
fail there, under a name of the channel. rootInH is meant to fail in its call of the chain. The
guards hold less: the name is none of those that are expected of the same routine where a condition
is false, and, except for rootInH, there is a failure. A state in which one earlier condition is
false must fail under that condition's name. That no other condition is false is by the choice of
the state. Several conditions share a name, so a name does not always show which of them failed. A
condition written with must, and a step that returns none, have the name "refused".

Not reached here: the conditions after a call of the channel or of the chain (internal-f-draws among
them); in objectsF, the five conditions named internal-f-exist, the one named internal-f-join-place
and the steps that return none; in doorTerms, the length of L and L0 = 0; in rowWeights, that the
product form is well formed; all of selfTestF and tileSelfTestF. OnBytes/Model/TestTreesChannel.lean
reaches the later conditions of rootInH and t2Batch. OnBytes/Model/TestTailMore.lean reaches
internal-f-join-place and two of the five. OnBytes/Model/TestTailHeld.lean tests most conditions of
selfTestF and tileSelfTestF, and runs both with the names internal-t2f-untyped,
internal-f-tail-slot, internal-t2f-untiled, internal-f-tie-weights and internal-f-read-weights.
OnBytes/Model/TestTreesConditions.lean tests the conditions of doorTerms and rowWeights and does not
look at the name. The docstring of subName says where the C++ verifier has the names and conditions.

The terms are explained in OnBytes/Model/Tail.lean (the docstring of HTailF2 says where), and at the
head of OnBytes/Model/Trees.lean, the channel and its rounds in OnBytes/Iop/Ground.lean. The file is
not imported by the program. The C++ files that are named below lie in verifier/src.
-/
import OnBytes.Model.TestTailRun

namespace OnBytes.Model.TestTailNames

open OnBytes OnBytes.Model OnBytes.Model.TestTailRun

/-- The name under which a routine of a sub-proof fails on the state F; "" if it does not fail.

Each name that a guard of this file writes out, except "refused", is in vf_rejection_names.txt; four
end there in a hyphen, after which the C++ appends a name. The counterparts of the conditions that
the guards try are in vf_subproof_segment.h, vf_smallness_test_members.inc and vf_smallness_test.h,
for internal-eq-index in vf_common.h, and for internal-L-row in vf_lookup_helpers.h (uEnt; the
comment at the guards of readName says what it does not test). Some conditions that fail here as
"refused" have no line in the C++; the docstrings of Trees.names and Tail.names list them. -/
def subName {α : Type} (x : SubM α) (F : Fork) : String :=
  match (x F) (noRounds false) with
  | .ok _ => ""
  | .error e => e.name

/-- The name under which a routine inside a link fails; "" if it does not fail. -/
def linkName {α : Type} (x : LinkM α) (L : LinkCtx) (F : Fork) : String := subName (x L) F

/-! ## The claims of the smallness test -/

/-- The example of TestTailRun before its claims are added. -/
def before : Option (HTailF2 × Fork) :=
  planned.toOption.map fun (tl, F) => (afterMessages tl, afterDraw tl F)

/-- The name under which objectsF fails on the changed example with the list funs of tables. The
same list is first recorded as the closed one; onTl can then change that record. -/
def claimsName (funs : Array HFun) (onTl : HTailF2 → HTailF2 := id) (onF : Fork → Fork := id) :
    String :=
  match before with
  | none => "no example"
  | some (tl, F) => subName ((onTl { tl with funs := funs }).objectsF funs) (onF F)

/-- The example's table. -/
def table : HFun := (funs false).getD 0 {}

#guard claimsName #[table] == ""
-- The list is not the one that was closed.
#guard claimsName #[table] (fun tl => { tl with funs := #[{ table with start := 1 }] }) ==
  "internal-f-fun-moved"
#guard claimsName #[table] (fun tl => { tl with funClosed := false }) == "internal-f-fun-closed"
#guard claimsName #[table] (fun tl => { tl with funs := #[table, table] }) ==
  "internal-f-fun-closed"
-- A weight on a slot of the smallness test before its claims.
#guard claimsName #[table] id (fun F => { F with LS := F.LS.set! 3 oneE }) == "internal-f-tail-slot"
-- The sub-proof has no U1.
#guard claimsName #[{ table with tree := 0 }] == "internal-t2f-unit"
#guard claimsName #[{ table with len := 0, phi := #[] }] == "shape-functional"
#guard claimsName #[{ table with len := 4, phi := els false 50 4 }] == "shape-functional"
#guard claimsName #[{ table with phi := els false 50 2 }] == "shape-functional"
-- A table of a matrix that does not exist, or on a vector that holds no tables, is never read.
#guard claimsName #[table, { table with mat := 1 }] == "internal-t2f-functional"
#guard claimsName #[table, { table with tree := 1 }] == "internal-t2f-functional"
-- One segment of six rows reads two of U3's four entries.
#guard claimsName #[{ table with len := 6, phi := els false 50 6 }] == "internal-f-table-read"
-- A column's sum over the drawn matrix is 0: all its entries are 0.
#guard claimsName #[table] (fun tl => { tl with
  cfF := (Array.range 320).map fun i => if i < 160 then 0 else tl.cfF.getD i 0 }) ==
  "internal-f-table-read"
-- The padding key of a call is not 0.
#guard claimsName #[table] (fun tl => { tl with
  z2 := { tl.z2 with call := { tl.z2.call with t0 := 1 } } }) == "internal-f-padding-key"
-- A piece with more keys than its call, and a piece that begins after the call's last key.
#guard claimsName #[table] (fun tl => { tl with
  z1 := { tl.z1 with pieces := tl.z1.pieces.modify 0 fun p => { p with b := 12 } } }) ==
  "internal-eq-index"
#guard claimsName #[table] (fun tl => { tl with
  z1 := { tl.z1 with pieces := tl.z1.pieces.modify 1 fun p => { p with off := 8192 } } }) ==
  "internal-eq-index"

/-! ## One read -/

/-- The name under which the example's first read fails. -/
def readName (Fn : HFun) (onF : Fork → Fork := id) : String :=
  match before with
  | none => "no example"
  | some (tl, F) =>
    subName (do
      let tl ← tl.weightsF
      tl.linRead Fn 0 0 oneE) (onF F)

#guard readName table == ""
-- U3 without a column; a row of U3 whose index does not fit 32 bits. The C++ counterpart, uEnt
-- (vf_lookup_helpers.h), tests the second and does not test whether the array has a column.
#guard readName table (fun F => { F with trees := F.trees.modify 0 fun X => { X with K := 0 } }) ==
  "internal-L-row"
#guard readName { table with start := 2 ^ 32 }
  (fun F => { F with trees := F.trees.modify 0 fun X => { X with K := 1 } }) == "internal-L-row"

/-! ## The draw of the matrix -/

/-- The name under which drawMatrixF fails on the changed example. -/
def drawName (onTl : HTailF2 → HTailF2) : String :=
  match before with
  | none => "no example"
  | some (tl, F) => subName (onTl tl).drawMatrixF F

#guard drawName id != "" && drawName id != "refused"
#guard drawName (fun tl => { tl with NM := 2 }) == "refused"
#guard drawName (fun tl => { tl with NM := 0, mats := #[] }) == "refused"

/-! ## Inside a link -/

/-- A request's shape with one link of two oracle messages, at the moments 0 and 1. -/
def shape : Params.ReqShape :=
  { (default : Params.ReqShape) with
    link := [{ plain := 0, messages := [
      { shape := {}, leafClass := 0, moment := 0, life := 0 },
      { shape := {}, leafClass := 0, moment := 1, life := 0 }] }] }

/-- The layout: the array A, of six rows and one column, in the link's first message. -/
def layout : Params.ReqLayout :=
  { link := [[{ name := "A", message := 0, sizeI := 6, sizeC := 1, blocks := [] }]] }

/-- The state of the calls over the links at link 0, with the shape and the layout above. Its own
record of the order is left at the defaults (inLink is false), so ChainCheck.later and
ChainCheck.close fail on it. -/
def check : ChainCheck :=
  { frame := { shape := shape, groups := #[] }, rows := { layout := layout } }

/-- The link when doorH is called: both moments have come and the batching element is drawn. -/
def atDoor : LinkCtx :=
  { check := check, arrayOf := #[(0, "A")],
    list := { link := true, planned := true, nt := #[{}] }, moments := 2, handed := true }

/-- The sub-proof's state when doorH is called: one array with one virtual row, one claim. -/
def forkAtDoor : Fork :=
  { trees := #[{ name := "A", R := 6, K := 1,
                 rows := #[{ coef := Array.replicate 6 oneE, L := #[oneE], rowForm := true,
                             rowOnes := true }] }],
    planClaimsF := 1, nClaim := 1, kapMapF := #[true], thetaDrawnF := true }

/-- The name under which doorH fails. -/
def doorName (onL : LinkCtx → LinkCtx := id) (onF : Fork → Fork := id) : String :=
  linkName (doorH 0) (onL atDoor) (onF forkAtDoor)

/-- The name under which the example fails. It is meant to be the channel's, which has no round; the
guard below holds only that it is not empty and none of the names that this section expects where a
condition is false. -/
def channel : String := doorName

#guard !["", "refused", "internal-t2-order", "internal-f-door", "plan-link", "internal-coef",
  "internal-row-form"].contains channel
#guard doorName (fun L => { L with list := { L.list with link := false } }) == "internal-t2-order"
#guard doorName (fun L => { L with list := { L.list with walked := true } }) == "internal-t2-order"
#guard doorName (fun L => { L with done := true }) == "internal-t2-order"
#guard doorName (fun L => { L with handed := false }) == "internal-t2-order"
#guard doorName id (fun F => { F with planClaimsF := 0, nClaim := 0, kapMapF := #[] }) ==
  "internal-f-door"
#guard doorName id (fun F => { F with nClaim := 0 }) == "internal-f-door"
-- A claim's weight was not handed out.
#guard doorName id (fun F => { F with kapMapF := #[false] }) == "refused"
-- A weight on an array outside the list.
#guard doorName id (fun F => { F with
  trees := F.trees.push { R := 1, K := 1, rows := #[{ L := #[oneE] }] } }) == "internal-f-door"
#guard doorName id (fun F => { F with
  trees := F.trees.push { R := 1, K := 1, rows := #[{ L := #[zeroE] }] } }) == channel
#guard doorName (fun L => { L with arrayOf := #[] }) == "plan-link"
-- The list is longer than the arrays.
#guard doorName (fun L => { L with arrayOf := #[(0, "A"), (0, "A")],
                                   list := { L.list with nt := #[{}, {}] } }) == "refused"
-- The array's name and link against the layout, through doorH; its size on laidAs itself.
#guard doorName (fun L => { L with arrayOf := #[(0, "B")] }) == "refused"
#guard doorName (fun L => { L with arrayOf := #[(1, "A")] }) == "refused"
#guard laidAs check 0 "A" 6 1 && !laidAs check 0 "A" 5 1 && !laidAs check 0 "A" 6 2
-- The length of coef against the array's rows; then a written-out weight against the product form.
#guard doorName id (fun F => HTailF2.onRow F 0 0 fun r => { r with coef := r.coef.push oneE }) ==
  "internal-coef"
#guard doorName id (fun F => HTailF2.onRow F 0 0 fun r => { r with coef := r.coef.set! 2 zeroE }) ==
  "internal-row-form"

/-! ## The batching element -/

/-- The link before the batching element is drawn. -/
def beforeBatch : LinkCtx := { atDoor with handed := false }

/-- The name under which t2Batch fails. The sub-proof has three slots. -/
def batchName (used : Nat) (onL : LinkCtx → LinkCtx := id) : String :=
  linkName (t2Batch used) (onL beforeBatch) { forkAtDoor with ns := 3, thetaDrawnF := false }

#guard !["", "refused", "internal-slot-count", "plan-link"].contains (batchName 3)
#guard batchName 2 == "internal-slot-count"
#guard batchName 3 (fun L => { L with list := { L.list with planned := false } }) ==
  "internal-slot-count"
#guard batchName 3 (fun L => { L with list := { L.list with link := false } }) == "plan-link"
#guard batchName 3 (fun L => { L with handed := true }) == "plan-link"
-- One moment of the link is still to come.
#guard batchName 3 (fun L => { L with moments := 1 }) == "plan-link"

/-! ## A commitment, and a call of the chain -/

#guard linkName (rootInH [0]) { beforeBatch with handed := true } forkAtDoor == "plan-link"
#guard linkName (rootInH [0]) { beforeBatch with done := true } forkAtDoor == "plan-link"
-- On beforeBatch itself rootInH is meant to pass its first condition and to fail in its call of the
-- chain: ChainCheck.later refuses the made-up state (check), which is not inside a link. This guard
-- holds only that the name is not plan-link.
#guard linkName (rootInH [0]) beforeBatch forkAtDoor != "plan-link"
#guard linkName (LinkM.call fun c => pure c) atDoor forkAtDoor == ""
#guard linkName (LinkM.call fun c => pure c) { atDoor with link := 1 } forkAtDoor == "refused"

/-! ## The messages of the smallness test -/

/-- The name under which transcriptF fails on the changed example. -/
def messagesName (onTl : HTailF2 → HTailF2) : String :=
  match before with
  | none => "no example"
  | some (tl, F) => linkName (onTl tl).transcriptF beforeBatch F

-- On the unchanged example transcriptF fails under internal-f-matrix-order: the made-up link does
-- not have the example's arrays, so this guard shows that transcriptF calls the test of the order
-- before it draws the matrix. The test stands after the two conditions below.
#guard messagesName id == "internal-f-matrix-order"
#guard messagesName (fun tl => { tl with funClosed := false }) == "internal-f-fun-open"
#guard messagesName (fun tl => { tl with shp := #[] }) == "internal-t2f-map"

end OnBytes.Model.TestTailNames
