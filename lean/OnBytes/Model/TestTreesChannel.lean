-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestTreesChannel.lean: rootInH and t2Batch of Trees.lean on a dry channel whose plan
is written by hand, and a few conditions on made-up states.

OnBytes/Model/TestTailNames.lean runs the routines of Trees.lean without rounds, so it reaches only
the conditions before a routine's first call of the channel. Here the channel is a dry one, and its
plan, written by hand, has just the rounds that the routine closes. So rootInH gets past
ChainCheck.later and t2Batch past its draw, and the conditions after these calls are reached. The
state of the calls over the links is written by hand too: no chain has made it. That only one
condition is false in a changed state is by the choice of the change.

No proof is read. The terms are explained at the head of OnBytes/Model/Trees.lean and in
OnBytes/Model/Tail.lean (the docstring of HTailF2 says where). The file is not imported by the
program.
-/
import OnBytes.Model.TestTailNames
import OnBytes.Model.TestTreesConditions

namespace OnBytes.Model.TestTreesChannel

open OnBytes OnBytes.Model

/-! ## rootInH -/

/-- An oracle message of one main row over the base field, under code 0, with one answer. -/
def oneRow : OracleShape := { code := 0, mainRows := 1, mainDeg := 1, answers := 1 }

/-- One link of two oracle messages, at the moments 0 and 1. -/
def shape2 : Params.ReqShape :=
  { (default : Params.ReqShape) with
    link := [{ plain := 0, messages := [
      { shape := oneRow, leafClass := 0, moment := 0, life := 0 },
      { shape := oneRow, leafClass := 0, moment := 1, life := 0 }] }] }

/-- The array A in the first message, B and C in the second. -/
def layout2 : Params.ReqLayout :=
  { link := [[{ name := "A", message := 0, sizeI := 1, sizeC := 1, blocks := [] },
              { name := "B", message := 1, sizeI := 1, sizeC := 1, blocks := [] },
              { name := "C", message := 1, sizeI := 1, sizeC := 1, blocks := [] }]] }

/-- The state of the calls after the link's first moment. -/
def afterFirst : ChainCheck :=
  { frame := { shape := shape2, groups := #[], next := .laterOrClose, moment := 1, group := 0 },
    rows := { layout := layout2 }, inLink := true, moments := 1 }

/-- A dry channel with the two rounds in which one message is sent and sampled, and a statement with
one code and one group. -/
def twoRounds : Ctx :=
  { ch := { dry := true,
            entries := [{ name := "SEND seed", drawE := 3, drawNZ := 1 },
                        { name := "SEND answer" }] },
    st := { codes := { base := #[{ logN := 4, ell := 4, r := 1 }] }, groups := #[{ code := 0 }] } }

/-- The link after its first moment. -/
def link2 : LinkCtx :=
  { check := afterFirst, link := 0, arrayOf := #[(0, "A"), (0, "B"), (0, "C")],
    list := { link := true, planned := true, nt := #[{}, {}, {}] }, moments := 1 }

/-- The sub-proof's three arrays. -/
def fork2 : Fork :=
  { trees := #[{ name := "A", R := 1, K := 1 }, { name := "B", R := 1, K := 1 },
               { name := "C", R := 1, K := 1 }] }

/-- The name under which rootInH fails; "" if it does not fail. -/
def rootName (trees : List Nat) (onL : LinkCtx → LinkCtx := id) (onF : Fork → Fork := id) :
    String :=
  match (rootInH trees (onL link2)) (onF fork2) twoRounds with
  | .ok _ => ""
  | .error e => e.name

/-- True if rootInH goes through, counts one moment more and leaves exactly these arrays marked as
committed. -/
def after (trees : List Nat) (marked : Array Bool) : Bool :=
  match (rootInH trees link2) fork2 twoRounds with
  | .ok x => x.1.2.trees.map (·.root.isSome) == marked && x.1.1.2.moments == 2
  | .error _ => false

-- The two arrays of the second moment, in either order.
#guard rootName [1, 2] == "" && rootName [2, 1] == ""
#guard after [1, 2] #[false, true, true]
-- An array of the first moment in the place of one of the second.
#guard rootName [1, 0] == "plan-link"
-- An array that is committed already.
#guard rootName [1, 2] id (fun F => F.rootTaken 2 0) == "plan-link"
-- One array twice, the other not at all.
#guard rootName [1, 1] == "plan-link"
-- An array that another link has committed to, under a name that the layout has here.
#guard rootName [1, 2] (fun L => { L with arrayOf := #[(0, "A"), (0, "B"), (7, "C")] }) ==
  "plan-link"
-- Fewer arrays than the layout has at the moment; none; an index that is no array's.
#guard rootName [1] == "plan-link" && rootName [] == "plan-link" && rootName [1, 9] == "plan-link"

/-! ## t2Batch -/

/-- A dry channel whose plan has one round: that of the batching element. -/
def oneRound : Ctx := { ch := { dry := true, entries := [{ name := "BAT-sigma", drawE := 1 }] } }

/-- The sub-proof's state before t2Batch, with three slots. -/
def start3 : Fork := { TestTailNames.forkAtDoor with ns := 3, thetaDrawnF := false }

/-- The name under which t2Batch fails from the state F; "" if it does not fail. -/
def batchName (F : Fork) : String :=
  match (t2Batch 3 TestTailNames.beforeBatch) F oneRound with
  | .ok _ => ""
  | .error e => e.name

/-- True if t2Batch goes through from the state F, leaves every virtual row with its K column
weights, has the batching element drawn and no claim's weight handed out, and records in the link
that it has run, with the number of slots. -/
def batched (F : Fork) : Bool :=
  match (t2Batch 3 TestTailNames.beforeBatch) F oneRound with
  | .ok x =>
    let G := x.1.2
    let L := x.1.1.2
    (G.trees.all fun X => X.rows.all fun r => r.L.size == X.K) && G.thetaDrawnF &&
      G.kapMapF == #[false] && L.handed && L.list.used == 3
  | .error _ => false

#guard batchName start3 == ""
-- The plan has no claim.
#guard batchName { start3 with planClaimsF := 0 } == "internal-f-draws"
-- The rows come without column weights, as a plan keeps them (Fork.trimL).
#guard batched start3.trimL

/-! ## doorH: the list is longer than the arrays -/

/-- The state of TestTailNames with a second array in the layout, Z, of no rows and no columns. A
layout that ChainCheck.start has admitted has no such array. -/
def checkZ : ChainCheck :=
  { TestTailNames.check with rows := { layout := { link := [[
      { name := "A", message := 0, sizeI := 6, sizeC := 1, blocks := [] },
      { name := "Z", message := 0, sizeI := 0, sizeC := 0, blocks := [] }]] } } }

-- The list has two records, the state one array. doorH reads the missing array as one of no rows
-- and no columns, the size that this layout gives Z, so the comparison with the layout would pass.
-- Of the conditions that fail as "refused", only "the list is not longer than the arrays" is false.
#guard TestTailNames.doorName (fun L => { L with
    check := checkZ, arrayOf := #[(0, "A"), (0, "Z")],
    list := { L.list with nt := #[{}, {}] } }) == "refused"

/-! ## EqRun.next recomputes no more than it says -/

/-- The run at index 0 with the product of the first three factors overwritten by 0. -/
def marked : EqRun :=
  let r := EqRun.start TestTreesConditions.point 0
  { r with pre := r.pre.set! 3 zeroE }

-- The step from 0 to 1 changes bit 0 alone, so only the last product is computed again.
#guard marked.next.pre.getD 3 oneE == zeroE

/-! ## States whose lists do not fit each other

shapeF and drawMatrixF are the only writers of NM, mats, off, gtTree, cfF and cfFirst, and they keep
these fields in step. None of the states here can arise in a run. -/

/-- One matrix of one cell. -/
def cell : TMat := { name := "x", m := 1, k := 1 }

/-- A state that holds a matrix and counts none. -/
def uncounted : HTailF2 := { NM := 0, mats := #[cell], off := #[0], mz := 1 }

-- zzCol and tabAt refuse a matrix from NM on, though the list holds one there.
#guard uncounted.zzCol 0 0 0 == none
#guard uncounted.tabAt { mat := 0, len := 1 } 0 0 == none
-- A matrix without a recorded first row counts from 0.
#guard ({ NM := 1, mats := #[cell], off := #[], mz := 1 } : HTailF2).zzCol 0 0 0 == some 0
-- An entry after the end of the drawn matrix counts as 0.
#guard HTailF2.foldColumn #[] 0 1 #[oneE] == zeroE

/-- One matrix of one column without a recorded first column; the drawn entries 1 and -1. -/
def noFirstColumn : HTailF2 where
  tau := 1
  NM := 1
  mats := #[cell]
  cfFirst := #[]
  cfF := #[1, -1]
  vt := #[oneE]
  vp := #[oneE]
  gamX := #[#[]]
  gamV := #[#[]]

-- It counts from column 0: entry 1, not entry -1.
#guard (noFirstColumn.foldSums 0).any fun tl => tl.gamX == #[#[oneE]]
-- A matrix without a recorded array is taken to be in array 0, here U3, whose shape does not fit.
#guard
  match (({} : HTailF2).shape #[{ name := "x", m := 6, k := 2 }] #[none] #[]
      #[false, false, true, false] 160).bind fun tl =>
      ({ tl with gtTree := #[] } : HTailF2).addTrees {} {} #[0, 0, 4] #[] 100 128 with
  | .error e => e == "internal-t2f-map"
  | .ok _ => false

end OnBytes.Model.TestTreesChannel
