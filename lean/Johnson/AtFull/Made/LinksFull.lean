-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Made/LinksFull.lean: THE VALUES THAT `buildLinksH`'s TESTS READ, AT THE FULL SIZE,
WRITTEN DOWN: the 25 segments' views (Johnson/AtFull/Made/LinksView.lean) and what the 25 segments
declare; AND SIX OF THE EIGHT TESTS DECIDED AT THEM BY LEAN's KERNEL, each with a negative test.
Definitions with code and theorems.
  `arraysRel`, `viewAt`, `viewFull`: a segment's view by its sort (the first layers' segment,
    attention's, the other layers', the head's): fv, gid, ns; arrayOf written relative to the
    segment's own number (four values). `momentsAt`, `nameAt`, `declaredFull`: the declared arrays
    (four values of the moments).
  `idsFull`: the sub-proofs' identifiers in the segments' order.
  `tableRows_full` (h₅), `numbersB_full` (h₁₁'s condition), `heldB_full` (h₄'s condition, at
    `ReqLit.shapeFull` and `Johnson.G.layoutFull`), `reqOk_full` (h₈, at
    `Johnson.G.proofCodesWritten`), `wsTests_full` (h₆, h₇: at what `wsLayOf` returns at the full
    size's ten numbers). Beside each: a bend at which the same test says no.
WHENCE THE VALUES: a run (a print of the planner's own values at `VerifierAndGoals.storedPublicFiles`, by name: no
theorem); a second run has held `viewFull`, `declaredFull`, `idsFull` and the codes against the
planner's own as equations: true. THAT THEY ARE THE PLANNER's IS PROVED NOWHERE HERE: it is a
hypothesis of Johnson/AtFull/Made/BuiltAtFull.lean.
Limits. Closed facts at written values. `linksFit` (h₁₀) is not decided here (another file's closed
fact); `listedFits` (h₉) needs no decision (no position is listed). No soundness is claimed.

-/
import Johnson.AtFull.Made.LinksView
import Johnson.Desc.ReqLit.Full
import Johnson.G.LayoutLit
import Johnson.G.SendsWritten
import Johnson.Top.H.LooksAtPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Model OnBytes.Model.Stages OnBytes.Params

/-! ## 1 The values -/

/-- The sort of segment l: 0 the first layers' segment, 1 attention's, 2 the other layers', 3 the
head's. -/
def sortAt (l : Nat) : Nat :=
  if l == 0 then 0 else if l == 24 then 3 else if l % 2 == 1 then 1 else 2

/-- For each array of a segment's list: how many segments earlier it is committed to, and its name
there. -/
def arraysRel : Nat → List (Nat × String)
  | 0 => [(0, "U3"), (0, "M0"), (0, "M1"), (0, "M2"), (0, "M3"), (0, "M4"), (0, "M5"), (0, "M8"),
      (0, "M6"), (0, "M7"), (0, "ZZ"), (0, "BZ")]
  | 1 => [(0, "U3"), (0, "M0"), (0, "M1"), (0, "M2"), (0, "M3"), (0, "ZZ"), (0, "BZ"), (1, "M6")]
  | 2 => [(0, "U3"), (0, "M0"), (0, "M1"), (0, "M2"), (0, "M3"), (0, "M4"), (0, "M5"), (0, "M6"),
      (0, "M7"), (0, "ZZ"), (0, "BZ"), (2, "M7")]
  | _ => [(0, "U3"), (0, "M0"), (0, "M1"), (0, "M2"), (0, "M3"), (0, "M4"), (0, "M5"), (0, "M6"),
      (0, "ZZ"), (0, "BZ"), (2, "M7")]

/-- The scalars that a segment's sub-proof sends. -/
def nsOfSort : Nat → Nat
  | 0 => 4059
  | 1 => 4190
  | 2 => 4058
  | _ => 3570

/-- Segment l's view. -/
def viewAt (l : Nat) : LinkView :=
  (l % 2 == 0, if l % 2 == 0 then l / 2 + 1 else 13 + (l + 1) / 2, nsOfSort (sortAt l),
    ((arraysRel (sortAt l)).map fun x => (l - x.1, x.2)).toArray)

/-- **The 25 views.** -/
def viewFull : List LinkView := (List.range 25).map viewAt

/-- The identifiers, in the segments' order. -/
def idsFull : List Nat := viewFull.map (·.2.1)

/-- What a segment declares, moment by moment. -/
def momentsAt : Nat → Array (Array FrameArray)
  | 0 => #[#[⟨"M0", 21846, 5990, false, 0⟩, ⟨"M1", 21846, 5990, false, 0⟩,
        ⟨"M2", 21846, 5990, false, 0⟩, ⟨"M3", 10923, 3200, false, 0⟩, ⟨"M4", 2731, 324, false, 0⟩,
        ⟨"M5", 21846, 256, false, 0⟩, ⟨"M8", 21846, 400, false, 0⟩, ⟨"M6", 21846, 1536, false, 1⟩,
        ⟨"M7", 21846, 400, false, 2⟩],
      #[⟨"U3", 1, 407626, true, 0⟩],
      #[⟨"ZZ", 128, 999424, false, 0⟩, ⟨"BZ", 32, 2048, false, 0⟩]]
  | 1 => #[#[⟨"M0", 21846, 7200, false, 0⟩, ⟨"M1", 2731, 360, false, 0⟩,
        ⟨"M2", 21846, 640, false, 0⟩, ⟨"M3", 5462, 512, false, 0⟩],
      #[⟨"U3", 1, 60640, true, 0⟩],
      #[⟨"ZZ", 128, 442368, false, 0⟩, ⟨"BZ", 32, 2048, false, 0⟩]]
  | 2 => #[#[⟨"M0", 21846, 5990, false, 0⟩, ⟨"M1", 21846, 5990, false, 0⟩,
        ⟨"M2", 21846, 5990, false, 0⟩, ⟨"M3", 10923, 3200, false, 0⟩, ⟨"M4", 2731, 324, false, 0⟩,
        ⟨"M5", 21846, 256, false, 0⟩, ⟨"M6", 21846, 1536, false, 1⟩,
        ⟨"M7", 21846, 400, false, 2⟩],
      #[⟨"U3", 1, 407226, true, 0⟩],
      #[⟨"ZZ", 128, 999424, false, 0⟩, ⟨"BZ", 32, 2048, false, 0⟩]]
  | _ => #[#[⟨"M0", 21846, 4816, false, 0⟩, ⟨"M1", 21846, 4816, false, 0⟩,
        ⟨"M2", 21846, 4816, false, 0⟩, ⟨"M3", 21846, 4816, false, 0⟩, ⟨"M4", 5462, 640, false, 0⟩,
        ⟨"M5", 2731, 15, false, 0⟩, ⟨"M6", 10923, 384, false, 0⟩],
      #[⟨"U3", 1, 61680, true, 0⟩],
      #[⟨"ZZ", 128, 770048, false, 0⟩, ⟨"BZ", 32, 2048, false, 0⟩]]

/-- A segment's name. -/
def nameAt (l : Nat) : String :=
  if l == 24 then "H" else (if l % 2 == 0 then "G" else "A") ++ toString (l / 2)

/-- **What the 25 segments declare.** -/
def declaredFull : Array FrameLink :=
  ((List.range 25).map fun l => (⟨nameAt l, momentsAt (sortAt l)⟩ : FrameLink)).toArray

/-! ## 2 The tests' conditions, as Bools of what they read -/

/-- `numbersHeld`'s condition. -/
def numbersB (links : Array LinkH) (shape : ReqShape) (pending : Nat) (ids : List Nat) : Bool :=
  shape.link.map (·.plain) == List.replicate (links.size - 1) 0 ++ [1] &&
    pending == onTable links && ids == links.toList.map (·.gid)

/-- `heldAgainst`'s condition. -/
def heldB (declared : Array FrameLink) (shape : ReqShape) (layout : ReqLayout) : Bool :=
  declared.size == shape.link.length && declared.size == layout.link.length &&
    ((zipT declared.toList (zipT shape.link layout.link)).all fun x => linkHeld x.1 x.2.1 x.2.2)

/-- The two tests on the committed table's layout, at what `wsLayOf` returns. -/
def wsTests (w : WsShape) (p3 : Bool) (lkW rows kCol : Nat) : Bool :=
  match wsLayOf w p3 lkW with
  | .ok Y =>
    !(Y.U.any fun u => u.nlw == 4 && u.X != 12) && wfLayoutOk Y && rows == Y.m0 && kCol == Y.lk
  | .error _ => false

/-! ## 3 The decisions -/

theorem viewFull_length : viewFull.length = 25 := by decide +kernel

theorem onTable_full : onTable (viewFull.map ofView).toArray = 13 := by decide +kernel

/-- **h₅.** -/
theorem tableRows_full : tableRows (viewFull.map ofView).toArray 12 = .ok () := by
  unfold tableRows
  rw [onTable_full]
  rfl

/-- A negative test: at one group more it refuses. -/
theorem tableRows_bend : tableRows (viewFull.map ofView).toArray 13 ≠ .ok () := by
  unfold tableRows
  rw [onTable_full]
  exact fun h => nomatch h

set_option maxRecDepth 100000 in
/-- **h₁₁'s condition.** -/
theorem numbersB_full : numbersB (viewFull.map ofView).toArray
    VerifiableInference.Desc.ReqLit.shapeFull 13 idsFull = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- A negative test: at one pending row more. -/
theorem numbersB_bend : numbersB (viewFull.map ofView).toArray
    VerifiableInference.Desc.ReqLit.shapeFull 14 idsFull = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **h₄'s condition.** -/
theorem heldB_full : heldB declaredFull VerifiableInference.Desc.ReqLit.shapeFull
    Johnson.G.layoutFull = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: at one declared segment fewer. -/
theorem heldB_bend : heldB declaredFull.pop VerifiableInference.Desc.ReqLit.shapeFull
    Johnson.G.layoutFull = false := by decide +kernel

/-- What is declared, with the first array of the first segment one row higher. -/
def declaredBent : Array FrameLink :=
  declaredFull.modify 0 fun D =>
    { D with
      moment := D.moment.modify 0 fun M => M.modify 0 fun a => { a with rows := a.rows + 1 } }

set_option maxRecDepth 1000000 in
/-- A negative test on the weighty conjunct: one declared array's rows one higher. -/
theorem heldB_bend_rows : heldB declaredBent VerifiableInference.Desc.ReqLit.shapeFull
    Johnson.G.layoutFull = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **h₈.** -/
theorem reqOk_full : reqOk Johnson.G.proofCodesWritten
    VerifiableInference.Desc.ReqLit.shapeFull = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: at no mask code. -/
theorem reqOk_bend : reqOk { Johnson.G.proofCodesWritten with mask := #[] }
    VerifiableInference.Desc.ReqLit.shapeFull = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **h₆ and h₇'s conditions.** -/
theorem wsTests_full : wsTests Lk6.AtPlan.wsFull true recordLines.blockLog 3076096 18 = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: at one column bit more. -/
theorem wsTests_bend : wsTests Lk6.AtPlan.wsFull true recordLines.blockLog 3076096 19 = false := by
  decide +kernel

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.viewFull_length
#print axioms Johnson.AtFull.Made.onTable_full
#print axioms Johnson.AtFull.Made.tableRows_full
#print axioms Johnson.AtFull.Made.tableRows_bend
#print axioms Johnson.AtFull.Made.numbersB_full
#print axioms Johnson.AtFull.Made.numbersB_bend
#print axioms Johnson.AtFull.Made.heldB_full
#print axioms Johnson.AtFull.Made.heldB_bend
#print axioms Johnson.AtFull.Made.heldB_bend_rows
#print axioms Johnson.AtFull.Made.reqOk_full
#print axioms Johnson.AtFull.Made.reqOk_bend
#print axioms Johnson.AtFull.Made.wsTests_full
#print axioms Johnson.AtFull.Made.wsTests_bend
