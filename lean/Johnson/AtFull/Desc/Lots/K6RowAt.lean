-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/Lots/K6RowAt.lean: THE ROW OF K6's LOT (P4.k6Lot) FROM EQUATIONS OF FIELDS WITH
WRITTEN VALUES, AND THE CLOSED FACTS BENEATH IT, BY EVALUATION IN LEAN'S KERNEL AT THE WRITTEN
VALUES OF THE FULL SIZE.
WHAT IT DOES NOT SHOW, FIRST. THAT ANY Z AND G MEET k6_row_written's HYPOTHESES: OWED TO OTHERS, BY
NAME: the number of built segments · the last one's name "H", its one foreign array (K6RowFt.lean
has it for the PLAN's record; that the built segment bears the plan's is owed), that array's owner
in arrayOf · the owner's name "G11" · the written table of steps and entries · the records Numbers
and Stream at G.W (in the goals' scope, at the library's publicOf: numbers_in_scope,
stream_in_scope). NO EXAMPLE OF THE HEAD IS SHOWN IN THIS FILE; two, at storedPublicFiles and at zGap alone, are
AtFullSide.Top.headMember_zFull and headMember_zGap, whose own Limits say what they are worth.
Nothing on soundness. WHAT THE ROW IS BLIND TO: the block's decision · the rounds' entries · the
test on the request · the runs' functions · which messages 73 and 67 are.
ON THE COLUMN planOk. Six numbers of the parameter file are free in the goals' scope (MF, KF, epsF,
C, theta, cap): so that column is no closed fact of fixed sizes: it comes of the record Numbers'
ranges, by theorems. NO KERNEL FACT ON IT STANDS HERE: one at a hand-written copy of a stored set's
shape would meet neither the lot nor G.W.

Main names (namespace Johnson.AtFull.Lots).
  k6Msgs_written [kernel]: at the written table of steps and entries the step "H.1.call" sends
      message 73, and "G11.0.call" message 67.
  k6Msgs_false [kernel]: THE TEST CAN SAY NO: four bent sentences evaluate to false: 74 · the step
      "H.0.call" · the step "G10.0.call" · a name that the table has not.
  k6Msgs_at: so at every public part with these two lists.
  ok_of_numbers, laidOk_of_numbers: the two tests on the plan from the records Numbers and
      Stream (Johnson/Goal/Meaning/HeadCondScope.lean: equations of fields with written values;
      ranges for the six free numbers): ok_in_scope's and laidOk_in_scope's own last
      lines, at these records in the place of the scope.
  k6_row_written: THE ROW: lotSk G (P4.k6Lot Z) = k6LotW from equations of fields with written
      values (and these ranges) alone.
  k6_written, k6_written_false [kernel]: A CROSS-CHECK THAT NOBODY SPENDS: row 341 of the written
      table cutFirstFull (Johnson/Desc/Ok/PlanWritten/CutLit.lean) is the written skeleton's row
      under the place's name "H:4" (by rowIsB, H1Row.lean); three bent ones are not. THAT TABLE WAS
      PRINTED OFF THE
      DESCRIPTION, SO OFF THIS VERY LOT: NO INDEPENDENT WITNESS.
It stands over: the laws on skeletons
(Johnson/Desc/ProofFile/Law/Skel/) · rootsOf and the written entries (Johnson/Road/K4/K4SentAt.lean,
Johnson/AtFull/K4Sent/Written.lean) · the written table of steps
(Johnson/AtFull/Cut/CutWrittenLit.lean: the constant Johnson.AtFull.Cut.cutWritten).

-/
import Johnson.AtFull.Desc.Lots.K8MsgsOn
import Johnson.AtFull.K4Sent.Written
import Johnson.AtFull.Cut.CutWrittenLit
import Johnson.AtFull.Desc.Lots.K6Row
import Johnson.Goal.Meaning.HeadCondScope
import Johnson.AtFull.Desc.Lots.H1Row

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Lots

open Johnson.AtFull.Cut (cutWritten)
open Johnson.AtFull.K4Sent (esWritten)
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law.InScope (Numbers Stream planOk_of_numbers
    laid_of_numbers)
open ProofFile.Sk (lotSk)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **The two steps' messages at the written values.** -/
theorem k6Msgs_written : (k8MsgsOn cutWritten esWritten "H.1.call" == [73] &&
    k8MsgsOn cutWritten esWritten "G11.0.call" == [67]) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **The test can say no.** -/
theorem k6Msgs_false : (k8MsgsOn cutWritten esWritten "H.1.call" == [74] ||
    k8MsgsOn cutWritten esWritten "H.0.call" == [73] ||
    k8MsgsOn cutWritten esWritten "G10.0.call" == [67] ||
    !(k8MsgsOn cutWritten esWritten "H.1.nowhere").isEmpty) = false := by
  decide +kernel

/-- So at every public part with the written table of steps and entries. -/
theorem k6Msgs_at {Z : ProofFile.Pub} (hc : Z.cuts = cutWritten)
    (he : Z.D.1.map (·.entry) = esWritten) :
    ProofFile.k8Msgs Z "H.1.call" = [73] ∧ ProofFile.k8Msgs Z "G11.0.call" = [67] := by
  have h := k6Msgs_written
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h
  rw [k8Msgs_eq, k8Msgs_eq, hc, he]
  exact h

/-! ## The two tests on the plan, from the numbers -/

/-- The kind's test on the plan, from the record of numbers: the last three lines of
ok_in_scope, at that record in the place of the scope. -/
theorem ok_of_numbers {X : OnBytes.Model.Verify.Public} (N : Numbers X) (w : Nat) :
    (parOf X.hS w).ok = true := by
  have hls : X.hS.ls = 6 := by unfold OnBytes.Model.Head.Shape.ls; rw [N.la, N.lt]
  exact @planOk_of_numbers (parOf X.hS w).sizes (parOf X.hS w).policy X.hS.tabS N.lt hls N.d N.V
    N.sh N.F N.sT N.m1 N.m2 N.m3 N.k1 N.k2 N.k3 N.e1 N.e2 N.c1 N.c2 N.c3

/-- The tests on how the cells are laid, from the two records: laidOk_in_scope's own
lines, at these records in the place of the scope. -/
theorem laidOk_of_numbers {X : OnBytes.Model.Verify.Public} (N : Numbers X) (St : Stream X) :
    laidOk X = true := by
  have hls : X.hS.ls = 6 := by unfold OnBytes.Model.Head.Shape.ls; rw [N.la, N.lt]
  refine @laid_of_numbers (parOf X.hS 0).sizes (parOf X.hS 0).policy
    (laidAt X.hS (OnBytes.Model.Verify.borderOf X.y))
    N.lt hls N.d N.V N.sh N.c1 N.c2 N.la N.lPd N.XL St.nl St.off ?_ ?_
  · show (OnBytes.Model.Verify.borderOf X.y).cnt * (OnBytes.Model.Verify.borderOf X.y).J = 5120
    rw [St.cnt, St.J]
  · show 400 ≤ (OnBytes.Model.Verify.borderOf X.y).kxb *
      ((OnBytes.Model.Verify.borderOf X.y).mxb / 2 ^ X.hS.la)
    rw [St.kxb, St.mxb, N.la]
    decide

/-! ## The row -/

/-- **THE ROW**: from equations of fields with written values, and, for the six numbers that are
free in the goals' scope, their ranges (the record Numbers). -/
theorem k6_row_written {Z : ProofFile.Pub} {G : ProofFile.Ground} {X Y : OnBytes.Model.Stages.LinkH}
    {iU3 t l₀ : Nat} {nm : String} (hsz : G.built.size = 25)
    (hU : G.W.H.tl.ix.U.getD 2 none = some iU3) (N : Numbers G.W) (St : Stream G.W)
    (hc : Z.cuts = cutWritten) (he : Z.D.1.map (·.entry) = esWritten)
    (hX : G.built.back? = some X) (nX : X.name = "H") (hFT : X.tl.ix.FT.toList = [t])
    (hborn : X.arrayOf[t]? = some (l₀, nm)) (hY : G.built[l₀]? = some Y) (nY : Y.name = "G11") :
    lotSk G (P4.k6Lot Z) = k6LotW :=
  k6_row_at
    { size := hsz, third := ⟨iU3, hU⟩, lt := N.lt, d := N.d, ok := ok_of_numbers N _
      laid := laidOk_of_numbers N St
      before := ⟨X, Y, t, l₀, nm, hX, hFT, hborn, hY, nX, nY, (k6Msgs_at hc he).1,
        (k6Msgs_at hc he).2⟩ }

/-! ## A cross-check against the written table of the first chain -/

set_option maxRecDepth 1000000 in
/-- **Row number 341 of the written table cutFirstFull is the written skeleton's row**, under the
place's name. A cross-check: nobody spends it; and that table was printed off the description, so
off this very lot: no independent witness. -/
theorem k6_written : rowIsB 341 { k6SkW with name := "H:4" } = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **It can say no**: 81 rounds; the two messages exchanged; the row in front. -/
theorem k6_written_false : (rowIsB 341 { k6SkW with name := "H:4", nRounds := 81 } ||
    rowIsB 341 { k6SkW with name := "H:4", before := [(1, 67), (1, 73)] } ||
    rowIsB 340 { k6SkW with name := "H:4" }) = false := by
  decide +kernel

end Johnson.AtFull.Lots

#print axioms Johnson.AtFull.Lots.k6Msgs_written
#print axioms Johnson.AtFull.Lots.k6Msgs_false
#print axioms Johnson.AtFull.Lots.k6Msgs_at
#print axioms Johnson.AtFull.Lots.ok_of_numbers
#print axioms Johnson.AtFull.Lots.laidOk_of_numbers
#print axioms Johnson.AtFull.Lots.k6_row_written
#print axioms Johnson.AtFull.Lots.k6_written
#print axioms Johnson.AtFull.Lots.k6_written_false
