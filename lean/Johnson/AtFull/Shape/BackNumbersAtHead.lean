-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/BackNumbersAtHead.lean: UNDER THE HYPOTHESIS `P5J.AtMg` THE NUMBERS OF THE KIND
K13 ON THE FIRST CHAIN (the library's "members' batching"), `K13.whereOf Zp`
(Johnson/Desc/ProofFile/Lot/K13.lean), ARE A WRITTEN RECORD: A CLOSED TERM. With it: six fields of
the first chain's parameters, and the chain's two numbers. The proofs only combine laws of the
library; nothing is evaluated here.

Words. `P5J.AtMg` (Johnson/P5J/AtMg.lean) is the library's hypothesis at the full size; the library
calls it "the head". Below: the hypothesis.

Purpose. A table of steps on shapes, one for each of the 358 blocks in the first chain's blocksInOrder list,
is to be evaluated at closed terms. It is not in the library yet, so nothing about what it reads is
claimed here. These equations are meant for its steps at the numbers 355 and 356.

How. The record K13.Where has eight fields (Johnson/Desc/K13/Kind.lean). whereOf sets seven of them
and leaves reply at its default, true: so four are literals (chain, piece, pieceRows, reply). rows
and lin are fields of Zp.first: in scope, where the entry test on what the planner configured
accepts, they are the written ones (`first_written_in_scope`,
Johnson/Goal/Numbers/MadeInScope.lean). work, at the batching's first three rounds, is (0, 0, 0),
and the batching starts at round 48270 (`Written`, Johnson/Goal/Numbers/WrittenAtZ.lean;
`written_of_made`, Johnson/Desc/K14/Law/SharedConstCodesMade.lean). sent, what the chain has sent
before that round, is a sum over the declared rounds' entries, which are the written list's
(`Written354.entries`, `written354_of_pins`, Johnson/Loose/H2K12/ClosedOfPins354.lean). The
hypothesis gives the scope, that Zp is what `ProofFile.pureRoad.pub`
(Johnson/Desc/ProofFile/OnlineDescriptionPublicPart.lean) returns at the three public files (its field laid.pub), the
entry test's accept (`AtMg.pins`) and `LaidAt.laidPOf`, which the last two laws take (both in
Johnson/P5T/FenceAtMg.lean).

Main names.
* `pinned_at_head`: the entry test's accept, in the form that the laws take. `first_at_head`:
  FirstWritten Zp.first. `par_at_head`: Zp.P.
* `where13W`: the written record. **`where13_at_head`**: K13.whereOf Zp = where13W.

Limits. UNDER THE HYPOTHESIS. That the hypothesis can be met is shown only for `P5J.AtMgA`, which
extends AtMg, at the hash OnBytes.secondHashFunction and at two named sets of public files (`headMember_zFull`,
AtFullSide/Top/HeadMemberAtFull.lean; `headMember_zGap`, AtFullSide/Top/HeadMemberAtGap.lean); by
the first file's own words the example's weights are synthetic. where13W's field sent is a closed
sum over 48,270 written entries: NOT EVALUATED HERE. Of where13W's fields the entry tests compare
rows, lin and the entries beneath sent with written values; work and the round 48270 come by
theorem. Where the written values come from is said in their own files. Three fields of Zp.first
(given, identifiers, more) are not written: they depend on the public files' digest or are not
fixed. Only the full-size parameters are covered. Nothing on soundness, completeness or hiding.
-/
import Johnson.Loose.H2K12.ClosedOfPins354
import Johnson.Desc.K14.Law.SharedConstCodesMade
import Johnson.P5T.FenceAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open VerifiableInference
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.K13 (Where whereOf fromOf)
open VerifiableInference.PlanWritten (pinnedAt_of_row FirstWritten proofSizedFull)
open VerifiableInference.PlanWritten.Joined (first_written_in_scope par_in_scope)
open OnBytes.Maker (WholeD)
open P5J (AtMg)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- Under the hypothesis the entry test on what the planner configured accepts, in the form that
the laws take. -/
theorem pinned_at_head (h : AtMg o Z D r Zp Np cF) :
    PlanWritten.madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true :=
  pinnedAt_of_row (Z := Zp) (by rw [h.pins.1, Bool.or_true])

/-- **Under the hypothesis six fields of the first chain's parameters are the written ones.** -/
theorem first_at_head (h : AtMg o Z D r Zp Np cF) : FirstWritten Zp.first :=
  first_written_in_scope h.scope h.laid.pub (pinned_at_head h)

/-- **Under the hypothesis the first chain's two numbers are written.** -/
theorem par_at_head (h : AtMg o Z D r Zp Np cF) :
    Zp.P = ⟨0, proofSizedFull.request.answers⟩ :=
  par_in_scope h.scope h.laid.pub (pinned_at_head h)

/-- The numbers of the members' batching on the first chain (the kind K13), written. Its last field
is a closed sum, not evaluated here: the roots of the written entries in front of round 48270. -/
def where13W : Where :=
  { chain := 1, piece := 3, pieceRows := 4, rows := 13, lin := proofSizedFull.batch.shape,
    work := (0, 0, 0), sent := ((P5T.esFull.1.take 48270).map (·.roots)).sum }

/-- **UNDER THE HYPOTHESIS THE NUMBERS OF THE MEMBERS' BATCHING ARE THE WRITTEN ONES.** -/
theorem where13_at_head (h : AtMg o Z D r Zp Np cF) :
    whereOf Zp = where13W := by
  obtain ⟨x, -, W⟩ := _root_.Desc.K14.Law.Sh.written_of_made h.scope h.laid.pub (pinned_at_head h)
    h.laid.laidPOf
  have W4 := H2K12.written354_of_pins h.scope h.laid.pub h.pins.1 h.laid.laidPOf
  obtain ⟨-, f2, -, f4, -, -⟩ := first_at_head h
  have e : whereOf Zp =
      { chain := 1, piece := 3, pieceRows := 4, rows := Zp.first.pendingRows, lin := Zp.first.lin,
        work := (whereOf Zp).work, sent := ((Zp.D.1.take (fromOf Zp)).map (·.entry.roots)).sum } :=
    rfl
  have s : (Zp.D.1.take 48270).map (·.entry.roots) = (P5T.esFull.1.take 48270).map (·.roots) := by
    rw [← W4.entries, ← List.map_take, List.map_map]
    rfl
  rw [e, f2, f4, W.work, W.start, s]
  rfl

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.pinned_at_head
#print axioms Johnson.AtFull.Shape.first_at_head
#print axioms Johnson.AtFull.Shape.par_at_head
#print axioms Johnson.AtFull.Shape.where13_at_head
