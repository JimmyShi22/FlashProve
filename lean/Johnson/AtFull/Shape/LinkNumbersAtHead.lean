-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/LinkNumbersAtHead.lean: UNDER THE HYPOTHESIS `P5J.AtMg` THE NUMBERS OF THE
BATCHING (the kind K9) AND OF THE CLOSING (the kind K10) AT A SEGMENT OF THE FIRST CHAIN, `IM.k9At
Zp l` (Johnson/IMR/LinkSeat.lean) AND `ProofFile.k10Par Zp (ProofFile.k9Stretches Zp) p`
(Johnson/Desc/ProofFile/Lot/K9.lean), ARE THE LIBRARY's READERS ON ENTRIES AT WRITTEN VALUES: CLOSED
TERMS. With them: the table of steps, the places that have rounds, the declared rounds' entries. The
proofs only combine laws of the library; nothing is evaluated here.

Words. `P5J.AtMg` (Johnson/P5J/AtMg.lean) is the library's hypothesis at the full size; the library
calls it "the head". Below: the hypothesis.

Purpose. A table of steps on shapes, one for each of the 358 blocks in the first chain's flat list,
is to be evaluated at closed terms. It is not in the library yet, so nothing about what it reads is
claimed here. These equations are meant for its steps at the 25 batchings (the kind K9) and the 25
closings (the kind K10).

How. The two readers read Zp.cuts, Zp.D.1 and the groups of Zp.s₀'s frame. (1) The table of steps is
cutOf of the plan's own entries (`pubBy_cuts`, Johnson/Goal/Numbers/WrittenOfPins.lean); in scope,
under `LaidAt.laidPOf` (Johnson/P5T/FenceAtMg.lean), these entries are the written list's
(`plans_written`, Johnson/Goal/Numbers/PlanWrittenPlans.lean); at the written list cutOf returns
`cutWritten` (`cut_written`, Johnson/AtFull/Cut/CutAtWritten.lean: by Lean's kernel); its places are
`spotsWritten` (`spots_written`, Johnson/AtFull/Desc/SpotsWritten.lean). (2) Of a declared round the
readers use the entry alone: the library has versions of them on entries, and laws that tie each
version to the reader's own text (`stretched_entries`, `k9Where_eq`, `k10ParG_eq`,
Johnson/AtFull/Desc/Lots/K9RowAt.lean; `k10Par_eq`, K9Row.lean; `walk_eq`, `xsW`, `groupsW`,
K9RowWritten.lean: both in the same folder). The declared rounds' entries are the plan's own
(`pubBy_entries`). (3) The state before the first segment is the first record at Zp.first's codes,
shape and layout (`start?_first`, Johnson/Desc/First/EPubAtStart.lean), whose frame's groups are
reqGroups of the shape, which is the written one (`Written354.shape`).

Main names.
* `plan1_at_head`, **`cuts_at_head`** (Zp.cuts = cutWritten), `spots_at_head`, `entries_at_head`,
  `groups_at_head`.
* `stretches_of`: general: the stretches, each round cut to its entry, depend on the places and the
  entries alone. `stretches_at_head`: under the hypothesis they are `xsW`.
* **`k9At_at_head`**: IM.k9At Zp l = k9WhereE xsW l. **`k10_at_head`**: ProofFile.k10Par Zp
  (ProofFile.k9Stretches Zp) p = k10ParE groupsW xsW p.

Limits. UNDER THE HYPOTHESIS. That the hypothesis can be met is shown only for `P5J.AtMgA`, which
extends AtMg, at the hash OnBytes.secondHashFunction and at two named sets of public files (`headMember_zFull`,
AtFullSide/Top/HeadMemberAtFull.lean; `headMember_zGap`, AtFullSide/Top/HeadMemberAtGap.lean); by
the first file's own words the example's weights are synthetic. CLOSED TERMS, NOT NUMERALS: what
k9WhereE and k10ParE return at xsW is not evaluated here (the library's blocks_written and
batch_written, Johnson/AtFull/Desc/Lots/K9RowWritten.lean, evaluate tests on them by the kernel).
Beneath all written values here stands one list, the written rounds `dryProofFull`
(Johnson/G/DryProofLit.lean: written by a program from a print of Lean's evaluator, by its own
opening comment); cutWritten and spotsWritten are tied to it by Lean's kernel; under the hypothesis
the entry tests have compared the files' own rounds with it. The declared rounds themselves are not
written here: their entries are. Only the full-size parameters are covered. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Desc.Lots.K9RowWritten
import Johnson.AtFull.Cut.CutAtWritten
import Johnson.Goal.Numbers.WrittenOfPins
import Johnson.Goal.Numbers.PlanWrittenPlans
import Johnson.Loose.H2K12.ClosedOfPins354
import Johnson.IMR.LinkSeat
import Johnson.Desc.First.EPubAtStart
import Johnson.Desc.ProofFile.Law.PureMade
import Johnson.P5T.FenceAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open VerifiableInference
open VerifiableInference.Desc (Chain)
open VerifiableInference.PlanWritten (plans_written pubBy_entries)
open Johnson.AtFull.Cut (cutWritten cut_written)
open Johnson.AtFull.Desc (spotsWritten spots_written)
open Johnson.AtFull.Desc.Lots (toE stretchedE stretched_entries walk_eq esW xsW groupsW k9WhereE
  k10ParE k9Where_eq k10Par_eq k10ParG_eq)
open OnBytes.Maker (WholeD)
open P5J (AtMg)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- Under the hypothesis the first chain's plan's own entries are the written list's. -/
theorem plan1_at_head (h : AtMg o Z D r Zp Np cF) : Zp.plans.1 = esW := by
  obtain ⟨Z₁, hZ₁, e1, -, -⟩ := plans_written h.scope h.laid.laidPOf
  obtain rfl : Zp = Z₁ := Except.ok.inj (h.laid.pub.symm.trans hZ₁)
  exact e1

/-- **Under the hypothesis the table of steps is the written one.** -/
theorem cuts_at_head (h : AtMg o Z D r Zp Np cF) : Zp.cuts = cutWritten := by
  have c := _root_.Desc.K14.Law.pubBy_cuts h.laid.pub
  rw [plan1_at_head h] at c
  exact (Option.some.inj (cut_written.symm.trans c)).symm

/-- Under the hypothesis the first chain's declared rounds' entries are the written list's. -/
theorem entries_at_head (h : AtMg o Z D r Zp Np cF) : Zp.D.1.map (·.entry) = esW :=
  (pubBy_entries h.laid.pub).1.trans (plan1_at_head h)

/-- The stretches of the declared rounds, each round cut to its entry, depend on the places and on
the entries alone. General: no written value. -/
theorem stretches_of {Z₁ : ProofFile.Pub} {ps : List ProofFile.Spot} {es : List Fmt.Entry}
    (hs : ProofFile.spotsOf Z₁.cuts = some ps) (he : Z₁.D.1.map (·.entry) = es) :
    (ProofFile.k9Stretches Z₁).map toE = stretchedE ps es 0 := by
  unfold ProofFile.k9Stretches
  rw [hs, Option.map_some, Option.getD_some, stretched_entries, he]

/-- Under the hypothesis the places that have rounds are the written list. -/
theorem spots_at_head (h : AtMg o Z D r Zp Np cF) : ProofFile.spotsOf Zp.cuts = some spotsWritten := by
  rw [cuts_at_head h]
  exact spots_written

/-- **Under the hypothesis the stretches of the declared rounds, each round cut to its entry, are
the written ones.** -/
theorem stretches_at_head (h : AtMg o Z D r Zp Np cF) : (ProofFile.k9Stretches Zp).map toE = xsW :=
  (stretches_of (spots_at_head h) (entries_at_head h)).trans (walk_eq spotsWritten esW 0)

/-- Under the hypothesis the groups of the frame of the state before the first segment are the
written shape's. -/
theorem groups_at_head (h : AtMg o Z D r Zp Np cF) : Zp.s₀.check.frame.groups = groupsW := by
  have W4 := H2K12.written354_of_pins h.scope h.laid.pub h.pins.1 h.laid.laidPOf
  have h0 : VerifiableInference.Desc.First.S.start? (VerifiableInference.Desc.First.parP Zp.first)
      Zp.first.codes Zp.first.shape Zp.first.layout = some Zp.s₀ :=
    ProofFile.Law.pubBy_start (st := ProofFile.plainStarts) h.laid.pub
  rw [VerifiableInference.Desc.First.start?_first h0, W4.shape]
  rfl

/-- **UNDER THE HYPOTHESIS K9's NUMBERS AT A SEGMENT ARE WRITTEN.** -/
theorem k9At_at_head (h : AtMg o Z D r Zp Np cF) (l : Nat) : IM.k9At Zp l = k9WhereE xsW l := by
  show ProofFile.k9Where (ProofFile.k9Stretches Zp) l = _
  rw [k9Where_eq, stretches_at_head h]

/-- **UNDER THE HYPOTHESIS K10's NUMBERS AT A SEGMENT ARE WRITTEN.** -/
theorem k10_at_head (h : AtMg o Z D r Zp Np cF) (p : VerifiableInference.Desc.K9.Where) :
    ProofFile.k10Par Zp (ProofFile.k9Stretches Zp) p = k10ParE groupsW xsW p := by
  rw [k10Par_eq, k10ParG_eq, stretches_at_head h, groups_at_head h]

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.plan1_at_head
#print axioms Johnson.AtFull.Shape.cuts_at_head
#print axioms Johnson.AtFull.Shape.entries_at_head
#print axioms Johnson.AtFull.Shape.stretches_of
#print axioms Johnson.AtFull.Shape.spots_at_head
#print axioms Johnson.AtFull.Shape.stretches_at_head
#print axioms Johnson.AtFull.Shape.groups_at_head
#print axioms Johnson.AtFull.Shape.k9At_at_head
#print axioms Johnson.AtFull.Shape.k10_at_head
