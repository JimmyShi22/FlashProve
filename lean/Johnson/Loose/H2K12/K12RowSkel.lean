-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Loose.H2K12.K12RowSkelW
import Johnson.Loose.H2K12.K12MemberWritten
import Johnson.Desc.ProofFile.Law.Skel.SkelEnd
/-
Johnson/Loose/H2K12/K12RowSkel.lean: CONDITIONAL: UNDER THE PREMISE hV (OR THE SIX THAT GIVE IT),
SHOWN OF NO PUBLIC FILES BY LEAN's KERNEL: THE PROXIMITY TEST's (the kind K12's) ROW AMONG
THE ROWS THAT "the proof file's IOP as written in Lean returns, with its cut" WANTS OF EACH LOT, IN
ANOTHER FORM: THE LOT's SKELETON IS THE WRITTEN ONE (ProofFile.Sk.lotSk,
Johnson/Desc/ProofFile/Law/Skel/SkelFaults.lean). Calls and unfoldings:
no evaluation in Lean's kernel stands in this file. The same shape as the row for the kind
K5 (Johnson/Desc/First/Att/Row/K5RowSkel.lean).
WHO SPENDS IT: ProofFile.Sk.back_of_skel (…/Skel/SkelEnd.lean): from one such row a lot (its
hk), Steady at every lot (its hS), the base's sub-protocols being the lots' (its hB) and four closed
facts over the written skeletons it gives FOUR OF
THE SEVEN STEPS of the back of the IOP's maker (no fault; nothing lacking; the sub-protocols at the
places; the first chain), with the chain's skeletons. Whether Lean's kernel bears these four closed
facts at the real lists is not asked there; nor is it here. A later caller
(ProofFile.Sk.Full.rows_fifteen, …/Skel/Full/Fifteen.lean) asks the row in another form, RowAt: the step
from k12_lot_skel to that form (rowAt_of_lotSk | rowAt_plain, …/Skel/Full/Rows.lean: one closed fact
more) is not in this file.
  k12_blocks_skel  from hV (the numbers which the list of rounds gives are the written member
                   piLFull): the lot's sub-protocols' skeletons are [k12SkelW]
                   (H2K12/K12RowSkelW.lean), at every ground G
  k12_lot_skel     from hV: the lot's skeleton: its name, letters := false, still := [], that one
                   skeleton, no batching, no test behind a run of claims, none behind the adding
  k12_steady       the lot makes no batching: so it is Steady (steady_none)
  k12_lot_skel_written THE SAME END FROM HYPOTHESES BY FIELD: members_written's six
                   (H2K12/K12MemberWritten.lean) at Z.made: five equations (three on fields of what
                   the planner configured, one on the plans as read back, one on what is sent), and
                   (D) (hD : declPOf Z.made = .ok D). It spends no opening
                   and no "in scope" test
THE KIND's THREE OTHER SUB-PROTOCOLS stand in no lot of the first chain: the shared and the second
seat lay them; their rows are not here.
WHAT IT IS NOT: none of the six is shown of any public files by Lean's kernel. The name in the
skeleton is the lot's own; the name under which the seat lays the sub-protocol comes of the spots.
The full size alone. No soundness statement. Nothing on hiding.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12

open OnBytes OnBytes.Params Johnson.G.OfPlan
open VerifiableInference.PlanWritten (proofSizedFull)
open VerifiableInference.Number.ByRuns (proofThree)
open Johnson.G (proofSendsFull)
open H2K.Member (piLFull)

/-- **The row, in the form "(L.blocks G).map skel = its written rows".** -/
theorem k12_blocks_skel (Z : ProofFile.Pub) (G : ProofFile.Ground) (hV : H2U.p12OfMade Z.made = piLFull) :
    ((VerifiableInference.Desc.K12.lot Z).blocks G).map ProofFile.Sk.skel = [k12SkelW] := by
  rw [k12_blocks, hV]
  exact congrArg (fun x => [x]) skelL_full

/-- **THE LOT's SKELETON IS THE WRITTEN ONE.** -/
theorem k12_lot_skel (Z : ProofFile.Pub) (G : ProofFile.Ground) (hV : H2U.p12OfMade Z.made = piLFull) :
    ProofFile.Sk.lotSk G (VerifiableInference.Desc.K12.lot Z) =
      { name := "the proximity test at F:2 (K12)", letters := false, still := []
        blocks := [k12SkelW], batch := fun _ => none, each := fun _ => false
        tests := fun _ => false } := by
  unfold ProofFile.Sk.lotSk
  rw [k12_blocks_skel Z G hV]
  rfl

theorem k12_steady (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    ProofFile.Sk.Steady G (VerifiableInference.Desc.K12.lot Z) :=
  ProofFile.Sk.steady_none G _ fun _ => rfl

/-- **THE SAME, FROM HYPOTHESES BY FIELD.** -/
theorem k12_lot_skel_written (Z : ProofFile.Pub) (G : ProofFile.Ground)
    (hs : Z.made.p.chains.made.sized.set = recordSet)
    (hz : Z.made.p.chains.made.sized.proof = proofSizedFull)
    (hp : Z.made.p.chains.made.proof =
      [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan])
    (hg : ProofPlansPriced Z.made proofThree.A.plan proofThree.B.plan proofThree.C.plan)
    (hc : Z.made.proof = proofSendsFull) (D : Decl3) (hD : declPOf Z.made = .ok D) :
    ProofFile.Sk.lotSk G (VerifiableInference.Desc.K12.lot Z) =
      { name := "the proximity test at F:2 (K12)", letters := false, still := []
        blocks := [k12SkelW], batch := fun _ => none, each := fun _ => false
        tests := fun _ => false } :=
  k12_lot_skel Z G (members_written Z.made hs hz hp hg hc D hD).1

end H2K12

#print axioms H2K12.k12_blocks_skel
#print axioms H2K12.k12_lot_skel
#print axioms H2K12.k12_steady
#print axioms H2K12.k12_lot_skel_written
