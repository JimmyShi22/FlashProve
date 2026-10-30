-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkJointFold.lean: a run of the program's fold leads from joint to joint.

OnBytes/Slice/BlkJoints.lean writes down what is known between two blocks of the program's run on a
link's chain. This file proves the statement of OnBytes/Slice/BlkChain.lean on a fold for these
joints, from the theorem on the program's fold (OnBytes/Slice/BlkFoldSem.lean).

Main definition.
 `FoldTies`     the tie on columns (where the columns are that a later block reads) goes through a
                fold.
Main theorem.
 `foldRuns_at`  a run of the program's fold leads from `GroupAt` at a claim q to `SingleAt` at the
                claim after the fold (OnBytes/Slice/ChainSem.lean: `foldNext`).

Not claimed. `FoldTies`: it is a hypothesis. Nothing on soundness.
-/
import OnBytes.Slice.BlkFoldSem
import OnBytes.Slice.BlkJoints
import OnBytes.Slice.ChainSem

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb _root_.Run
open Params (IoppStage)

/-- The tie goes through a fold: from the tie Tie before it to the tie Tie' after it, on the
fold's output. What is known of the run: the mask was marked as spent (c to c1); the fold's rounds
were taken and nothing else was done (c1 to c'); the point that was drawn; the fold's own tests of
the shape and of the row have passed. -/
def FoldTies (K : Codes) (s : Sg) (cur : IoppStage) (pt : Fin (s.h + s.g) → GE)
    (rest : List Fmt.RoundView) (Tie : Ctx → GroupRow → GroupLayout → Nat → Prop)
    (Tie' : Ctx → SingleRows → Prop) : Prop :=
  ∀ (c c1 c' : Ctx) (row : GroupRow) (L : GroupLayout) (o : Nat) (eps claim : E)
    (gamma : List E), Tie c row L o → c.st.codes = K → PlainForm row.c →
    (Blk.spendAsMask o).Yields c () c1 → RanRounds (s.h + s.g + 1) rest c1 c' →
    readP (s.h + s.g) gamma = pt → gamma.length = s.h + s.g →
    foldShapeOk c.st (ioppFoldShape cur L) = true →
    foldRowOk c1.st (ioppFoldShape cur L) row = true →
    Tie' c' (foldOutput c1.st (ioppFoldShape cur L) row o eps gamma claim)

/-- For a stage with the program's codes (`hK`) and ties that go through a fold (`hT`): if `GroupAt`
holds and the program's fold runs through, `SingleAt` holds where the run ends, at the claim
`foldNext`. -/
theorem foldRuns_at (V : Fmt.View) (K : Codes) (roots : Nat) (s : Sg) (cur : IoppStage)
    (hK : StageCodes s cur K) (dE dT : PQ.RD)
    (q : GE × (s.cIn.J → GE)) (τ : Tr (PQ.uL (ckP .two) (foldRds s dE dT))) (rest : List Fmt.RoundView)
    (Tie : Ctx → GroupRow → GroupLayout → Nat → Prop) (Tie' : Ctx → SingleRows → Prop)
    (hT : FoldTies K s cur (foldPt s dE dT τ) rest Tie Tie') :
    FoldRuns cur (GroupAt V K roots s q (PQ.rvSL (ckP .two) (foldRds s dE dT) τ ++ rest) Tie)
      (SingleAt V K roots s (foldNext s s.Z.l dE dT q τ) rest Tie') := by
  intro answers c row L mask rows c' hJ hrun
  obtain ⟨o, rfl, ht⟩ := hJ.mask
  obtain ⟨hst, c1, eps, claim, gamma, hsp, hout, hpt, hlen, hran, hshape, _, hrow⟩ :=
    blk_fold_sem s (ioppFoldShape cur L) hK.k hK.h row hJ.plain o dE dT τ.1 τ.2.1 τ.2.2
      rest c c' rows hJ.run.onView.dry (by rw [hJ.run.codes]; exact congrArg (·.l) hK.mask)
      hJ.run.pending hrun
  have e1 := Blk.spendAsMask_inv o c c1 hsp
  refine ⟨⟨⟨hran.dry, ?_, ?_⟩, hran.pending, ?_, ?_, hJ.run.answers⟩, ?_, ?_⟩
  · rw [hran.firstTree, e1]
    exact hJ.run.onView.first
  · rw [hran.opened, e1]
    exact hJ.run.onView.opened
  · rw [hran.st, e1]
    exact hJ.run.codes
  · rw [hran.roots, e1]
    exact hJ.run.roots
  · rw [hst, hJ.claim]
    rfl
  · rw [hout]
    exact hT c c1 c' row L o eps claim gamma ht hJ.run.codes hJ.plain hsp hran hpt hlen hshape hrow

end OnBytes.Slice

#print axioms OnBytes.Slice.foldRuns_at
