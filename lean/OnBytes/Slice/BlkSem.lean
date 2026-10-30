-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkSem.lean: the program's yes inside the written protocol gives the yes in the field,
if each block of the program leads from joint to joint.

OnBytes/Slice/ChainSem.lean composes the claims of the batching, the folds, the code switches and
the base case, read in the field, into one predicate on the written rounds, `SemAccept`. A
verifier's text has to be looked at in one direction: its yes implies `SemAccept`. This file does
the joining for the program's own decision on a link's chain. The decision's yes on a view is
followed from block to block (OnBytes/Slice/BlkChain.lean), with the joints of
OnBytes/Slice/BlkJoints.lean at the claims of ChainSem.lean. The two folds and the last stage are
proved to lead from joint to joint (OnBytes/Slice/BlkJointFold.lean, BlkJointLast.lean).

Main theorem.
 `semAccept_of_runs`   for a link with three stages whose last stage has no row variables, under
                       the conditions on sizes and readings that the statement lists:
                       `SemAccept`, from the yes of the program's decision on the view.

A joint is what is known of the program's state between two blocks: which claim it holds, read in
the field, and which rounds are left (OnBytes/Slice/BlkJoints.lean). A tie says how the columns that
a later block will read depend on the written oracles.

Not claimed: what the theorem asks, as hypotheses with names. `hHead`: the link's steps and the
batching lead to the first joint. `hC1`, `hC2`: the two code switches lead from joint to joint.
`hT1`, `hT2`: the tie on columns goes through a fold.
Nothing is said of a link whose masks do not ride in the switches' messages: `hride` excludes it.
Nothing is said of a link whose first mask is not sent with the folded rows: the first joint asks
that the mask of the first fold has come, so for such a link `hHead` cannot be met.
-/
import OnBytes.Slice.BlkJointFold
import OnBytes.Slice.BlkJointLast

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb _root_.Run
open Params (LinkShape IoppStage)

section
variable {S : Sz} {t₀ : ℕ} {s2 s3 : Sg} {d2 dS2 dS3 dL dB : PQ.RD}
  (R : Reads S t₀ s2 s3 d2 dS2 dS3 dL dB) (hf1 : CsFit (S.sg t₀) s2) (hf2 : CsFit s2 s3)
  (dA dE1 dT1 dC1 dE2 dT2 dC2 : PQ.RD)
  (x : S.lk.X4) (o2 : (wRound d2).Orc) (cA : (wRound dA).Chal)
  (τF1 : Tr (PQ.uL (ckP .two) (foldRds (S.sg t₀) dE1 dT1)))
  (τC1 : Tr (PQ.uL (ckP .two) [dS2, dC1]))
  (τF2 : Tr (PQ.uL (ckP .two) (foldRds s2 dE2 dT2)))
  (τC2 : Tr (PQ.uL (ckP .two) [dS3, dC2])) (τB : Tr (PQ.uL (ckP .two) [dL, dB]))

/-- The program's yes on a view gives the yes in the field, for a link with three stages whose last
stage has no row variables and whose masks ride, under the conditions on sizes and readings that the
statement lists, if the link's steps with the batching and the two code switches lead from joint to
joint (`hHead`, `hC1`, `hC2`) and the ties go through the two folds (`hT1`, `hT2`). V: the view.
Λ, first, further, s: the link's shape, the two tables and the start of the program's run. st1, st2,
st3: the program's three stages. K: the statement's codes. Tie0 to Tie3: what ties the columns that
a later block reads to the written oracles. -/
theorem semAccept_of_runs (V : Fmt.View) (Λ : LinkShape) (first further : TableKey)
    (st1 st2 st3 : IoppStage) (htest : Λ.test = [st1, st2, st3])
    (hride : Λ.choice.masksRide = true) (s : Start) (K : Codes)
    (hK1 : StageCodes (S.sg t₀) st1 K) (hK2 : StageCodes s2 st2 K) (hK3 : StageCodes s3 st3 K)
    (hn1 : R.n1 = (S.sg t₀).Z.l) (hn2 : R.n2 = s2.Z.l)
    (hw3 : R.w3 τC2.1 = wordIn s3 (lastColW dS3 τC2.1.1))
    (hg3 : R.g3 τC2.1 = wordMk s3 (lastMk dS3 τC2.1.1)) (hfu : R.fu τB.1 = lst (sentW dL τB.1) 0)
    (hfs : R.fs τB.2.2.1 = shownW s3 (sentW dB τB.2.2.1))
    (h0 : s3.h = 0) (g0 : s3.g = 0) (hza : s3.Z.a ≤ s3.C.a) (ha : s3.C.a ≤ 32)
    (hW : PQ.colW dS3.tree = 12) (hN : PQ.posN dS3.tree = 2 ^ s3.C.a) {nB : ℕ}
    (hB : SendsDraws dB nB 0 s3.t s3.C.a) (hsh : Shows V 2 (treeCol dS3 τC2.1))
    (Tie0 Tie2 : Ctx → GroupRow → GroupLayout → Nat → Prop)
    (Tie1 Tie3 : Ctx → SingleRows → Prop)
    (hHead : HeadRuns Λ first further st1 (startCtx s V)
      (GroupAt V K 1 (S.sg t₀) (claimBat R dA x cA)
        (PQ.rvSL (ckP .two) _ τF1 ++ (PQ.rvSL (ckP .two) _ τC1 ++ (PQ.rvSL (ckP .two) _ τF2 ++
          (PQ.rvSL (ckP .two) _ τC2 ++ PQ.rvSL (ckP .two) _ τB)))) Tie0))
    (hT1 : FoldTies K (S.sg t₀) st1 (foldPt (S.sg t₀) dE1 dT1 τF1)
      (PQ.rvSL (ckP .two) _ τC1 ++ (PQ.rvSL (ckP .two) _ τF2 ++
        (PQ.rvSL (ckP .two) _ τC2 ++ PQ.rvSL (ckP .two) _ τB))) Tie0 Tie1)
    (hC1 : CsRuns true st2 [st3]
      (SingleAt V K 1 (S.sg t₀) (claimFold1 R dA dE1 dT1 x cA τF1)
        (PQ.rvSL (ckP .two) _ τC1 ++ (PQ.rvSL (ckP .two) _ τF2 ++
          (PQ.rvSL (ckP .two) _ τC2 ++ PQ.rvSL (ckP .two) _ τB))) Tie1)
      (GroupAt V K 2 s2 (claimCs1 R hf1 dA dE1 dT1 dC1 x o2 cA τF1 τC1)
        (PQ.rvSL (ckP .two) _ τF2 ++ (PQ.rvSL (ckP .two) _ τC2 ++ PQ.rvSL (ckP .two) _ τB)) Tie2))
    (hT2 : FoldTies K s2 st2 (foldPt s2 dE2 dT2 τF2)
      (PQ.rvSL (ckP .two) _ τC2 ++ PQ.rvSL (ckP .two) _ τB) Tie2 Tie3)
    (hC2 : CsRuns true st3 []
      (SingleAt V K 2 s2 (claimFold2 R hf1 dA dE1 dT1 dC1 dE2 dT2 x o2 cA τF1 τC1 τF2)
        (PQ.rvSL (ckP .two) _ τC2 ++ PQ.rvSL (ckP .two) _ τB) Tie3)
      (LastAt V K 3 s3 st3
        (claimCs2 R hf1 hf2 dA dE1 dT1 dC1 dE2 dT2 dC2 x o2 cA τF1 τC1 τF2 τC2)
        (PQ.rvSL (ckP .two) _ τB) 2))
    (hdec : (linkVerify Λ first further).decides s V = true) :
    SemAccept R hf1 hf2 dA dE1 dT1 dC1 dE2 dT2 dC2 x o2 cA τF1 τC1 τF2 τC2 τB := by
  rw [semAccept_iff, hw3, hg3, hfu, hfs]
  have hF1 := foldRuns_at V K 1 (S.sg t₀) st1 hK1 dE1 dT1 (claimBat R dA x cA) τF1 _ Tie0 Tie1 hT1
  have hF2 := foldRuns_at V K 2 s2 st2 hK2 dE2 dT2
    (claimCs1 R hf1 dA dE1 dT1 dC1 x o2 cA τF1 τC1) τF2 _ Tie2 Tie3 hT2
  have hL := lastRuns_at V K 3 s3 h0 g0 hza ha Λ.choice.masksRide st3 hK3 dS3 dL dB τC2.1 hW hN τB
    [] (claimCs2 R hf1 hf2 dA dE1 dT1 dC1 dE2 dT2 dC2 x o2 cA τF1 τC1 τF2 τC2) 2 hsh hB
  rw [List.append_nil] at hL
  rw [← hn1] at hF1
  rw [← hn2] at hF2
  rw [← hride] at hC1 hC2
  exact blk_chain Λ first further st1 st2 st3 htest s V _ _ _ _ _ _ hHead hF1 hC1 hF2 hC2 hL hdec

end

end OnBytes.Slice

#print axioms OnBytes.Slice.semAccept_of_runs
