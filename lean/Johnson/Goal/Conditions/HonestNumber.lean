-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/HonestNumber.lean: THE HONEST PROVER's HASH CALLS AS A NUMERAL, at the
letters S of one set of public files WHOSE KEY FILE's AND PROOF FILE's DATA ARE THE WRITTEN DATA
(writtenKFull, writtenPFull, Johnson/Flat/Dec/FitAtWritten.lean): allF
(Johnson/Prover/All/CountF.lean) at caps of 2^(work + 6) tries is 7068035999651.

Main names.
  sums_key, sums_proof   the six sums of Johnson/Prover/Law/CountFWritten.lean at data that ARE the
    written data.
  capT, capL, capB       DEFINITIONS: the three files' caps: capAt
    (Johnson/Prover/Law/CountFAt.lean) at the bits of work of S's rounds.
  chainF_wqW_of_sum, wireBlocksButOne_atWrittenRounds, chainT_written, chainL_written, chainB_written   the parts.
  allF_written           THE STATEMENT.

What it asks. S.DK = writtenKFull · S.DP = writtenPFull (in scope, where protocolDataWellFormed says yes, at
dataAtFiles flashProveData Z: key_built_written, Johnson/Goal/Description/KeyWritten.lean, and
proof_built_written, ProofWritten.lean) · the three coins' paths have the lengths 0, 0 and 6.

Limits. THE THREE LENGTHS ARE PREMISES: 0 (the key file's calls) and 6 (the proof file's) are the
depths of request trees at which FitAtWritten.lean evaluates the frame's test; the copy's file's 0
is what the frame's wiring lays; that S's plan has the first two depths is not shown here (at dataAtFiles
flashProveData Z, where protocolDataWellFormed says yes: depthReqT_the, depth_the). THE CAPS ARE OF OUR CHOOSING.
The copy's file's rounds are dsFull at every S, by DescriptionDataAtFiles's text. An upper bound on every path, with
chainF's looseness. No goal's form is named.
This file states no goal.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.HonestAtDescriptionDataAtFiles
import Johnson.Prover.Law.CountFWritten
import Johnson.Goal.Skeleton.LiveOfReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace FlashProve
open VerifierAndGoals
open VerifiableInference VerifiableInference.OnPublicFiles
open Rom OnBytes.Flat OnBytes.Slice OnBytes.Maker _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open LPFD.Full (KF)
open PV.EntryFive (dsF xsF)
open Johnson.G (writtenKFull writtenPFull writtenKFull_eq writtenPFull_eq dKeyFull dProofFull sumE
  fr_a)

/-- The key file's three sums at data that are the written data. -/
theorem sums_key (D : WholeD) (e : D = writtenKFull) :
    sumE 0 (D.ds₁.map fun d => roundF 24088 0 (d.trees.map (·.a)) d.entry.work) =
        1100439984544 ∧
      sumE 0 (D.ds₂.map fun d => roundF 24088 0 (d.trees.map (·.a)) d.entry.work) =
        2748829449534 ∧
      sumE 0 (D.ds₃.map fun d => roundF 24088 0 (d.trees.map (·.a)) d.entry.work) =
        1374391651799 := by
  have e' : D = dKeyFull := e.trans writtenKFull_eq
  subst e'
  exact ⟨key1, key2, key3⟩

/-- The proof file's. -/
theorem sums_proof (D : WholeD) (e : D = writtenPFull) :
    sumE 0 (D.ds₁.map fun d => roundF 24088 6 (d.trees.map (·.a)) d.entry.work) =
        5700400065 ∧
      sumE 0 (D.ds₂.map fun d => roundF 24088 6 (d.trees.map (·.a)) d.entry.work) =
        171849072342 ∧
      sumE 0 (D.ds₃.map fun d => roundF 24088 6 (d.trees.map (·.a)) d.entry.work) =
        337661579 := by
  have e' : D = dProofFull := e.trans writtenPFull_eq
  subst e'
  exact ⟨proof1, proof2, proof3⟩

/-- chainF_wqW (Johnson/Prover/Law/CountFAt.lean) from a sum that is given as a number. B: the
blocks of a whole answer. -/
theorem chainF_wqW_of_sum (C : PQ.CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (p : ℕ)
    (ds : List TypedOracleCompiler.Run.PQ.RD) (a : ℕ) (xs : List PQ.XO) {Y : Type}
    (dec : Y → PQ.View → Bool) (B : ℕ) (hB : K + 2 = B) (n : ℕ)
    (h : (ds.map fun d => roundF B p (d.trees.map (·.a)) d.entry.work).sum = n) :
    chainF (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape (linkSkeletonOfRoundData C ds a xs dec).up.ann
      (Johnson.RunOne.StrictW.wqW C ds a xs dec K chal).sh (capAt (workL ds)) 0 p =
      2 + p + 2 * B + n := by
  subst hB
  rw [chainF_wqW, h]

variable {Zk : OnBytes.K.Pub} (S : DescriptionDataAtFiles Zk) (c₀ : Digest) (m₀ : List (Dig 256))

/-- The three files' caps: capAt: 2^(work + 6) - 1 at every round (63 where work is 0). -/
def capT : ℕ → ℕ := capAt (Page.workAt (S.DK.at frS.P.T.a))
def capL : ℕ → ℕ := capAt (workL dsF)
def capB : ℕ → ℕ := capAt (Page.workAt (S.DP.at frS.P.T.a))

variable (eK : S.DK = writtenKFull) (eP : S.DP = writtenPFull)
include eK eP

theorem wireBlocksButOne_atWrittenRounds : KF S.DK S.DP = 24086 := by
  rw [eK, eP]
  exact FlashProve.kf_written

/-- The key file's chain. -/
theorem chainT_written :
    chainF (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).protocol.offline.shape (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).offlineRoundSplits
      (wTC (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).queryLayout).sh (capT S) 0 0 = 5223661230411 :=
  (chainF_of_sums (ckP .two) (KF S.DK S.DP) (chalP .two (KF S.DK S.DP)) 0 (S.DK.at frS.P.T.a)
    (front₀ S.G.rec₀) (join₀ S.G.rec₀) ByteArray.empty silK S.runK 24088
    (by rw [wireBlocksButOne_atWrittenRounds S eK eP]) _ _ _ (sum_of_sumE (sums_key S.DK eK).1)
    (sum_of_sumE (sums_key S.DK eK).2.1) (sum_of_sumE (sums_key S.DK eK).2.2)).trans (by norm_num)

/-- The proof file's chain. -/
theorem chainB_written :
    chainF (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).protocol.onlineBatch.loc.shape (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).protocol.onlineBatch.ann
      (wBC (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).queryLayout).sh (capB S) 0 6 = 177887278538 :=
  (chainF_of_sums (ckP .two) (KF S.DK S.DP) (chalP .two (KF S.DK S.DP)) 6 (S.DP.at frS.P.T.a)
    (front₀ S.G.z₀.2) (join₀ S.G.z₀.2) ByteArray.empty silP S.runP 24088
    (by rw [wireBlocksButOne_atWrittenRounds S eK eP]) _ _ _ (sum_of_sumE (sums_proof S.DP eP).1)
    (sum_of_sumE (sums_proof S.DP eP).2.1) (sum_of_sumE (sums_proof S.DP eP).2.2)).trans
    (by norm_num)

/-- The copy's file's chain. -/
theorem chainL_written :
    chainF (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).protocol.link.shape (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).linkRoundSplits
      (wLC (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).queryLayout).sh capL 0 0 = 1649307525166 :=
  (chainF_wqW_of_sum (ckP .two) (KF S.DK S.DP) (chalP .two (KF S.DK S.DP)) 0 dsF frS.P.T.a xsF
    S.dec 24088 (by rw [wireBlocksButOne_atWrittenRounds S eK eP]) _ (sum_of_sumE copy0)).trans (by norm_num)

/-- **THE HONEST PROVER's HASH CALLS, AS A NUMERAL.** -/
theorem allF_written {Kap : Type}
    (d : Draw 256 (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).protocol (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).LeafBody
      (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).offlineRoundSplits (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).linkRoundSplits Kap)
    (pT : d.coT.path.length = 0) (pL : d.coL.path.length = 0) (pB : d.coB.path.length = 6) :
    allF (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).queryLayout (capT S) capL (capB S) d = 7068035999651 := by
  have hd : (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).queryLayout.depth = 32 := fr_a
  have hk : (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).queryLayout.K = 24087 :=
    congrArg (· + 1) (wireBlocksButOne_atWrittenRounds S eK eP)
  unfold allF
  rw [pT, pL, pB, chainT_written S c₀ m₀ eK eP, chainL_written S c₀ m₀ eK eP,
    chainB_written S c₀ m₀ eK eP, hd, hk]
  norm_num

end FlashProve

#print axioms FlashProve.sums_key
#print axioms FlashProve.sums_proof
#print axioms FlashProve.chainF_wqW_of_sum
#print axioms FlashProve.wireBlocksButOne_atWrittenRounds
#print axioms FlashProve.chainT_written
#print axioms FlashProve.chainB_written
#print axioms FlashProve.chainL_written
#print axioms FlashProve.allF_written
