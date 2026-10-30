--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/StepsTwins.lean: what Johnson/Desc/K14/Honest/ItemsEach.lean,
ShapesBehind.lean and ItemsHold.lean show behind each of the eight sub-protocols of the linear
claim's shared rounds, said again with no premise on the run but the format's own steps.

Each theorem here is one of theirs, with a run of steps up to the sub-protocol
(Johnson/Desc/K14/Honest/StepsBack.lean: StepTo1, …, StepTo8) in the stead of a run of the kind's
functions. A run of steps follows from the fold over the first so many of the eight, AS THE KIND's
TEXT MAKES THEM: a proof file's IOP as written in Lean holds them carried to the file's type of
claims, behind a front sub-protocol; the way from its own list to these eight is not in this file.

Main names:
  Eight.stepTo1_of_fold, …, stepTo8_of_fold   **from foldBlocks over the first so many of the eight
                      to a run of steps**: the rounds and the columns that the fold has taken are
                      named, and what is left over is what the fold returns
  Steps.met1, …, met8   AllMet behind each of the eight (of the whole statement: these ask what
                      earlier sendings showed)
  Steps.omU_behind1, nearU_behind1, recRow_behind1, sample_behind2, recG_behind3, loc_behind4,
  sample_behind5, fold_behind7, foldU_behind8, foldOmega_behind8   the claims on the honest tables:
                      each asks, of what is shown, only what its own sub-protocol shows
  Steps.shape1, …, shape8, Steps.codes1, …, codes8   the library's tests on the state (shapeK,
                      codX). shapeK at the first two: where the key's sizes fit
  steps_twins_met     **a member**, under PlanFacts, the two sendings' test on the plan and an
                      Eight P: what these theorems ask, but for the premise on the committed
                      table's every column (hTab), is met together, whatever the four messages'
                      random values and the words in front are

What is assumed, as premises: Public8 (at met1, …, met8: Start8); the run of steps up to the
sub-protocol; of what is shown, of the committed table and of the key, what the theorem's namesake
asks, said at the view without the digest (Seen8.view).

What is not claimed. What the namesakes do not claim. The member is ChainStepsMet.lean's: rows 0, a
key that is no committer's, one location. That a prover's play makes such steps. Nothing on
soundness or on hiding. This is not completeness of the protocol or of a program.

-/
import Johnson.Desc.K14.Honest.StepsBack
import Johnson.Desc.K14.Honest.ItemsHold
import Johnson.Desc.K14.Honest.ChainStepsMet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Means (Words)
open OnBytes.Slice (rdE)
open VerifiableInference.Desc (OpenedColumn foldBlocks)
open VerifiableInference.Desc.Own (keyFits)
open VerifiableInference.Desc.K1 (planOkOwn)
open VerifiableInference.Desc.Key.LaidW (inFrontOf)
open Desc.K14.Law (genK rowsOn parU parO OmU NearAt RecAll RowsU RowsUL RowsO FoldAt SmpSay uRK
  codX)

variable {P : P14} {sentU : Array OracleNotice} {layO : TreeLay}

/-! ## From the fold over the first so many of the eight to a run of steps -/

/-- **From the fold over the first one of the eight**, up to "LIN point". -/
theorem Eight.stepTo1_of_fold (B : Eight P) (hU : withU P.S = some sentU) (ft : Nat) (d0 s : St)
    (rs rs' : List Fmt.RoundView) (c c' : List OpenedColumn)
    (h : foldBlocks ft [B.b1] d0 rs c = .ok (s, rs', c')) :
    ∃ W D, rs = [W.R1] ++ rs' ∧ c = c' ∧ D.d1 = s ∧ StepTo1 B ft d0 W D := by
  obtain ⟨R1, d1, t1, rfl, s1, h⟩ := B.peel1 hU ft _ d0 rs c _ h
  obtain ⟨rfl, rfl, rfl⟩ := fold_nil h
  exact ⟨⟨R1, R1, R1, R1, R1, R1, R1, R1, []⟩, ⟨d1, d1, d1, d1, d1, d1, d1, d1, inFrontOf d0,
    inFrontOf d0, #[], #[]⟩, rfl, rfl, rfl, ⟨⟨_, _, s1⟩⟩⟩

/-- **From the fold over the first two of the eight**, up to the sending of o_u. -/
theorem Eight.stepTo2_of_fold (B : Eight P) (hU : withU P.S = some sentU) (ft : Nat) (d0 s : St)
    (rs rs' : List Fmt.RoundView) (c c' : List OpenedColumn)
    (h : foldBlocks ft [B.b1, B.b2] d0 rs c = .ok (s, rs', c')) :
    ∃ W D, rs = [W.R1, W.R2a, W.R2b] ++ rs' ∧ c = c' ∧ D.d2 = s ∧ StepTo2 B ft d0 W D := by
  obtain ⟨R1, d1, t1, rfl, s1, h⟩ := B.peel1 hU ft _ d0 rs c _ h
  obtain ⟨R2a, R2b, d2, t2, rfl, s2, h⟩ := B.peel2 hU ft _ d1 t1 c _ h
  obtain ⟨rfl, rfl, rfl⟩ := fold_nil h
  exact ⟨⟨R1, R2a, R2b, R1, R1, R1, R1, R1, []⟩, ⟨d1, d2, d2, d2, d2, d2, d2, d2, inFrontOf d0,
    inFrontOf d0, #[], #[]⟩, rfl, rfl, rfl, ⟨⟨⟨_, _, s1⟩⟩, ⟨_, _, s2⟩⟩⟩

/-- **From the fold over the first three of the eight**, up to "(rec_gamma)". -/
theorem Eight.stepTo3_of_fold (B : Eight P) (hU : withU P.S = some sentU) (ft : Nat) (d0 s : St)
    (rs rs' : List Fmt.RoundView) (c c' : List OpenedColumn)
    (h : foldBlocks ft [B.b1, B.b2, B.b3] d0 rs c = .ok (s, rs', c')) :
    ∃ W D, rs = [W.R1, W.R2a, W.R2b] ++ rs' ∧ c = c' ∧ D.d3 = s ∧ StepTo3 B ft d0 W D := by
  obtain ⟨R1, d1, t1, rfl, s1, h⟩ := B.peel1 hU ft _ d0 rs c _ h
  obtain ⟨R2a, R2b, d2, t2, rfl, s2, h⟩ := B.peel2 hU ft _ d1 t1 c _ h
  obtain ⟨d3, s3, h⟩ := B.peel3 hU ft _ d2 t2 c _ h
  obtain ⟨rfl, rfl, rfl⟩ := fold_nil h
  exact ⟨⟨R1, R2a, R2b, R1, R1, R1, R1, R1, []⟩, ⟨d1, d2, d3, d3, d3, d3, d3, d3, inFrontOf d0,
    inFrontOf d0, #[], #[]⟩, rfl, rfl, rfl, ⟨⟨⟨⟨_, _, s1⟩⟩, ⟨_, _, s2⟩⟩, ⟨_, _, s3⟩⟩⟩

/-- **From the fold over the first four of the eight**, up to "LOC". -/
theorem Eight.stepTo4_of_fold (B : Eight P) (hU : withU P.S = some sentU) (ft : Nat) (d0 s : St)
    (rs rs' : List Fmt.RoundView) (c c' : List OpenedColumn)
    (h : foldBlocks ft [B.b1, B.b2, B.b3, B.b4] d0 rs c = .ok (s, rs', c')) :
    ∃ W D, rs = [W.R1, W.R2a, W.R2b, W.R4] ++ rs' ∧ c = W.cs ++ c' ∧ D.d4 = s ∧ StepTo4 B ft d0 W D
      := by
  obtain ⟨R1, d1, t1, rfl, s1, h⟩ := B.peel1 hU ft _ d0 rs c _ h
  obtain ⟨R2a, R2b, d2, t2, rfl, s2, h⟩ := B.peel2 hU ft _ d1 t1 c _ h
  obtain ⟨d3, s3, h⟩ := B.peel3 hU ft _ d2 t2 c _ h
  obtain ⟨R4, d4, t4, cs, c4, rfl, rfl, s4, h⟩ := B.peel4 hU ft _ d3 t2 c _ h
  obtain ⟨rfl, rfl, rfl⟩ := fold_nil h
  exact ⟨⟨R1, R2a, R2b, R4, R1, R1, R1, R1, cs⟩, ⟨d1, d2, d3, d4, d4, d4, d4, d4, inFrontOf d0,
    inFrontOf d0, #[], #[]⟩, rfl, rfl, rfl, ⟨⟨⟨⟨⟨_, _, s1⟩⟩, ⟨_, _, s2⟩⟩, ⟨_, _, s3⟩⟩, ⟨_, s4⟩⟩⟩

/-- **From the fold over the first five of the eight**, up to the sending of o_omega and o_sp. -/
theorem Eight.stepTo5_of_fold (B : Eight P) (hU : withU P.S = some sentU) (ft : Nat) (d0 s : St)
    (rs rs' : List Fmt.RoundView) (c c' : List OpenedColumn)
    (h : foldBlocks ft [B.b1, B.b2, B.b3, B.b4, B.b5] d0 rs c = .ok (s, rs', c')) :
    ∃ W D, rs = [W.R1, W.R2a, W.R2b, W.R4, W.R5a, W.R5b] ++ rs' ∧ c = W.cs ++ c' ∧ D.d5 = s ∧
      StepTo5 B ft d0 W D := by
  obtain ⟨R1, d1, t1, rfl, s1, h⟩ := B.peel1 hU ft _ d0 rs c _ h
  obtain ⟨R2a, R2b, d2, t2, rfl, s2, h⟩ := B.peel2 hU ft _ d1 t1 c _ h
  obtain ⟨d3, s3, h⟩ := B.peel3 hU ft _ d2 t2 c _ h
  obtain ⟨R4, d4, t4, cs, c4, rfl, rfl, s4, h⟩ := B.peel4 hU ft _ d3 t2 c _ h
  obtain ⟨R5a, R5b, d5, t5, rfl, s5, h⟩ := B.peel5 hU ft _ d4 t4 c4 _ h
  obtain ⟨rfl, rfl, rfl⟩ := fold_nil h
  exact ⟨⟨R1, R2a, R2b, R4, R5a, R5b, R1, R1, cs⟩, ⟨d1, d2, d3, d4, d5, d5, d5, d5, inFrontOf d0,
    inFrontOf d0, #[], #[]⟩, rfl, rfl, rfl, ⟨⟨⟨⟨⟨⟨_, _, s1⟩⟩, ⟨_, _, s2⟩⟩, ⟨_, _, s3⟩⟩, ⟨_, s4⟩⟩,
    ⟨_, _, s5⟩⟩⟩

/-- **From the fold over the first six of the eight**, up to the joinings. -/
theorem Eight.stepTo6_of_fold (B : Eight P) (hU : withU P.S = some sentU) (ft : Nat) (d0 s : St)
    (rs rs' : List Fmt.RoundView) (c c' : List OpenedColumn)
    (h : foldBlocks ft [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6] d0 rs c = .ok (s, rs', c')) :
    ∃ W D, rs = [W.R1, W.R2a, W.R2b, W.R4, W.R5a, W.R5b] ++ rs' ∧ c = W.cs ++ c' ∧ D.d6 = s ∧
      StepTo6 B ft d0 W D := by
  obtain ⟨R1, d1, t1, rfl, s1, h⟩ := B.peel1 hU ft _ d0 rs c _ h
  obtain ⟨R2a, R2b, d2, t2, rfl, s2, h⟩ := B.peel2 hU ft _ d1 t1 c _ h
  obtain ⟨d3, s3, h⟩ := B.peel3 hU ft _ d2 t2 c _ h
  obtain ⟨R4, d4, t4, cs, c4, rfl, rfl, s4, h⟩ := B.peel4 hU ft _ d3 t2 c _ h
  obtain ⟨R5a, R5b, d5, t5, rfl, s5, h⟩ := B.peel5 hU ft _ d4 t4 c4 _ h
  obtain ⟨d6, s6, h⟩ := B.peel6 hU ft _ d5 t5 c4 _ h
  obtain ⟨rfl, rfl, rfl⟩ := fold_nil h
  exact ⟨⟨R1, R2a, R2b, R4, R5a, R5b, R1, R1, cs⟩, ⟨d1, d2, d3, d4, d5, d6, d6, d6, inFrontOf d0,
    inFrontOf d0, #[], #[]⟩, rfl, rfl, rfl, ⟨⟨⟨⟨⟨⟨⟨_, _, s1⟩⟩, ⟨_, _, s2⟩⟩, ⟨_, _, s3⟩⟩, ⟨_, s4⟩⟩,
    ⟨_, _, s5⟩⟩, ⟨_, _, s6⟩⟩⟩

/-- **From the fold over the first seven of the eight**, up to "LIN zeta". -/
theorem Eight.stepTo7_of_fold (B : Eight P) (hU : withU P.S = some sentU) (ft : Nat) (d0 s : St)
    (rs rs' : List Fmt.RoundView) (c c' : List OpenedColumn)
    (h : foldBlocks ft [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7] d0 rs c = .ok (s, rs', c')) :
    ∃ W D, rs = [W.R1, W.R2a, W.R2b, W.R4, W.R5a, W.R5b, W.R7] ++ rs' ∧ c = W.cs ++ c' ∧ D.d7 = s ∧
      StepTo7 B ft d0 W D := by
  obtain ⟨R1, d1, t1, rfl, s1, h⟩ := B.peel1 hU ft _ d0 rs c _ h
  obtain ⟨R2a, R2b, d2, t2, rfl, s2, h⟩ := B.peel2 hU ft _ d1 t1 c _ h
  obtain ⟨d3, s3, h⟩ := B.peel3 hU ft _ d2 t2 c _ h
  obtain ⟨R4, d4, t4, cs, c4, rfl, rfl, s4, h⟩ := B.peel4 hU ft _ d3 t2 c _ h
  obtain ⟨R5a, R5b, d5, t5, rfl, s5, h⟩ := B.peel5 hU ft _ d4 t4 c4 _ h
  obtain ⟨d6, s6, h⟩ := B.peel6 hU ft _ d5 t5 c4 _ h
  obtain ⟨R7, d7, t7, rfl, s7, h⟩ := B.peel7 hU ft _ d6 t5 c4 _ h
  obtain ⟨rfl, rfl, rfl⟩ := fold_nil h
  exact ⟨⟨R1, R2a, R2b, R4, R5a, R5b, R7, R1, cs⟩, ⟨d1, d2, d3, d4, d5, d6, d7, d7, inFrontOf d0,
    inFrontOf d0, #[], #[]⟩, rfl, rfl, rfl, ⟨⟨⟨⟨⟨⟨⟨⟨_, _, s1⟩⟩, ⟨_, _, s2⟩⟩, ⟨_, _, s3⟩⟩, ⟨_, s4⟩⟩,
    ⟨_, _, s5⟩⟩, ⟨_, _, s6⟩⟩, ⟨_, _, s7⟩⟩⟩

/-- **From the fold over all eight**, up to "SPLIT". -/
theorem Eight.stepTo8_of_fold (B : Eight P) (hU : withU P.S = some sentU)
    (hS : P.S.sharedSplitNeeded = true) (ft : Nat) (d0 s : St)
    (rs rs' : List Fmt.RoundView) (c c' : List OpenedColumn)
    (h : foldBlocks ft [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8] d0 rs c = .ok (s, rs', c'))
      :
    ∃ W D, rs = [W.R1, W.R2a, W.R2b, W.R4, W.R5a, W.R5b, W.R7, W.R8] ++ rs' ∧ c = W.cs ++ c' ∧ D.d8
      = s ∧ StepTo8 B ft d0 W D := by
  obtain ⟨R1, d1, t1, rfl, s1, h⟩ := B.peel1 hU ft _ d0 rs c _ h
  obtain ⟨R2a, R2b, d2, t2, rfl, s2, h⟩ := B.peel2 hU ft _ d1 t1 c _ h
  obtain ⟨d3, s3, h⟩ := B.peel3 hU ft _ d2 t2 c _ h
  obtain ⟨R4, d4, t4, cs, c4, rfl, rfl, s4, h⟩ := B.peel4 hU ft _ d3 t2 c _ h
  obtain ⟨R5a, R5b, d5, t5, rfl, s5, h⟩ := B.peel5 hU ft _ d4 t4 c4 _ h
  obtain ⟨d6, s6, h⟩ := B.peel6 hU ft _ d5 t5 c4 _ h
  obtain ⟨R7, d7, t7, rfl, s7, h⟩ := B.peel7 hU ft _ d6 t5 c4 _ h
  obtain ⟨R8, d8, t8, rfl, s8, h⟩ := B.peel8 hU hS ft _ d7 t7 c4 _ h
  obtain ⟨rfl, rfl, rfl⟩ := fold_nil h
  exact ⟨⟨R1, R2a, R2b, R4, R5a, R5b, R7, R8, cs⟩, ⟨d1, d2, d3, d4, d5, d6, d7, d8, inFrontOf d0,
    inFrontOf d0, #[], #[]⟩, rfl, rfl, rfl, ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _, s1⟩⟩, ⟨_, _, s2⟩⟩, ⟨_, _, s3⟩⟩, ⟨_, s4⟩⟩,
    ⟨_, _, s5⟩⟩, ⟨_, _, s6⟩⟩, ⟨_, _, s7⟩⟩, ⟨_, _, s8⟩⟩⟩

variable {d0 : St} {H : Inputs} {B : Eight P} {ft : Nat} {W : Seen8} {D : States8}

/-! ## AllMet behind each of the eight, from the steps up to there -/

/-- Behind "LIN point" all that the statement claims holds of the honest words. -/
theorem Steps.met1 (S : Start8 P sentU layO d0 H) (u : StepTo1 B ft d0 W D) :
    Means.AllMet rdE D.d1.st (words2 P sentU d0 W.view.r1 H) :=
  S.met1 (S.pub.to1 u)

/-- Behind the sending of o_u, where the OOD answers shown are the honest ones. -/
theorem Steps.met2 (S : Start8 P sentU layO d0 H) (u : StepTo2 B ft d0 W D)
    (hU : ShownU P sentU d0 W.view D H) :
    Means.AllMet rdE D.d2.st (words2 P sentU d0 W.view.r1 H) := by
  obtain ⟨x, ids, t⟩ := S.pub.to2 u
  have k := S.met2 t hU
  exact k

/-- Behind "(rec_gamma)", where each answer of the key is its row's own. -/
theorem Steps.met3 (S : Start8 P sentU layO d0 H) (u : StepTo3 B ft d0 W D)
    (hU : ShownU P sentU d0 W.view D H) (hA : OwnAnswers P d0.loc.key H) :
    Means.AllMet rdE D.d3.st (words2 P sentU d0 W.view.r1 H) := by
  obtain ⟨x, ids, t⟩ := S.pub.to3 u
  have k := S.met3 t hU hA
  exact k

/-- Behind "LOC", where each opened column holds the rows' own symbols. -/
theorem Steps.met4 (S : Start8 P sentU layO d0 H) (u : StepTo4 B ft d0 W D)
    (hU : ShownU P sentU d0 W.view D H) (hA : OwnAnswers P d0.loc.key H)
    (hC : OwnColumns P W.view H) :
    Means.AllMet rdE D.d4.st (words2 P sentU d0 W.view.r1 H) := by
  obtain ⟨x, ids, t⟩ := S.pub.to4 u
  have k := S.met4 t hU hA hC
  exact k

/-- Behind the sending of o_omega and o_sp, where the OOD answers shown there are honest too. -/
theorem Steps.met5 (S : Start8 P sentU layO d0 H) (u : StepTo5 B ft d0 W D)
    (hU : ShownU P sentU d0 W.view D H) (hA : OwnAnswers P d0.loc.key H)
    (hC : OwnColumns P W.view H) (hO : ShownO P sentU d0 W.view D H) :
    Means.AllMet rdE D.d5.st (words2 P sentU d0 W.view.r1 H) := by
  obtain ⟨x, ids, x', ids', t⟩ := S.pub.to5 u
  have k := S.met5 t hU hA hC hO
  exact k

/-- Behind the joinings. -/
theorem Steps.met6 (S : Start8 P sentU layO d0 H) (u : StepTo6 B ft d0 W D)
    (hU : ShownU P sentU d0 W.view D H) (hA : OwnAnswers P d0.loc.key H)
    (hC : OwnColumns P W.view H) (hO : ShownO P sentU d0 W.view D H) :
    Means.AllMet rdE D.d6.st (words2 P sentU d0 W.view.r1 H) := by
  obtain ⟨x, ids, x', ids', t⟩ := S.pub.to6 u
  have k := S.met6 t hU hA hC hO
  exact k

/-- Behind "LIN zeta". -/
theorem Steps.met7 (S : Start8 P sentU layO d0 H) (u : StepTo7 B ft d0 W D)
    (hU : ShownU P sentU d0 W.view D H) (hA : OwnAnswers P d0.loc.key H)
    (hC : OwnColumns P W.view H) (hO : ShownO P sentU d0 W.view D H) :
    Means.AllMet rdE D.d7.st (words2 P sentU d0 W.view.r1 H) := by
  obtain ⟨x, ids, x', ids', t⟩ := S.pub.to7 u
  have k := S.met7 t hU hA hC hO
  exact k

/-- Behind "SPLIT", where the scalar shown is the honest one too. -/
theorem Steps.met8 (S : Start8 P sentU layO d0 H) (u : StepTo8 B ft d0 W D)
    (hU : ShownU P sentU d0 W.view D H) (hA : OwnAnswers P d0.loc.key H)
    (hC : OwnColumns P W.view H) (hO : ShownO P sentU d0 W.view D H)
    (hM : ShownMu P d0 W.view H) :
    Means.AllMet rdE D.d8.st (words2 P sentU d0 W.view.r1 H) := by
  obtain ⟨x, ids, x', ids', t⟩ := S.pub.to8 u
  have k := S.met8 t hU hA hC hO hM
  exact k

/-! ## The claims on the honest tables, from the steps up to the sub-protocol that opens them -/

/-- Behind "LIN point": the library's OmU. -/
theorem Steps.omU_behind1 (S : Public8 P sentU layO d0) (u : StepTo1 B ft d0 W D)
    (h0 : d0.st.oracles.size = 0) (H : Inputs) :
    OmU P.par (uRK P.par) (fun w : Words Cb.Gl.E => w) (omegaAt P d0) D.d1
      (words2 P sentU d0 W.view.r1 H) :=
  S.omU_behind1 (S.to1 u) h0 H

/-- Behind "LIN point": the library's NearAt, at every radius, under hTab. -/
theorem Steps.nearU_behind1 (S : Public8 P sentU layO d0) (u : StepTo1 B ft d0 W D)
    (h0 : d0.st.oracles.size = 0) (H : Inputs) (tab : Nat → List UInt64)
    (hTab : ∀ x < 2 ^ P.par.S.fold.index.code.logN, ∀ r < P.par.S.fold.index.rows,
      rdE.val (ofF ((tab x).toArray.getD r 0)) = genK rdE P.par.S.fold x (H.Rw r)) (e' : Nat) :
    NearAt rdE P.par (uRK P.par D.d1) (words2 P sentU d0 W.view.r1 H) tab e' :=
  S.nearU_behind1 (S.to1 u) h0 H tab hTab e'

/-- Behind "LIN point": the library's RecAll, WHERE THE KEY's SIZES FIT and each answer of the key
is its row's own. -/
theorem Steps.recRow_behind1 (S : Public8 P sentU layO d0) (u : StepTo1 B ft d0 W D)
    (h0 : d0.st.oracles.size = 0) (hkey : keyFits d0.loc.key P.par.S.fold.index = true)
    (hA : OwnAnswers P d0.loc.key H) :
    RecAll rdE P.par (uRK P.par D.d1) (words2 P sentU d0 W.view.r1 H) :=
  S.recRow_behind1 (S.to1 u) h0 hkey hA

/-- Behind the sending of o_u its sample rows hold, where what this sending shows is honest. -/
theorem Steps.sample_behind2 (S : Public8 P sentU layO d0) (u : StepTo2 B ft d0 W D)
    (hU : ShownU P sentU d0 W.view D H) :
    SmpSay d0.st.oracles.size D.d2 (words2 P sentU d0 W.view.r1 H) := by
  obtain ⟨x, ids, t⟩ := S.to2 u
  have k := S.sample_behind2 t (H := H) hU
  exact k

/-- Behind "(rec_gamma)" the rows on o_u's group hold, and they are just its own. Nothing is asked
of what is shown. -/
theorem Steps.recG_behind3 (S : Public8 P sentU layO d0) (u : StepTo3 B ft d0 W D)
    (hA : OwnAnswers P d0.loc.key H) :
    RowsUL rdE 0 P.par.S.fold.index.answers D.d3 (words2 P sentU d0 W.view.r1 H) ∧
      (rowsOn D.d3 D.d3.loc.gU).length = P.par.S.fold.index.answers := by
  obtain ⟨x, ids, t⟩ := S.to3 u
  have k := S.recG_behind3 t hA
  exact k

/-- Behind "LOC" the rows that it has laid hold, as many as locations were sampled. Nothing is asked
of what is shown. -/
theorem Steps.loc_behind4 (S : Public8 P sentU layO d0) (u : StepTo4 B ft d0 W D)
    (hC : OwnColumns P W.view H) :
    RowsUL rdE P.par.S.fold.index.answers P.par.S.fold.columns D.d4
        (words2 P sentU d0 W.view.r1 H) ∧
      (rowsOn D.d4 D.d4.loc.gU).length =
        P.par.S.fold.index.answers + P.par.S.fold.columns := by
  obtain ⟨x, ids, t⟩ := S.to4 u
  have k := S.loc_behind4 t hC
  exact k

/-- Behind the second sending o_omega's and o_sp's sample rows hold, where what this sending shows
is honest. -/
theorem Steps.sample_behind5 (S : Public8 P sentU layO d0) (u : StepTo5 B ft d0 W D)
    (hO : ShownO P sentU d0 W.view D H) :
    SmpSay (d0.st.oracles.size + 2) D.d5 (words2 P sentU d0 W.view.r1 H) ∧
      SmpSay (d0.st.oracles.size + 3) D.d5 (words2 P sentU d0 W.view.r1 H) := by
  obtain ⟨x, ids, x', ids', t⟩ := S.to5 u
  have k := S.sample_behind5 t (H := H) hO
  exact k

/-- Behind "LIN zeta" (fold)'s equation holds at the point noted. Nothing is asked of what is shown
or of the committed table. -/
theorem Steps.fold_behind7 (S : Public8 P sentU layO d0) (u : StepTo7 B ft d0 W D) (H : Inputs) :
    FoldAt rdE P.par.S D.d7 (words2 P sentU d0 W.view.r1 H) := by
  obtain ⟨x, ids, x', ids', t⟩ := S.to7 u
  have k := S.fold_behind7 t H
  exact k

/-- Behind "SPLIT" the last row on o_u's group holds, where the scalar shown is honest. -/
theorem Steps.foldU_behind8 (S : Public8 P sentU layO d0) (u : StepTo8 B ft d0 W D)
    (hM : ShownMu P d0 W.view H) :
    RowsU rdE (P.par.S.fold.index.answers + P.par.S.fold.columns) 1 D.d8
        (words2 P sentU d0 W.view.r1 H) ∧
      (rowsOn D.d8 D.d8.loc.gU).length =
        P.par.S.fold.index.answers + P.par.S.fold.columns + 1 := by
  obtain ⟨x, ids, x', ids', t⟩ := S.to8 u
  have k := S.foldU_behind8 t hM
  exact k

/-- Behind "SPLIT" the one row on o_omega's group holds, where the scalar shown is honest. -/
theorem Steps.foldOmega_behind8 (S : Public8 P sentU layO d0) (u : StepTo8 B ft d0 W D)
    (hM : ShownMu P d0 W.view H) :
    RowsO rdE 0 1 D.d8 (words2 P sentU d0 W.view.r1 H) ∧
      (rowsOn D.d8 D.d8.loc.gOmega).length = 1 := by
  obtain ⟨x, ids, x', ids', t⟩ := S.to8 u
  have k := S.foldOmega_behind8 t hM
  exact k

/-! ## The library's test on the state, from the steps up to there -/

/-- Behind "LIN point", WHERE THE KEY's SIZES FIT. -/
theorem Steps.shape1 (S : Public8 P sentU layO d0) (u : StepTo1 B ft d0 W D)
    (hkey : keyFits d0.loc.key P.par.S.fold.index = true) : shapeAtRun P d0 2 D.d1 = true :=
  S.shape1 (S.to1 u) hkey

/-- Behind the sending of o_u, WHERE THE KEY's SIZES FIT. -/
theorem Steps.shape2 (S : Public8 P sentU layO d0) (u : StepTo2 B ft d0 W D)
    (hkey : keyFits d0.loc.key P.par.S.fold.index = true) : shapeAtRun P d0 3 D.d2 = true := by
  obtain ⟨x, ids, t⟩ := S.to2 u
  have k := S.shape2 t hkey
  exact k

/-- Behind "(rec_gamma)". -/
theorem Steps.shape3 (S : Public8 P sentU layO d0) (u : StepTo3 B ft d0 W D) :
    shapeAtRun P d0 4 D.d3 = true := by
  obtain ⟨x, ids, t⟩ := S.to3 u
  have k := S.shape3 t
  exact k

/-- Behind "LOC". -/
theorem Steps.shape4 (S : Public8 P sentU layO d0) (u : StepTo4 B ft d0 W D) :
    shapeAtRun P d0 5 D.d4 = true := by
  obtain ⟨x, ids, t⟩ := S.to4 u
  have k := S.shape4 t
  exact k

/-- Behind the sending of o_omega and o_sp. -/
theorem Steps.shape5 (S : Public8 P sentU layO d0) (u : StepTo5 B ft d0 W D) :
    shapeAtRun P d0 6 D.d5 = true := by
  obtain ⟨x, ids, x', ids', t⟩ := S.to5 u
  have k := S.shape5 t
  exact k

/-- Behind the joinings. -/
theorem Steps.shape6 (S : Public8 P sentU layO d0) (u : StepTo6 B ft d0 W D) :
    shapeAtRun P d0 7 D.d6 = true := by
  obtain ⟨x, ids, x', ids', t⟩ := S.to6 u
  have k := S.shape6 t
  exact k

/-- Behind "LIN zeta". -/
theorem Steps.shape7 (S : Public8 P sentU layO d0) (u : StepTo7 B ft d0 W D) :
    shapeAtRun P d0 8 D.d7 = true := by
  obtain ⟨x, ids, x', ids', t⟩ := S.to7 u
  have k := S.shape7 t
  exact k

/-- Behind "SPLIT". -/
theorem Steps.shape8 (S : Public8 P sentU layO d0) (u : StepTo8 B ft d0 W D) :
    shapeAtRun P d0 9 D.d8 = true := by
  obtain ⟨x, ids, x', ids', t⟩ := S.to8 u
  have k := S.shape8 t
  exact k

/-! ## The state's codes, from the steps up to there -/

/-- The state's codes are the plan's behind "LIN point" (the library's codX). -/
theorem Steps.codes1 (S : Public8 P sentU layO d0) (u : StepTo1 B ft d0 W D) (j : Nat) :
    codX P j D.d1 = true :=
  S.codes1 (S.to1 u) j

/-- The state's codes are the plan's behind the sending of o_u (the library's codX). -/
theorem Steps.codes2 (S : Public8 P sentU layO d0) (u : StepTo2 B ft d0 W D) (j : Nat) :
    codX P j D.d2 = true := by
  obtain ⟨x, ids, t⟩ := S.to2 u
  have k := S.codes2 t j
  exact k

/-- The state's codes are the plan's behind "(rec_gamma)" (the library's codX). -/
theorem Steps.codes3 (S : Public8 P sentU layO d0) (u : StepTo3 B ft d0 W D) (j : Nat) :
    codX P j D.d3 = true := by
  obtain ⟨x, ids, t⟩ := S.to3 u
  have k := S.codes3 t j
  exact k

/-- The state's codes are the plan's behind "LOC" (the library's codX). -/
theorem Steps.codes4 (S : Public8 P sentU layO d0) (u : StepTo4 B ft d0 W D) (j : Nat) :
    codX P j D.d4 = true := by
  obtain ⟨x, ids, t⟩ := S.to4 u
  have k := S.codes4 t j
  exact k

/-- The state's codes are the plan's behind the sending of o_omega and o_sp (the library's codX). -/
theorem Steps.codes5 (S : Public8 P sentU layO d0) (u : StepTo5 B ft d0 W D) (j : Nat) :
    codX P j D.d5 = true := by
  obtain ⟨x, ids, x', ids', t⟩ := S.to5 u
  have k := S.codes5 t j
  exact k

/-- The state's codes are the plan's behind the joinings (the library's codX). -/
theorem Steps.codes6 (S : Public8 P sentU layO d0) (u : StepTo6 B ft d0 W D) (j : Nat) :
    codX P j D.d6 = true := by
  obtain ⟨x, ids, x', ids', t⟩ := S.to6 u
  have k := S.codes6 t j
  exact k

/-- The state's codes are the plan's behind "LIN zeta" (the library's codX). -/
theorem Steps.codes7 (S : Public8 P sentU layO d0) (u : StepTo7 B ft d0 W D) (j : Nat) :
    codX P j D.d7 = true := by
  obtain ⟨x, ids, x', ids', t⟩ := S.to7 u
  have k := S.codes7 t j
  exact k

/-- The state's codes are the plan's behind "SPLIT" (the library's codX). -/
theorem Steps.codes8 (S : Public8 P sentU layO d0) (u : StepTo8 B ft d0 W D) (j : Nat) :
    codX P j D.d8 = true := by
  obtain ⟨x, ids, x', ids', t⟩ := S.to8 u
  have k := S.codes8 t j
  exact k

/-! ## A member -/

/-- **What the theorems above ask, but for hTab, is met together at one member**, under the public
premises named: from the shared chain's first state at the written example's key there is a run of
all eight steps, with what is shown honest, at rows that are 0, whatever words lie in front and
whatever the random values of the four messages are. The view W stands behind "there is": of its
challenges the statement says nothing (they are ChainStepsMet.lean's written ones). -/
theorem steps_twins_met (P : P14) (sentU : Array OracleNotice) (layO : TreeLay)
    (hP : PlanFacts P.par P.codes sentU layO) (hBU : planOkOwn (parU P sentU) = true)
    (hBO : planOkOwn (parO P) = true) (B : Eight P) (w₀ : Words Cb.Gl.E)
    (cU cMask cOmega cSp : MsgCoins) (ft : Nat) :
    ∃ (W : Seen8) (D : States8),
      Start8 P sentU layO (firstW P) (inputs0 w₀ cU cMask cOmega cSp) ∧
      StepTo8 B ft (firstW P) W D ∧
      ShownU P sentU (firstW P) W.view D (inputs0 w₀ cU cMask cOmega cSp) ∧
      ShownO P sentU (firstW P) W.view D (inputs0 w₀ cU cMask cOmega cSp) ∧
      ShownMu P (firstW P) W.view (inputs0 w₀ cU cMask cOmega cSp) ∧
      OwnAnswers P (firstW P).loc.key (inputs0 w₀ cU cMask cOmega cSp) ∧
      OwnColumns P W.view (inputs0 w₀ cU cMask cOmega cSp) ∧
      keyFits (firstW P).loc.key P.par.S.fold.index = true ∧
      (firstW P).st.oracles.size = 0 := by
  obtain ⟨R2b, R5b, R8, d1, d2, d3, d4, d5, d6, d7, d8, s1, s2, s3, s4, s5, s6, s7, s8, _, e2, e5,
    e8, _⟩ := steps_met P sentU layO hP hBU hBO B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made w₀ cU
      cMask cOmega cSp [] [] ft
  exact ⟨⟨pointW P, seedsW (parU P sentU), R2b, rvPoss P.par.S.fold.columns, seedsW (parO P), R5b,
      zetaW P, R8, colW P⟩,
    ⟨d1, d2, d3, d4, d5, d6, d7, d8, inFrontOf d1, inFrontOf d1, #[], #[]⟩,
    ⟨⟨hP, hBU, hBO, rfl, rfl⟩, first_kept rdE P.codes _ w₀⟩,
    ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _, s1⟩⟩, ⟨_, _, s2⟩⟩, ⟨_, _, s3⟩⟩, ⟨_, s4⟩⟩, ⟨_, _, s5⟩⟩, ⟨_, _, s6⟩⟩, ⟨_, _, s7⟩⟩,
      ⟨_, _, s8⟩⟩,
    e2, e5, e8, rec_zero P.par.S.fold.index, col_zero P.par _, key_fits _, rfl⟩

end Desc.K14.Honest

#print axioms Desc.K14.Honest.Eight.stepTo1_of_fold
#print axioms Desc.K14.Honest.Eight.stepTo2_of_fold
#print axioms Desc.K14.Honest.Eight.stepTo3_of_fold
#print axioms Desc.K14.Honest.Eight.stepTo4_of_fold
#print axioms Desc.K14.Honest.Eight.stepTo5_of_fold
#print axioms Desc.K14.Honest.Eight.stepTo6_of_fold
#print axioms Desc.K14.Honest.Eight.stepTo7_of_fold
#print axioms Desc.K14.Honest.Eight.stepTo8_of_fold
#print axioms Desc.K14.Honest.Steps.met1
#print axioms Desc.K14.Honest.Steps.met2
#print axioms Desc.K14.Honest.Steps.met3
#print axioms Desc.K14.Honest.Steps.met4
#print axioms Desc.K14.Honest.Steps.met5
#print axioms Desc.K14.Honest.Steps.met6
#print axioms Desc.K14.Honest.Steps.met7
#print axioms Desc.K14.Honest.Steps.met8
#print axioms Desc.K14.Honest.Steps.omU_behind1
#print axioms Desc.K14.Honest.Steps.nearU_behind1
#print axioms Desc.K14.Honest.Steps.recRow_behind1
#print axioms Desc.K14.Honest.Steps.sample_behind2
#print axioms Desc.K14.Honest.Steps.recG_behind3
#print axioms Desc.K14.Honest.Steps.loc_behind4
#print axioms Desc.K14.Honest.Steps.sample_behind5
#print axioms Desc.K14.Honest.Steps.fold_behind7
#print axioms Desc.K14.Honest.Steps.foldU_behind8
#print axioms Desc.K14.Honest.Steps.foldOmega_behind8
#print axioms Desc.K14.Honest.Steps.shape1
#print axioms Desc.K14.Honest.Steps.shape2
#print axioms Desc.K14.Honest.Steps.shape3
#print axioms Desc.K14.Honest.Steps.shape4
#print axioms Desc.K14.Honest.Steps.shape5
#print axioms Desc.K14.Honest.Steps.shape6
#print axioms Desc.K14.Honest.Steps.shape7
#print axioms Desc.K14.Honest.Steps.shape8
#print axioms Desc.K14.Honest.Steps.codes1
#print axioms Desc.K14.Honest.Steps.codes2
#print axioms Desc.K14.Honest.Steps.codes3
#print axioms Desc.K14.Honest.Steps.codes4
#print axioms Desc.K14.Honest.Steps.codes5
#print axioms Desc.K14.Honest.Steps.codes6
#print axioms Desc.K14.Honest.Steps.codes7
#print axioms Desc.K14.Honest.Steps.codes8
#print axioms Desc.K14.Honest.steps_twins_met
