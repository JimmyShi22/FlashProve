-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/E2E/OutputHeadRowAtTheG.lean: THE OUTPUT HEAD's OWN ROUNDS (the kind K6): the kind's row
among the shares by kind (KindShare, Honest/Law/RowDebtsByKind.lean) at the lists
theGOfReturn made h T K, general in the relation and in the family of invariants. Calls alone.

WHAT IT IS NOT.
  * NOT ZERO KNOWLEDGE, NOT HIDING: one of sixteen shares that a conditional theorem
    (zeroKnowledgeOnServedRequests_atTheG, AtFullSide/T3/TheOneAtTheG.lean) takes as a premise; that
    file is NOT imported here: that the share fits its premise, at its relation and at its own
    words for the filling and the return, is shown by no theorem of this file (it is handed in as
    that premise's row K6 in AtFullSide/T3/TheRowsFilled.lean: zkOnServedRequests_fromRowsAtTheG).
  * No new law: the share and the line that the row stands are fields of HeadPaysAt
    (Honest/K6/Term/PaysAtTheG.lean), at the lists theGOfReturn made h T K.
  * UNDER laid: the kind's lot is among the lots of K; K is a letter: no value of it is laid here.
  * At this kind fresh is over no list, On holds always and bud bears no load: the share's weight is
    in fits and exact.
  * Nothing shows that a run ever calls the kind's parts: that is acceptance's, at the same lists.
  * AT THE BASE FILLING's return.

WHAT IS HERE. Three theorems, at every relation Rel and every family of invariants Th.
  k6Share_atTheG     the share of the kind K6
  k6Stands_atTheG    a list at the kind's place stands among the first chain's lists, with a side:
                     so the share is not over nothing
  sharesWithTheHeadsRowPaid   from the shares of the other kinds: the shares of all kinds

CALLED. headPays_at_theGOfReturn_at_the_base, HeadPaysAt.share (Honest/K6/Term/PaysAtTheG.lean).
-/
import Johnson.Desc.ProofFile.Honest.K6.Term.PaysAtTheG

set_option autoImplicit false
set_option maxRecDepth 100000
attribute [-instance] Inst.Model.Scl.ref

namespace AtPublicFiles.AtFiles.HonestTerm.OutputHead
open AtPublicFiles.AtFiles
open AtPublicFiles.TheG (ThreadParts theGOfReturn)
open AtPublicFiles.TheSides (KindRows)
open ProofFile.Honest (OnlineProverWithDescription Cells ThreadsP ready KindShare)
open ProofFile.Honest.K6 (headSimulatorLot headPays_at_theGOfReturn_at_the_base)
open ProofFile.Honest.Term (matrixInput baseMaker baseFilling)
open ProofFile.Honest.FirstThread (HeadAtReturn)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

variable {files : PublicFiles} {Wt : Type}

/-- CONDITIONAL: in scope; live; the base filling's return; the head at it; the kind's lot is among
the lots of K. **THE KIND's SHARE.** -/
theorem k6Share_atTheG
    (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    {A : OnlineProverWithDescription FullSizeMatrix ProofFile.Honest.IndexCommitterCoins Cells Unit Unit}
    (made : baseMaker files = .ok A)
    (h : HeadAtReturn files A) (T : ThreadParts A Wt) (K : KindRows (baseFilling files) A.Z A.G)
    (Rel : FullSizeMatrix → ProofFile.Honest.IndexCommitterCoins → ProofFile.Inst → Prop)
    (Th : ∀ w₀ rc ξ, Rel w₀ rc ξ → ∀ k R,
      ready A.F A.B ((theGOfReturn made h T K).prover A.H) w₀ rc ξ k = .ok R →
      ThreadsP A.F A.B ((theGOfReturn made h T K).prover A.H) w₀ rc ξ k R)
    (laid : headSimulatorLot (Rc := ProofFile.Honest.IndexCommitterCoins) (X := Unit) matrixInput.weights ∈ K.lots) :
    KindShare A (theGOfReturn made h T K) A.H Rel Th .K6 :=
  (headPays_at_theGOfReturn_at_the_base files scope live made h T K laid).share A.H Rel Th

/-- CONDITIONAL as k6Share_atTheG. **A LIST AT THE KIND's PLACE STANDS AMONG THE FIRST CHAIN's
LISTS, WITH A SIDE.** -/
theorem k6Stands_atTheG
    (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    {A : OnlineProverWithDescription FullSizeMatrix ProofFile.Honest.IndexCommitterCoins Cells Unit Unit}
    (made : baseMaker files = .ok A)
    (h : HeadAtReturn files A) (T : ThreadParts A Wt) (K : KindRows (baseFilling files) A.Z A.G)
    (laid : headSimulatorLot (Rc := ProofFile.Honest.IndexCommitterCoins) (X := Unit) matrixInput.weights ∈ K.lots) :
    ∃ L ∈ (theGOfReturn made h T K).first, L.place = IM.k6Place ∧
      ∃ σ, L.side A.F.first.blocksInOrder (theGOfReturn made h T K).falls₁ = some σ :=
  (headPays_at_theGOfReturn_at_the_base files scope live made h T K laid).stands

/-- CONDITIONAL as k6Share_atTheG. **THE SHARES OF ALL KINDS FROM THOSE OF THE OTHER KINDS.** -/
theorem sharesWithTheHeadsRowPaid
    (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    {A : OnlineProverWithDescription FullSizeMatrix ProofFile.Honest.IndexCommitterCoins Cells Unit Unit}
    (made : baseMaker files = .ok A)
    (h : HeadAtReturn files A) (T : ThreadParts A Wt) (K : KindRows (baseFilling files) A.Z A.G)
    (Rel : FullSizeMatrix → ProofFile.Honest.IndexCommitterCoins → ProofFile.Inst → Prop)
    (Th : ∀ w₀ rc ξ, Rel w₀ rc ξ → ∀ k R,
      ready A.F A.B ((theGOfReturn made h T K).prover A.H) w₀ rc ξ k = .ok R →
      ThreadsP A.F A.B ((theGOfReturn made h T K).prover A.H) w₀ rc ξ k R)
    (laid : headSimulatorLot (Rc := ProofFile.Honest.IndexCommitterCoins) (X := Unit) matrixInput.weights ∈ K.lots)
    (others : ∀ κ, κ ≠ .K6 →
      KindShare A (theGOfReturn made h T K) A.H Rel Th κ) :
    ∀ κ, KindShare A (theGOfReturn made h T K) A.H Rel Th κ := by
  intro κ
  by_cases isTheHead : κ = .K6
  · subst isTheHead
    exact k6Share_atTheG scope live made h T K Rel Th laid
  · exact others κ isTheHead

end AtPublicFiles.AtFiles.HonestTerm.OutputHead

#print axioms AtPublicFiles.AtFiles.HonestTerm.OutputHead.k6Share_atTheG
#print axioms AtPublicFiles.AtFiles.HonestTerm.OutputHead.k6Stands_atTheG
#print axioms AtPublicFiles.AtFiles.HonestTerm.OutputHead.sharesWithTheHeadsRowPaid
