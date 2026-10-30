-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/K1SocketsFilled.lean: the field planServes of TheThreadsHalf (AtFullSide/Honest/TheOneObject.lean), filled by
name, and the shared sending's (kind K1's) share of three more, at that file's own letters.

  1  planServes_filled    the field planServes: at every tied run the plan serves
  2  k1_five_filled       at every tied run and every value F of OpenFiles: FiveAtBorderJ at every place of the kind K1: K1's 52
                          of the 358 members of owes₁, yes₁ and carry₁
  3  an example           1 is laid into TheThreadsHalf

1: the library's planServes (Honest/Law/PlanGives.lean) at the run's own return of ready, from rootedSides_at_letters and
stored_at_letters (AtTheLetters.lean). 2: k1_five_at_letters at the run's R.

Limits.
  * made (the base maker returns) and the head h are hypotheses; in 1 also scope and live.
  * 1 says what PlanServes says: each round's tables are there with the declared sizes. Not what they hold.
  * 2 is a share, no field: it pays at the 52 members of the kind K1 alone; its limits are those of AtTheLetters.lean.
  * At the base prover. A tied run is a hypothesis' letter: that one exists is not shown here.
  * This file proves nothing about completeness, soundness or hiding.
-/
import AtFullSide.Honest.TheOneObject
import AtFullSide.K1.AtTheLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.Honest
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (tableCoins baseMaker)
open AtPublicFiles.AtFiles
open VerifierAndGoals (PublicFiles readFiles)
open VerifiableInference.Desc (KindName)

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]
variable {Z : PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (h : HeadAtReturn Z A)

variable {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)

/-- **The field planServes.** -/
theorem planServes_filled (made : baseMaker Z = .ok A) (scope : VerifierAndGoals.InScope Z = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) :
    ∀ r : TiedRun h hr, PlanServes A.H r.w.1 (tableCoins Z r.w.2.1) r.R :=
  fun r => planServes r.ready (head_planOk h.head) (TheLetters.rootedSides_at_letters h made)
    (TheLetters.stored_at_letters h made scope live r.w.1 r.w.2.1)

/-- **K1's share of owes₁, yes₁ and carry₁, at every tied run.** -/
theorem k1_five_filled (made : baseMaker Z = .ok A) (F : TheLetters.OpenFiles A) :
    ∀ r : TiedRun h hr, ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.K1 →
      FiveAtBorderJ (TheLetters.thread₁ h r.R) (TheLetters.said₁ h r.R) (TheLetters.J₁ h F)
        (fallsBy (TheLetters.falls₁ h) h.description.first.blocksInOrder) b :=
  fun r => TheLetters.k1_five_at_letters h made F r.R

/-- The field is laid into TheThreadsHalf. -/
example (made : baseMaker Z = .ok A) (scope : VerifierAndGoals.InScope Z = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) (others : TheThreadsHalf h hr) :
    TheThreadsHalf h hr :=
  { others with planServes := planServes_filled h hr made scope live }

end AtFullSide.Honest

#print axioms AtFullSide.Honest.planServes_filled
#print axioms AtFullSide.Honest.k1_five_filled
