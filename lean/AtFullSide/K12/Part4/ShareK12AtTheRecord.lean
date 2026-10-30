-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/Part4/ShareK12AtTheRecord.lean

This file joins theorems of other files into one statement: the KindShare of the kind K12 at the
family of invariants TheThreadsHalf.threadsAtRelation (AtFullSide/Honest/TheCrossing.lean), at the
rows theKOfRecord (E2E/TheKValue.lean) and at the relation BaseRel (AtFullSide/T3/HstAtBase.lean).

Terms
  * A kind (VerifiableInference.Desc.KindName) is one of sixteen labels, K1 to K15 and frame, that
    the places of the proof file's description carry. KindShare
    (Johnson/Desc/ProofFile/Honest/Law/RowDebtsByKind.lean) bundles three conditions on one kind,
    which later theorems take as premises.
  * made says that the builder onlineProverFromPublicFiles, at OnBytes.secondHashFunction and at the argument matrixFilling, returns
    A. h (HeadAtReturn Z A) holds the data from which the online description is made at A. O is a
    value of TheThreadsHalf h hr, the first half of the structure from which completeness is proved.
    T holds the arguments of the three threads. hRel says that every input of the relation is a tied
    request (TiedRequest).

Main statements
  k12_share_of_the_half
      Premises: made, O, T, hRel, a value E of TheThirteen, apart (the names of its entries differ)
      and slot₁₂ (its entry for K12 holds simulatorLot). Conclusion: the KindShare of K12 at the
      rows theK E apart (laterOurs A h.head), the relation K12Rel Z Ry and the family
      O.threadsAtRelation.
  an example
      BaseRel Z hr is K12Rel Z at the served requests, by rfl.
  k12_share_at_the_record
      Premises: made, O, T and hRel alone; apart and slot₁₂ are proved at theThirteen. Conclusion:
      the KindShare of K12 at the rows theKOfRecord A h.head, the relation BaseRel Z hr and the
      family O.threadsAtRelation.

Limits
  * This file makes no statement on what a proof hides, and none on completeness or soundness. A
    KindShare is a bundle of conditions that a later theorem takes as a premise; what follows from
    it is stated there.
  * The statements are conditional. Beside made and h, the premises O and hRel remain, and T is an
    argument. AtFullSide/E2E/ZeroKnowledgeFromWhatIsLeftAtRecord.lean (theHalf,
    thePartsOfTheThreads) and AtFullSide/E2E/ZeroKnowledgeFromWhatIsLeft.lean (baseRel_is_tied)
    supply them.
  * A KindShare can hold vacuously. This file does not state that the sides G hold a list of the
    kind K12, nor that a part of a test is called at any run.
  * The first condition of the KindShare asks the fields fits, exact and fresh of Good, at each
    list's own On and bud. It leaves the other fields of Good unasked, by asking them under a
    premise that never holds. The limits of AtFullSide/K12/ShareK12AtTheK.lean apply.
  * The statements are at the argument matrixFilling of onlineProverFromPublicFiles, which the files of AtFullSide/E2E
    call baseFilling, not at the argument that the online prover reads.
  * They hold for the format's second hash function OnBytes.secondHashFunction alone, and say nothing about the
    C++ programs.
  * The proofs in this file only combine theorems of other files, and every limit of these files
    applies here.

Built on
  * AtFullSide/K12/ShareK12OfTheObject.lean: k12_share_of_the_object.
  * AtFullSide/K12/MembershipsAtTheK.lean: k12_hK₀_at_theK to k12_hK₄_at_theK.
  * AtFullSide/K12/ShareK12AtTheK.lean: k12_pays_at_theK.
  * AtFullSide/K12/FirstBudK12.lean: k12_bud₁_at_theGOfReturn.
  * Johnson/Desc/ProofFile/Honest/K12/Sim2/K12OnAtTheG.lean: k12_on₁_at_the_g.
  * AtFullSide/Honest/TheCrossing.lean: TheThreadsHalf.threadsAtRelation_I.
  * E2E/TheThirteenOfRecord.lean: theThirteen_apart. AtFullSide/K12/K12Entry.lean: k12Entry_slot.
-/
import AtFullSide.K12.ShareK12OfTheObject
import AtFullSide.K12.ShareK12AtTheK
import AtFullSide.K12.FirstBudK12
import Johnson.Desc.ProofFile.Honest.K12.Sim2.K12OnAtTheG
import AtFullSide.Honest.TheCrossing
import AtFullSide.T3.HstAtBase
import E2E.TheKValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.K12
open VerifiableInference.Desc (KindName)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Sim2
open ProofFile.Honest.FirstThread (HeadAtReturn)
open ProofFile.Honest.Term (matrixInput matrixFilling tableCoins baseFilling)
open AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm AtPublicFiles.TheSides AtPublicFiles.TheG
open VerifierAndGoals (readFiles)
open LPFD.Full (XF)
open FlashProve (committerCoinCountLessOne)
open VerifiableInference.Compilation (BaseRel)
open AtFullSide.Honest AtFullSide.Honest.TheLetters

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]
variable {Z : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} {h : HeadAtReturn Z A}
  {pp : Inst.Model.ScalesAndPolicy} {hr : readFiles Z = .ok pp} {Wt : Type}

set_option maxHeartbeats 4000000 in
/-- The KindShare of the kind K12 at the family O.threadsAtRelation and at the rows theK E apart
(laterOurs A h.head), for any value O of TheThreadsHalf h hr. Conditional: the premises are listed
at the head of this file. -/
theorem k12_share_of_the_half
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (O : TheThreadsHalf h hr) (T : ThreadParts A Wt)
    (E : TheThirteen (baseFilling Z) A.Z A.G) (apart : (E.entries.map (·.slot.name)).Nodup)
    (slot₁₂ : E.k12.slot = simulatorLot (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref)
    (Ry : FullSizeMatrix → XF → Prop)
    (hRel : ∀ w₀ rc x, K12Rel Z Ry w₀ rc x → ∃ n w, w.1 = w₀ ∧ tableCoins Z w.2.1 = rc ∧
      TiedRequest h hr n w x) :
    KindShare A (theGOfReturn made h T (theK E apart (AtFullSide.M1.laterOurs A h.head))) A.H
      (K12Rel Z Ry)
      (O.threadsAtRelation made
        (theGOfReturn made h T (theK E apart (AtFullSide.M1.laterOurs A h.head)))
        (theGOfReturn_prover made h T (theK E apart (AtFullSide.M1.laterOurs A h.head))) hRel)
      KindName.K12 :=
  k12_share_of_the_object made O T (theK E apart (AtFullSide.M1.laterOurs A h.head))
    (k12_hK₁_at_theK h E apart) (k12_hK₂_at_theK h E apart) (k12_hK₃_at_theK h E apart)
    (k12_hK₄_at_theK h E apart) Ry hRel (k12_pays_at_theK made h T E apart slot₁₂)
    (k12_on₁_at_the_g made h T (theK E apart (AtFullSide.M1.laterOurs A h.head))
      (k12_hK₀_at_theK E apart _ slot₁₂) _
      (fun w₀ rc x hrel k R hR => (O.threadsAtRelation_I made _ _ hRel w₀ rc x hrel k R hR).1))
    (k12_bud₁_at_theGOfReturn made h T (theK E apart (AtFullSide.M1.laterOurs A h.head))
      (k12_hK₀_at_theK E apart _ slot₁₂))

/-- BaseRel and K12Rel at the served requests are the same term. -/
example : BaseRel Z hr = K12Rel Z (ServedRequest committerCoinCountLessOne Z hr) := rfl

set_option maxHeartbeats 4000000 in
/-- The KindShare of the kind K12 at the rows theKOfRecord and the relation BaseRel, for any value O
of TheThreadsHalf h hr and any arguments T of the threads. Conditional on made, O and hRel. -/
theorem k12_share_at_the_record
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (O : TheThreadsHalf h hr) (T : ThreadParts A Wt)
    (hRel : ∀ w₀ rc x, BaseRel Z hr w₀ rc x → ∃ n w, w.1 = w₀ ∧ tableCoins Z w.2.1 = rc ∧
      TiedRequest h hr n w x) :
    KindShare A (theGOfReturn made h T (theKOfRecord A h.head)) A.H (BaseRel Z hr)
      (O.threadsAtRelation made (theGOfReturn made h T (theKOfRecord A h.head))
        (theGOfReturn_prover made h T (theKOfRecord A h.head)) hRel)
      KindName.K12 :=
  k12_share_of_the_half made O T (theThirteen Z A.Z A.G) (theThirteen_apart Z A.Z A.G)
    (k12Entry_slot Z A.Z A.G) (ServedRequest committerCoinCountLessOne Z hr) hRel

end AtFullSide.K12

#print axioms AtFullSide.K12.k12_share_of_the_half
#print axioms AtFullSide.K12.k12_share_at_the_record
