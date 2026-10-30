-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/StandsAtServedHasAMember.lean

E2E/TheHonestProverNotTaken.lean states its propositions on the honest prover's default branches
under the premise StandsAtServed. This file shows that this premise can be met: at every served
input there is a list of challenges of the declared form at which no stopping rule of the honest
online prover fires, and a served input exists. The header of CompleteAtTheFiles.lean explains the
terms.

Main statements. All but the first are conditional on h : HeadAtReturn Z A, on the return A of the
base construction (made), on protocolDataWellFormed (asDescriptionFiles Z) = true and on readFiles Z = .ok pp (hr).
  * silentAt_reads_four: silentAt (Johnson/Desc/ProofFile/Honest/Rule.lean) is the function that
    says whether, and by which rule, the honest prover stops at a list of challenges. It depends on
    a prover only through the prover's trace and its three lists first, shared and second.
  * someMessageIsNotWithheld: at a served request, for every randomness r : (protocolAtFiles Z).EncodingRandomness of the table
    and every e : (protocolAtFiles Z).OutOfDomainSeed, some message of the verifier lies outside the abort set (withheld) of
    the honest online prover, at copy number 0.
  * aDueListWithNoStopAtEveryServedInput: every served input has a list of challenges with
    StandsAtServed.
  * standsAtServedHasAMember: for every r and e as above there are a matrix, an input and a list of
    challenges with StandsAtServed.

Limits.
  * StandsAtServed has three clauses on an input and a list of challenges: the input is served, the
    list has the declared form, and no stopping rule fires. It does not say that the run succeeds at
    that list, that a verifier accepts, or that the run reaches any given position: midAtW and
    similar functions are not used here.
  * The list is obtained by a counting argument: the lists at which a stopping rule fires have
    probability at most 2^(-174), so some list lies outside them. Nothing computes the list, and
    nothing is said of which list it is.
  * silentAt also returns none where the prover has no trace for the request. These theorems do not
    say that a trace exists.
  * That a served input exists rests on servedRequest_met, which is shown at made-up weights
    (Meaning.served_met) and says nothing of a real model's weights.
  * The prover is that of onlineReturn Z A, which is the return A of the base construction with its
    randomness supplied by the table's coins, under h.
  * The statements hold for the full-size layout and for the format's second hash function,
    OnBytes.secondHashFunction, alone.
  * Nothing on completeness, on soundness or on what a proof hides.

Built on.
  * hid_at_the_capstone (AtFullSide/K8/HidAtTheCapstone.lean) and bad_at_the_online_return
    (AtFullSide/Honest/TheCapstoneFromTheObject.lean), which bound the two parts of the abort set by
    2^(-174) and by 0.
  * withheldC_iff (Johnson/Desc/ProofFile/Honest/Law/ThreadStratC.lean) and due_laid
    (Johnson/Desc/ProofFile/Honest/Law/DueHead.lean).
  * every_served_request_is_tied (AtFullSide/Honest/TheOneObject.lean) and servedRequest_met
    (E2E/CompleteAsIOPServedLaws.lean).
-/
import AtFullSide.Honest.TheCapstoneFromTheObject
import E2E.TheHonestProverNotTaken
import Johnson.Desc.ProofFile.Honest.Law.DueHead
import Johnson.Desc.ProofFile.Honest.Law.ThreadStratC
import Johnson.FrontRoad.SessionHid

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtFullSide.Honest
open Iop Prob
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (matrixInput matrixFilling tableCoins onlineMaker OnlineReturn)
open AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm AtPublicFiles.Bridge AtPublicFiles.Committed AtPublicFiles.TheFalls
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open OnBytes.Flat (front₀ join₀)
open _root_.Run (ckP)
open VerifierAndGoals (PublicFiles readFiles InScope)
open FlashProve (dataAtFiles)
open FlashProve (committerCoinCountLessOne flashProveData protocolDataWellFormed)
open LPFD.Full (instanceAsPlainRecord)

local instance (priority := high) nonemptyPadZ_standsAtServed : Nonempty PadZ :=
  pads_nonempty frS 402653181

local instance (priority := high) nonemptyRunValue_standsAtServed : Nonempty RunValue :=
  ⟨fun _ => 0⟩

local instance (priority := high) inhabitedRunValue_standsAtServed : Inhabited RunValue :=
  ⟨fun _ => 0⟩

/-- silentAt depends on a prover only through its trace and its three lists first, shared and
second. -/
theorem silentAt_reads_four {Xi W₀ Rc Ky Tr X₀ X : Type} (F : VerifiableInference.Desc.FileDescription Xi)
    {H H' : Prover W₀ Rc Xi Ky Tr X₀ X} (trace : H.trace = H'.trace) (first : H.first = H'.first)
    (shared : H.shared = H'.shared) (second : H.second = H'.second) (w₀ : W₀) (rc : Rc) (x : Xi)
    (ρ : Draws) : silentAt F H w₀ rc x ρ = silentAt F H' w₀ rc x ρ := by
  unfold silentAt
  rw [trace, first, shared, second]
  rfl

variable {Z : PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} {h : HeadAtReturn Z A}
  {pp : Inst.Model.ScalesAndPolicy} {hr : readFiles Z = .ok pp}

/-- Conditional on h, on the return of the base construction and on protocolDataWellFormed. At a served request,
for every r and e, some message of the verifier lies outside the abort set: the set has probability
at most 0 + 2^(-174), which is less than 1. -/
theorem someMessageIsNotWithheld
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (live : protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) (i : FullSizeMatrix) (r : (protocolAtFiles Z).EncodingRandomness) (e : (protocolAtFiles Z).OutOfDomainSeed)
    (x' : LPFD.Full.XF) (served : ServedRequest committerCoinCountLessOne Z hr i x') :
    ∃ ρ, ρ ∉ ((famG Z (onlineReturn Z A).Z h.places h.firstChain runValueBytes runValueBytes
      (onlineReturn Z A).B (theSides h) (onlineReturn Z A).H).at 0).withheld (i, r, e)
        (x', (protocolAtFiles Z).recOf i r e) := by
  have tied := every_served_request_is_tied (h := h) (hr := hr) h.head.scope 0 i r e x' served
  have hid := hid_at_the_capstone h.head.scope hr live (onlineMaker_returns made)
    h.head.toAtMg.laid.places h.head.toAtMg.laid.chain _ (theSides_fit (h := h)).prover 0 (i, r, e)
    (x', (protocolAtFiles Z).recOf i r e) tied.2
  have bad := bad_at_the_online_return made h.places h.firstChain (theSides h)
    (theSides_fit (h := h)).prover
  by_contra all
  push_neg at all
  have one := pr_eq_one_of_support_subset (unif _) (E := ((famG Z (onlineReturn Z A).Z h.places
    h.firstChain runValueBytes runValueBytes (onlineReturn Z A).B (theSides h)
    (onlineReturn Z A).H).at 0).withheld (i, r, e) (x', (protocolAtFiles Z).recOf i r e)) fun ρ _ => all ρ
  have le := pr_union_le (unif _) ((famG Z (onlineReturn Z A).Z h.places h.firstChain runValueBytes
    runValueBytes (onlineReturn Z A).B (theSides h) (onlineReturn Z A).H).at 0).Bad
    (((famG Z (onlineReturn Z A).Z h.places h.firstChain runValueBytes runValueBytes
      (onlineReturn Z A).B (theSides h) (onlineReturn Z A).H).at 0).Hid (i, r, e)
      (x', (protocolAtFiles Z).recOf i r e))
  have small : (1 : ℝ≥0∞) ≤ 0 + ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ)) :=
    one.symm.le.trans (le.trans (add_le_add bad hid))
  rw [zero_add] at small
  have lt : ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ)) < 1 := by
    rw [← ENNReal.ofReal_one]
    refine (ENNReal.ofReal_lt_ofReal_iff one_pos).2 ?_
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  exact absurd small (not_le.2 lt)

/-- Conditional on h, on the return of the base construction and on protocolDataWellFormed. At every served input
some list of challenges of the declared form triggers no stopping rule. -/
theorem aDueListWithNoStopAtEveryServedInput
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (live : protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) (matrix : FullSizeMatrix) (coins : (protocolAtFiles Z).EncodingRandomness)
    (input : ProofFile.Inst) (served : ServedInput (ServedRequest committerCoinCountLessOne Z hr) Z matrix coins input) :
    ∃ challenges, StandsAtServed (ServedRequest committerCoinCountLessOne Z hr) (onlineReturn Z A) h.places
      h.firstChain matrix coins input challenges := by
  obtain ⟨x', e, isServed, rfl⟩ := served
  obtain ⟨ρ, out⟩ := someMessageIsNotWithheld (h := h) made live matrix coins e x' isServed
  refine ⟨drawsAt (ckP .two) (dataZ Z) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
    (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty ρ, ⟨x', e, isServed, rfl⟩,
    due_laid h.head.scope h.head.toAtMg.laid _ _ _ ρ, ?_⟩
  have same := silentAt_reads_four (descZ (onlineReturn Z A).Z h.places h.firstChain)
    (H := provG Z (onlineReturn Z A).Z h.places h.firstChain (onlineReturn Z A).B (theSides h)
      (onlineReturn Z A).H) (H' := (onlineReturn Z A).H) rfl
    (congrArg (·.first) (theSides_fit (h := h)).prover)
    (congrArg (·.shared) (theSides_fit (h := h)).prover)
    (congrArg (·.second) (theSides_fit (h := h)).prover) matrix coins
    (instanceAsPlainRecord (x', (protocolAtFiles Z).recOf matrix coins e))
    (drawsAt (ckP .two) (dataZ Z) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
      (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty ρ)
  rw [← same]
  by_cases hasTrace : ((provG Z (onlineReturn Z A).Z h.places h.firstChain (onlineReturn Z A).B
      (theSides h) (onlineReturn Z A).H).trace matrix
      (instanceAsPlainRecord (x', (protocolAtFiles Z).recOf matrix coins e))).isSome = true
  · have iff := withheldC_iff (ckP .two) (dataZ Z) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
      (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty
      (descZ (onlineReturn Z A).Z h.places h.firstChain) silInst (onlineReturn Z A).B
      (provG Z (onlineReturn Z A).Z h.places h.firstChain (onlineReturn Z A).B (theSides h)
        (onlineReturn Z A).H) (seamZ Z runValueBytes runValueBytes 0)
      (shAt (onlineReturn Z A).Z h.places h.firstChain) (extZ Z) (matrix, coins, e)
      (instanceAsPlainRecord (x', (protocolAtFiles Z).recOf matrix coins e)) hasTrace ρ
    exact Option.not_isSome_iff_eq_none.1 fun some => out (iff.2 some)
  · unfold silentAt
    rw [Option.not_isSome_iff_eq_none.1 hasTrace]
    rfl

/-- Conditional on h, on the return of the base construction and on protocolDataWellFormed. StandsAtServed has a
member, for every r : (protocolAtFiles Z).EncodingRandomness and every value of (protocolAtFiles Z).OutOfDomainSeed. -/
theorem standsAtServedHasAMember
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (live : protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) (coins : (protocolAtFiles Z).EncodingRandomness) (seed : (protocolAtFiles Z).OutOfDomainSeed) :
    ∃ matrix input challenges, StandsAtServed (ServedRequest committerCoinCountLessOne Z hr) (onlineReturn Z A)
      h.places h.firstChain matrix coins input challenges := by
  obtain ⟨i, x', isServed⟩ := servedRequest_met committerCoinCountLessOne Z h.head.scope hr
  obtain ⟨challenges, stands⟩ := aDueListWithNoStopAtEveryServedInput (h := h) made live i coins
    (instanceAsPlainRecord (x', (protocolAtFiles Z).recOf i coins seed)) ⟨x', seed, isServed, rfl⟩
  exact ⟨i, _, challenges, stands⟩

end AtFullSide.Honest

#print axioms AtFullSide.Honest.silentAt_reads_four
#print axioms AtFullSide.Honest.someMessageIsNotWithheld
#print axioms AtFullSide.Honest.aDueListWithNoStopAtEveryServedInput
#print axioms AtFullSide.Honest.standsAtServedHasAMember
