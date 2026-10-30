-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotJoinFirstStruck.lean: WHAT IS LEFT OF THE FIRST CHAIN AT THE JOIN (LeftJoin, E2E/LotJoinFirst.lean), WITH ITS TWO LAST FIELDS
STRUCK, now that HeardOfFold is had in scope (E2E/LotHeardOfFold.lean): the field pile (ExchangeS at 16: three items)
falls to one named premise on coins, CoinsAtSlots (E2E/FirstHPile.lean); the field eval ((Eval) at 17) falls whole.

  LeftJoinStruck d Q w x   what is left: LeftJoin's five other fields, to the letter, and coins : CoinsAtSlots at the
                  join's thread
  leftJoin_of_struck   LeftJoin from it, in scope
  joinFirstStruck   so OwesS and YesS of the first chain at the join, from it

By what. exchange_batt and eval_item (E2E/FirstHEvalDone.lean), w_public (E2E/FirstHWPublic.lean); their premises
FirstPublic by firstPublic_atValue (E2E/LotFirstPublicAtValue.lean), HeardOfFold by lotHeardOfFold. Calls alone.

WHAT FALLS: at 16: the items pile, pinT and pin 0 as debts at a stand; at 17: (Eval). WHAT STAYS: CoinsAtSlots
· PlaysS and ExchangeS at 4, 10 · ExchangeS at 5, 11 · PlaysS and AcceptedS at 15.

Limits. AN IMPLICATION: no member of LeftJoinStruck is known at any input. All limits of E2E/LotJoinFirst.lean stand.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.LotJoinFirst
import E2E.LotHeardOfFold
import E2E.FirstHEvalDone
import E2E.FirstHWPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.FirstH.Lots
open VerifiableInference.Desc.Key (Xi)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription FullSizeMatrix protocolAtFiles)
open AtPublicFiles.AtFiles.HonestTerm (OfflineDescription offlineDescription matrixReader)
open AtPublicFiles.KeyStandWalked (offlineValue)
open AtPublicFiles.KeyBook (KeyPub keyBook)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest

section
variable {Z : PublicFiles} {K₀ : KeyPub} (d : OfflineDescription)
  (Q : LaterFill (keyBook K₀) FullSizeMatrix (protocolAtFiles Z).EncodingRandomness)

/-- **What is left of the first chain at the join, its two last fields struck.** A premise's form. -/
structure LeftJoinStruck (w : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed) (x : Xi) : Prop where
  playsK3 : ∀ b ∈ [4, 10], PlaysS (joinThread d Q w x) (joinSaid d Q w x) b
  exchangeK3 : ∀ b ∈ [4, 10], ExchangeS (joinThread d Q w x) (joinSaid d Q w x) b
  exchangeLayer : ∀ b ∈ [5, 11], ExchangeS (joinThread d Q w x) (joinSaid d Q w x) b
  playsRanges : PlaysS (joinThread d Q w x) (joinSaid d Q w x) 15
  acceptedRanges : AcceptedS (joinThread d Q w x) (joinSaid d Q w x)
    (fallsBy [] (keyFileDescription d.source d.numbers d.later).first.blocksInOrder) 15
  coins : CoinsAtSlots d.source d.numbers d.later (offlineValue (files := Z) d) matrixReader Q w.1
    w.2.1 x

variable {d Q}

/-- **LeftJoin from it.** -/
theorem leftJoin_of_struck (hs : KeySourced Z d.source d.numbers d.later) (scope : InScope Z = true)
    {w : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed} {x : Xi} (left : LeftJoinStruck d Q w x) :
    LeftJoin d Q w x where
  playsK3 := left.playsK3
  exchangeK3 := left.exchangeK3
  exchangeLayer := left.exchangeLayer
  playsRanges := left.playsRanges
  acceptedRanges := left.acceptedRanges
  pile := exchangeS_of _ _
    (exchange_batt hs scope (firstPublic_atValue hs scope) (lotHeardOfFold hs scope) left.coins)
  eval := fun _ hb _ _ _ _ _ _ _ _ hT hd hS =>
    eval_item hs scope (firstPublic_atValue hs scope) (w_public hs scope) (lotHeardOfFold hs scope)
      hb hT hd hS

/-- **So the first chain's debts and its yes at the join.** -/
theorem joinFirstStruck (hd : offlineDescription Z = .ok d) (scope : InScope Z = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (hQ : Q.kind₁ = kindFirst d.source d.numbers)
    {w : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed} {x : Xi} (left : LeftJoinStruck d Q w x) :
    OwesS (joinThread d Q w x) (joinSaid d Q w x) ∧
      YesS (joinThread d Q w x) (joinSaid d Q w x)
        (fallsBy [] (keyFileDescription d.source d.numbers d.later).first.blocksInOrder) :=
  joinFirst hd scope live hQ (leftJoin_of_struck (sourced_of_description hd live) scope left)

end

end AtPublicFiles.FirstH.Lots

#print axioms AtPublicFiles.FirstH.Lots.leftJoin_of_struck
#print axioms AtPublicFiles.FirstH.Lots.joinFirstStruck
