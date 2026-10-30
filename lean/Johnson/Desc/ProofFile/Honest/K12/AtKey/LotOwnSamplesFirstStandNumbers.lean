-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/LotOwnSamplesFirstStandNumbers.lean: THE PUBLIC NUMBERS THAT
`first_chain_members_sample_rows_say` (LotOwnSamplesFirst.lean) ASKS, IN SCOPE: where W's sending stands in the key file's
first chain, how many rounds stand in front of it, how many messages the statement has at the chain's end, and what the two
written plans send. Public data and steps of the verifier's alone.

  `vector_w_block_number`          W's sending is sub-protocol number 17 of the first chain's 19
  `rounds_of_front`                (letters) the rounds of a list's first n sub-protocols, counted off the list's rows
  `rounds_in_front_of_vector_w`    18,848 rounds stand in front of it
  `written_rounds_in_front`, `written_rounds_in_front_of_seal`   the closed line on `fullFirst`, and a control: one row
                                   further the count is another
  `messages_at_first_chain_end`    a fold over the whole first chain ends at a statement of 11 messages
  `written_plans_send`             `parIK` sends one message, `parWK` two; the index masks' message and W's message 0 have
                                   an answer to a sample. By the kernel
  `written_rider_is_not_sampled`   a control: W's sending's message 1 has none

By what. `places_named` (E2E/KeyPlacesNamed.lean), `lengths` (E2E/KeyThreadFits.lean), `first_end_shape` (OwnShape.lean),
`Chain.flat_eq`.

Limits.
- In scope, at the full size. The fold is a premise.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.LotOwnSamplesFirst
import Johnson.Desc.ProofFile.Honest.K12.AtKey.OwnShape
import E2E.KeyPlacesNamed
import E2E.KeyThreadFits
import E2E.KeyJobW

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtKey
open OnBytes (OracleNotice)
open VerifiableInference.Desc (Block OpenedColumn foldBlocks)
open VerifiableInference.Desc.Key (Source LaterPlaces Claim FirstState descriptionFromSource sendW pieces rootsBefore batchRound)
open Johnson.Prover.Send (shapeAt)
open Johnson.RunOne.KeyKeeps (st₁)
open Johnson.RunOne.KeyMsg (bW)
open Johnson.RunOne.KeySendGood (gW)
open Johnson.RunOne.Sound (rowsOf)
open AtPublicFiles.KeyBook (fullFirst places_named)
open AtPublicFiles.KeyLay (parIK parWK)
open AtPublicFiles.AtFiles (KeySourced pubOf sh₁B CF)
open AtPublicFiles.AtFiles.Full (T19)

variable {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {Nr : H2U.PlaceNums} {Pl : LaterPlaces}

/-- **W's sending is sub-protocol number 17 of the first chain.** -/
theorem vector_w_block_number (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    {bw : Block FirstState Claim}
    (hb : sendW Xs.Y.k.oneTime pieces (rootsBefore Xs.Y.D.1 (batchRound Xs.Y.D.1)) (gW Xs) = some bw) :
    bW Xs Nr Pl = 17 := by
  have hback : (descriptionFromSource Xs Nr Pl).first.back.length = 4 := by
    show ([_, _, _] ++ (sendW Xs.Y.k.oneTime pieces (rootsBefore Xs.Y.D.1 (batchRound Xs.Y.D.1))
      (gW Xs)).toList).length = 4
    rw [hb]
    rfl
  have hlen : (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length = bW Xs Nr Pl + 2 := by
    rw [VerifiableInference.Desc.Chain.flat_eq]
    simp only [List.length_append, List.length_cons, List.length_map, List.length_nil, hback]
    unfold bW
    omega
  have h19 : (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length = 19 := (AtPublicFiles.KeyThread.lengths scope hs.named).1
  omega

/-- The rounds of a list's first n sub-protocols, counted off the list's rows. -/
theorem rounds_of_front {S Cl : Type} (bs : List (Block S Cl)) (n : ℕ) :
    ((bs.take n).flatMap (·.rounds)).length = (((rowsOf bs).take n).map (·.2)).sum := by
  unfold rowsOf
  rw [List.length_flatMap, ← List.map_take, List.map_map]
  rfl

/-- The closed line: the first 17 rows of the written list have 18,848 rounds. -/
theorem written_rounds_in_front : ((fullFirst.take 17).map (·.2)).sum = 18848 := by decide +kernel

/-- Control: the first 18 rows have another count. -/
theorem written_rounds_in_front_of_seal : ((fullFirst.take 18).map (·.2)).sum ≠ 18848 := by
  decide +kernel

/-- **18,848 rounds stand in front of W's sending.** -/
theorem rounds_in_front_of_vector_w (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    {bw : Block FirstState Claim}
    (hb : sendW Xs.Y.k.oneTime pieces (rootsBefore Xs.Y.D.1 (batchRound Xs.Y.D.1)) (gW Xs) = some bw) :
    (((descriptionFromSource Xs Nr Pl).first.blocksInOrder.take (bW Xs Nr Pl)).flatMap (·.rounds)).length = 18848 := by
  have r1 : rowsOf (descriptionFromSource Xs Nr Pl).first.blocksInOrder = fullFirst := (places_named scope hs.named).1
  rw [vector_w_block_number hs scope hb, rounds_of_front, r1]
  exact written_rounds_in_front

/-- The written shape at the first chain's end has 11 messages. By the kernel. -/
theorem written_messages_at_end : T19.1.st.oracles.length = 11 := by decide +kernel

/-- **A fold over the whole first chain ends at a statement of 11 messages.** -/
theorem messages_at_first_chain_end (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (x : (descriptionFromSource Xs Nr Pl).XiPub) {e₁ : FirstState} {r₁ : List Fmt.RoundView} {c₁ : List OpenedColumn}
    (first : foldBlocks 0 (descriptionFromSource Xs Nr Pl).first.blocksInOrder ((descriptionFromSource Xs Nr Pl).start₁ x) r₁ c₁ =
      .ok (e₁, [], [])) : (st₁ e₁).oracles.size = 11 := by
  have g := first_end_shape hs scope x first
  have e : (sh₁B (pubOf Xs) CF e₁).1.st.oracles.length = (st₁ e₁).oracles.size := by
    show ((st₁ e₁).oracles.toList.map VerifiableInference.Desc.Ground.Sh.orcSh).length = _
    rw [List.length_map, Array.length_toList]
  rw [← e, g]
  exact written_messages_at_end

/-- **What the two written plans send.** By the kernel. -/
theorem written_plans_send :
    parIK.sent.size = 1 ∧ parWK.sent.size = 2 ∧ (shapeAt parIK 0).answers ≠ 0 ∧
      (shapeAt parWK 0).answers ≠ 0 := by
  decide +kernel

/-- Control: the message that rides with W has no answer to a sample. -/
theorem written_rider_is_not_sampled : (shapeAt parWK 1).answers = 0 := by decide +kernel

end ProofFile.Honest.K12.AtKey

#print axioms ProofFile.Honest.K12.AtKey.vector_w_block_number
#print axioms ProofFile.Honest.K12.AtKey.rounds_of_front
#print axioms ProofFile.Honest.K12.AtKey.written_rounds_in_front
#print axioms ProofFile.Honest.K12.AtKey.written_rounds_in_front_of_seal
#print axioms ProofFile.Honest.K12.AtKey.rounds_in_front_of_vector_w
#print axioms ProofFile.Honest.K12.AtKey.written_messages_at_end
#print axioms ProofFile.Honest.K12.AtKey.messages_at_first_chain_end
#print axioms ProofFile.Honest.K12.AtKey.written_plans_send
#print axioms ProofFile.Honest.K12.AtKey.written_rider_is_not_sampled
