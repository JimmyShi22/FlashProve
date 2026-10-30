-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/LotOwnSamplesFirstStand.lean: AT A STAND IN FRONT OF THE KEY FILE's OWN TEST, IN SCOPE,
THE SAMPLE ROWS OF THE OWN GROUP's TWO MEMBERS THAT THE FIRST CHAIN SENT (numbers 0 and 9 of the statement) SAY THEIR CLAIMS
OF THE TERM `wordsAtKeyOwnTest` (LotOwnWords.lean) AT THE FULL SIZE's NUMBERS: `first_chain_members_sample_rows_say`
(LotOwnSamplesFirst.lean) with every public premise paid.

  `challengesBeforeVectorWAtFullSize`   18,848
  `first_members_say_at_folds`   at the verifier's three folds
  `first_members_say_at_stand`   THE END: at a thread's stand: `Thread.Made` at border 2, the two earlier chains' folds at the
                                 head of what was seen (`ProofFile.Honest.K12.AtFile.EndsAre`), and the thread's first state is the
                                 description's start

What stays a premise.
- `SendersPlansAlike K` (LotOwnAlike.lean): the parts' two plans have the written notices and codes. On the parts.
- `SendersAnswersSeen` on what the stand has seen (m.seen). IT CAN SAY NO: LotOwnSamplesFirst.lean's head.
- The stand's three clauses (made, ends, begins).
No premise on numbers, plans of the verifier's, rounds or counts is left.

By what. LotOwnSamplesFirstStandPlans.lean, LotOwnSamplesFirstStandNumbers.lean, `public_samples` (OwnSamplesAt.lean),
`answersSeen_of_longer`.

Limits.
- SPEAKS OF ANSWERS, WHICH HANG ON THE PADS.
- In scope, at the full size. That a run reaches a stand is not said.
- Of Omega's copy (number 11), of the open rows and of `WordsTied` nothing is said here.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.LotOwnSamplesFirstStandPlans
import Johnson.Desc.ProofFile.Honest.K12.AtKey.LotOwnSamplesFirstStandNumbers
import Johnson.Desc.ProofFile.Honest.K12.AtKey.LotOwnAlike
import Johnson.Desc.ProofFile.Honest.K12.AtKey.OwnSamplesAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtKey
open OnBytes.Slice (rdE)
open OnBytes.Means (SampleSays)
open VerifiableInference.Desc (Block OpenedColumn foldBlocks)
open VerifiableInference.Desc.Key (Source LaterPlaces Xi Claim FirstState descriptionFromSource)
open VerifiableInference.Desc.Third (S₃)
open Johnson.Prover.Send (shapeAt)
open AtPublicFiles.KeyFile (KeyParts In1)
open AtPublicFiles.KeyLay (parIK parWK)
open AtPublicFiles.AtFiles (KeySourced)
open _root_.Desc.K14 (St)

/-- How many challenges of the first chain stand in front of W's sending, at the full size. -/
def challengesBeforeVectorWAtFullSize : ℕ := 18848

variable {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {Nr : H2U.PlaceNums} {Pl : LaterPlaces}
  {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk : Type}

/-- **At the verifier's three folds**, in scope. SPEAKS OF ANSWERS, WHICH HANG ON THE PADS. -/
theorem first_members_say_at_folds (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (K : KeyParts W₀ Rc X₀ X Wk) (senders : SendersPlansAlike K) (challengesOfFirstChain : ℕ)
    (k : Coins Bk) (input : In1 W₀ Rc) (heard : List Fmt.Drawn)
    {x : (descriptionFromSource Xs Nr Pl).XiPub} {e₁ : FirstState} {e₂ : St} {s₀ st : S₃} {ft : ℕ}
    {r₁ rs : List Fmt.RoundView} {c₁ cols : List OpenedColumn}
    (first : foldBlocks 0 (descriptionFromSource Xs Nr Pl).first.blocksInOrder ((descriptionFromSource Xs Nr Pl).start₁ x) r₁ c₁ = .ok (e₁, [], []))
    (start : (descriptionFromSource Xs Nr Pl).start₃ x e₁ e₂ = .ok s₀)
    (last : foldBlocks ft ((descriptionFromSource Xs Nr Pl).second.blocksInOrder.take 2) s₀ rs cols = .ok (st, [], []))
    (seen : SendersAnswersSeen K
      (numbersAtFullSize challengesBeforeVectorWAtFullSize challengesOfFirstChain) k input heard r₁) :
    SampleSays rdE st.st 0 (wordsAtKeyOwnTest K
        (numbersAtFullSize challengesBeforeVectorWAtFullSize challengesOfFirstChain) k input heard) ∧
      SampleSays rdE st.st 9 (wordsAtKeyOwnTest K
        (numbersAtFullSize challengesBeforeVectorWAtFullSize challengesOfFirstChain) k input heard) := by
  obtain ⟨bw, msg, hb, hm, -, -, -⟩ := public_samples hs scope
  obtain ⟨n1, n2, a1, a2⟩ := written_plans_send
  obtain ⟨alikeI, alikeW⟩ := plans_alike_at_description hs scope hm
    (indexMasksPlan := K.idx.P) (vectorWPlan := K.w.P)
    ⟨senders.indexMasksNotices, senders.indexMasksCodes⟩
    ⟨senders.vectorWNotices, senders.vectorWCodes⟩
  have sI : K.idx.P.sent.size = 1 := by rw [senders.indexMasksNotices]; exact n1
  have sW : K.w.P.sent.size = 2 := by rw [senders.vectorWNotices]; exact n2
  have shI : shapeAt K.idx.P 0 = shapeAt parIK 0 :=
    (counts_of_alike senders.indexMasksNotices senders.indexMasksCodes fun _ => none).2.2 0
  have shW : shapeAt K.w.P 0 = shapeAt parWK 0 :=
    (counts_of_alike senders.vectorWNotices senders.vectorWCodes fun _ => none).2.2 0
  have key := first_chain_members_sample_rows_say K
    (numbersAtFullSize challengesBeforeVectorWAtFullSize challengesOfFirstChain) k input heard hb hm
    alikeI alikeW
    (by show 0 + K.idx.P.sent.size ≤ 9; omega) (by show 9 + K.w.P.sent.size ≤ 11; omega) rfl rfl
    (rounds_in_front_of_vector_w hs scope hb).symm first start last
    (by
      show 9 + K.w.P.sent.size = _
      rw [messages_at_first_chain_end hs scope x first, sW])
    seen (by omega) (by omega)
    (by rw [sI, shI]; exact a1) (by rw [shW]; exact a2)
  rw [sI] at key
  exact key

/-- **THE END: AT A STAND.** made, ends, begins: the stand's three clauses. seen: the clause on what the stand has seen.
SPEAKS OF ANSWERS, WHICH HANG ON THE PADS. -/
theorem first_members_say_at_stand (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (K : KeyParts W₀ Rc X₀ X Wk) (senders : SendersPlansAlike K) (challengesOfFirstChain : ℕ)
    {V Pb Y : Type} (T : Thread Bk S₃ Claim V (In1 W₀ Rc) Y Pb)
    (blocks : T.bs = (descriptionFromSource Xs Nr Pl).second.blocksInOrder) {k : Coins Bk} {st : S₃}
    {m : Mid (In1 W₀ Rc) Y} {E : Env} (made : T.Made 2 k st m E) {base : List OpenedColumn}
    {e₁ : FirstState} {e₂ : St}
    (ends : ProofFile.Honest.K12.AtFile.EndsAre (descriptionFromSource Xs Nr Pl) m base e₁ e₂)
    (begins : ∀ s₀, T.begun k m.st.input (m.st.heard.take T.front) s₀ →
      (descriptionFromSource Xs Nr Pl).start₃ ((descriptionFromSource Xs Nr Pl).pub m.st.input.x) e₁ e₂ = .ok s₀)
    (seen : SendersAnswersSeen K
      (numbersAtFullSize challengesBeforeVectorWAtFullSize challengesOfFirstChain) k m.st.input
      m.st.heard m.seen) :
    SampleSays rdE st.st 0 (wordsAtKeyOwnTest K
        (numbersAtFullSize challengesBeforeVectorWAtFullSize challengesOfFirstChain) k m.st.input
        m.st.heard) ∧
      SampleSays rdE st.st 9 (wordsAtKeyOwnTest K
        (numbersAtFullSize challengesBeforeVectorWAtFullSize challengesOfFirstChain) k m.st.input
        m.st.heard) := by
  obtain ⟨-, -, -, -, s₀, cols, hbeg, -, hfold⟩ := made
  obtain ⟨r₁, r₂, rest, c₁, c₂, hseen, -, -, -, -, -, f₁, -⟩ := ends
  have last : foldBlocks T.ft ((descriptionFromSource Xs Nr Pl).second.blocksInOrder.take 2) s₀ (m.seen.drop T.front) cols =
      .ok (st, [], []) := by
    rw [← blocks]
    exact hfold
  rw [hseen] at seen
  exact first_members_say_at_folds hs scope K senders challengesOfFirstChain k m.st.input m.st.heard
    f₁ (begins s₀ hbeg) last
    ⟨answersSeen_of_longer seen.indexMasks, answersSeen_of_longer seen.vectorW⟩

end ProofFile.Honest.K12.AtKey

#print axioms ProofFile.Honest.K12.AtKey.challengesBeforeVectorWAtFullSize
#print axioms ProofFile.Honest.K12.AtKey.first_members_say_at_folds
#print axioms ProofFile.Honest.K12.AtKey.first_members_say_at_stand
