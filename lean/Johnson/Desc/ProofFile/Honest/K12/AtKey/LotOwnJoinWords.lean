-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/LotOwnJoinWords.lean: THE WORDS OF THE KEY FILE's LAST CHAIN AS THE TERM READS THEM OFF ITS
WITNESS (`wordsKey`, E2E/KeyLastWords.lean; `val₁Key`, E2E/KeyLastEvOwn.lean; `wit₃`, E2E/KeyDoorItems.lean; the first half's filling
`fillH`, E2E/FirstHFill.lean) ARE, AT THE THREE MEMBERS OF THE OWN TEST's GROUP, THE TERM `wordsAtKeyOwnTest` (LotOwnWords.lean).

  `filled_message_word`          (letters) a sending's message in the filling, `msgRun`, is the word of the sender's own rows
  `plan_number_of_index_masks`, `plan_number_of_vector_w`   the plan's numbers: message 0 of the statement is the witness's
                                 component 0; message 9 is component 2, where the ranges' test has four stages
  `first_half_at_index_masks`, `first_half_at_vector_w`   the first half's reader at numbers 0 and 9 is `msgRun` of the two senders
  `omega_tables_are_the_shared_words`, `shared_half_at_omega`   the shared thread's own witness at number 2 is Omega's two tables
                                 of the term
  `FilledWordsPremises`          what the three equations ask, all public but the length of what was heard
  `last_witness_words_are_the_term`   THE THREE EQUATIONS, at the numbers 0, 9, 11

By what. `own_coins_cut`, `words_at_index_masks`, `words_at_vector_w`, `words_at_omega_copy` (LotOwnTies.lean);
`words2_ours`, `get_witL` (Honest/K14/Thread2.lean); `toE_ofE`.

Imports. This file stands over E2E/KeyLastEvOwn.lean, in whose cone E2E/KeyOwnDense.lean declares `K12FrontD`; so does
AtFile/ClosingStand.lean. The two cannot be imported together.

Limits.
- WORDS AGAINST WORDS: two terms are one on three messages. Nothing on what a verifier sees, on a stand, or on any run.
- K, f, Q, x and the shared thread's letters are letters.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.LotOwnAlike
import Johnson.Desc.ProofFile.Honest.K14.Thread2
import E2E.KeySharedThread
import E2E.KeyLastEvOwn
import E2E.KeyLastWords
import E2E.KeyDoorItems
import E2E.FirstHFill

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace ProofFile.Honest.K12.AtKey
open OnBytes (TableKey)
open OnBytes.Means (Words)
open OnBytes.Slice (GE readE)
open Johnson.Prover.Send (shapeAt)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Key (Source LaterPlaces Xi descriptionFromSource valOf)
open Johnson.RunOne.KeyRows1 (plan₁)
open _root_.Desc.K14 (St)
open AtPublicFiles.KeyFile (KeyParts In1 randK14)
open AtPublicFiles.KeyTest (sIdx sW)
open AtPublicFiles.KeyThread (one₀)
open AtPublicFiles.KeySharedThread (threadKey parKey)
open AtPublicFiles.KeyDoorItems (wit₃ commonOf)
open AtPublicFiles.KeyLastChain (wordsKey val₁Key)
open AtPublicFiles.FirstH (fillH msgRun readH LaterFill)
open ProofFile.Honest.K1 (SendJob lentCut rowsLaid dueR)
open ProofFile.Honest.K14 (WitLens witL witAll get_witL holds2 words2_ours)
open ProofFile.Honest.K12.Light (sentOf)

/-- **A sending's message in the filling is the word of the sender's own rows**, where the book's row at the sender's address
is the sender's count, in the first chain's table alone. -/
theorem filled_message_word {Bk : ProverCoinCounts} {W X : Type} (J : SendJob W X) (own₀ : X) (k : Coins Bk)
    (w : W) (heard : List Fmt.Drawn) (challengesInFront : ℕ) (a : Addr)
    (ha : a = ⟨J.P.place, 0⟩) (hd : dueAt Bk.first a = dueR J.P J.ride)
    (h₂ : noRowIn Bk.shared a) (h₃ : noRowIn Bk.second a) (hsent : 0 < J.P.sent.size)
    (part : OnBytes.Part) (i : ℕ) :
    msgRun J own₀ k w (heard.take challengesInFront) part i =
      (rowsOfSending k a J w own₀ heard challengesInFront 0).word (shapeAt J.P 0) part i := by
  subst ha
  have hc : lentCut k 0 ⟨J.P.place, 0⟩ (dueR J.P J.ride) =
      some (ownCoinsOfSending k ⟨J.P.place, 0⟩ J) := own_coins_cut k _ J hd h₂ h₃
  unfold msgRun
  rw [hc]
  show (if J.first ≤ J.first ∧ J.first < J.first + J.P.sent.size then
      (rowsLaid J own₀ (ownCoinsOfSending k ⟨J.P.place, 0⟩ J) w (heard.take challengesInFront)
        (J.first - J.first)).word (shapeAt J.P (J.first - J.first)) part i
    else 0) = _
  rw [if_pos ⟨Nat.le_refl _, by omega⟩, Nat.sub_self]
  rfl

/-- The statement's message 0 is the witness's component 0. -/
theorem plan_number_of_index_masks (Xs : Source) : (plan₁ (one₀ Xs)).num 0 = some 0 := rfl

/-- The statement's message 9 is the witness's component 2, where the ranges' test has four stages. -/
theorem plan_number_of_vector_w (Xs : Source) (h : (one₀ Xs).ranges.stages.length = 4) :
    (plan₁ (one₀ Xs)).num 9 = some 2 := by
  show (if (9 == 0) = true then some 0 else if (9 == 1) = true then some 1
    else if (9 == 1 + 2 * (one₀ Xs).ranges.stages.length) = true then some 2 else none) = some 2
  rw [h]
  rfl

section Filling
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk : Type} (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces)
  (K : KeyParts W₀ Rc X₀ X Wk) (f : W₀ → Weights) (Q : LaterFill Bk W₀ Rc) (x : Xi)

/-- **The first half's reader at number 0.** -/
theorem first_half_at_index_masks (k : Coins Bk) (w₀ : W₀) (rc : Rc) (hA : List Fmt.Drawn)
    (part : OnBytes.Part) (i : ℕ) :
    val₁Key Xs (fillH Xs Nr Pl K f Q x) ((fillH Xs Nr Pl K f Q x).wit k w₀ rc hA []) 0 part i =
      msgRun K.idx K.own₀ k (⟨w₀, rc, x, ()⟩ : In1 W₀ Rc)
        (hA.take (roundsTo (descriptionFromSource Xs Nr Pl).first.blocksInOrder 0)) part i := by
  show readE (valOf (plan₁ (one₀ Xs)) readH ((fillH Xs Nr Pl K f Q x).wit k w₀ rc hA []) 0 part i) = _
  unfold valOf
  rw [plan_number_of_index_masks]
  exact OnBytes.Slice.toE_ofE _

/-- **The first half's reader at number 9.** -/
theorem first_half_at_vector_w (h : (one₀ Xs).ranges.stages.length = 4) (k : Coins Bk) (w₀ : W₀)
    (rc : Rc) (hA : List Fmt.Drawn) (part : OnBytes.Part) (i : ℕ) :
    val₁Key Xs (fillH Xs Nr Pl K f Q x) ((fillH Xs Nr Pl K f Q x).wit k w₀ rc hA []) 9 part i =
      msgRun K.w K.own₀ k (⟨w₀, rc, x, ()⟩ : In1 W₀ Rc)
        (hA.take (roundsTo (descriptionFromSource Xs Nr Pl).first.blocksInOrder 17)) part i := by
  show readE (valOf (plan₁ (one₀ Xs)) readH ((fillH Xs Nr Pl K f Q x).wit k w₀ rc hA []) 9 part i) = _
  unfold valOf
  rw [plan_number_of_vector_w Xs h]
  exact OnBytes.Slice.toE_ofE _

end Filling

section Shared
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk P₂ Wt₂ : Type} (Xs : Source) (Nr : H2U.PlaceNums)
  (Pl : LaterPlaces) (K : KeyParts W₀ Rc X₀ X Wk) (ℓ₂ : WitLens Wt₂) (Nm : NumbersS)
  (Mg₂ : Common W₀ Rc TableKey → MeaningS St P₂ Wt₂)
  (tb₂ : Fmt.TreeSource → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest₂ : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt₂)
  (Kp₂ : ℕ → St → St → Prop) (Vd₂ : Common W₀ Rc TableKey → Prop) (w₂ : Common W₀ Rc TableKey)

/-- Omega's two tables in the term are the shared chain's honest words at number 2. -/
theorem omega_tables_are_the_shared_words (N : OwnTestNumbers) (k : Coins Bk) (input : In1 W₀ Rc)
    (h₁ h₂ : List Fmt.Drawn) (hl : h₁.length = N.challengesOfFirstChain)
    (hsize : 0 < (_root_.Desc.K14.withOmega K.send.P.S).size)
    (restWords : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Words GE)
    (part : OnBytes.Part) (i : ℕ) :
    wordsOfOmegaAtKey K N k input (h₁ ++ h₂) part i =
      witAll K.send.P (sentOf K.send.P.S)
        (holds2 K.send.P K.weights fun c => randK14 (K.rand c)) restWords k (commonOfInput input) h₂
        2 part i := by
  unfold wordsOfOmegaAtKey witAll
  rw [← hl, List.drop_left]
  exact (words2_ours K.send.P (sentOf K.send.P.S) input.x.key _ _ _ 2
    (Or.inr ⟨Nat.le_refl 2, by omega⟩) part i).symm

/-- **The shared thread's own witness at number 2 is Omega's two tables of the term.** -/
theorem shared_half_at_omega (N : OwnTestNumbers) (k : Coins Bk) (input : In1 W₀ Rc)
    (heard : List Fmt.Drawn) (hlong : N.challengesOfFirstChain ≤ heard.length)
    (sharedPlan : K.send.P = parKey Xs Pl)
    (sendsOmega : 0 < (_root_.Desc.K14.withOmega K.send.P.S).size) (part : OnBytes.Part) (i : ℕ) :
    ℓ₂.get ((threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂).wit k (commonOf input)
        (heard.drop N.challengesOfFirstChain)) 2 part i =
      wordsOfOmegaAtKey K N k input heard part i := by
  have hl : (heard.take N.challengesOfFirstChain).length = N.challengesOfFirstChain := by
    rw [List.length_take]
    omega
  have e := omega_tables_are_the_shared_words K N k input (heard.take N.challengesOfFirstChain)
    (heard.drop N.challengesOfFirstChain) hl sendsOmega (fun k w h => ℓ₂.get (rest₂ k w h)) part i
  rw [List.take_append_drop] at e
  rw [e, sharedPlan]
  show ℓ₂.get (witL ℓ₂ (parKey Xs Pl) (AtPublicFiles.KeySharedThread.sentKey Xs Pl)
      (holds2 (parKey Xs Pl) K.weights fun c => randK14 (K.rand c)) rest₂ k (commonOf input)
      (heard.drop N.challengesOfFirstChain)) 2 part i = _
  rw [get_witL]
  rfl

end Shared

section Joined
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk P₂ Wt₂ : Type} (Xs : Source) (Nr : H2U.PlaceNums)
  (Pl : LaterPlaces) (K : KeyParts W₀ Rc X₀ X Wk) (f : W₀ → Weights) (Q : LaterFill Bk W₀ Rc)
  (x : Xi) (ℓ₂ : WitLens Wt₂) (Nm : NumbersS)
  (Mg₂ : Common W₀ Rc TableKey → MeaningS St P₂ Wt₂)
  (tb₂ : Fmt.TreeSource → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest₂ : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt₂)
  (Kp₂ : ℕ → St → St → Prop) (Vd₂ : Common W₀ Rc TableKey → Prop) (w₂ : Common W₀ Rc TableKey)

/-- **What the three equations ask.** before, first: the challenges in front of W's sending, and the first chain's. -/
structure FilledWordsPremises (place : Place) (before first : ℕ) : Prop where
  book : BookAtOwnTest Bk K place
  placeIndexMasks : K.idx.P.place = ⟨1, none, 1, .K1⟩
  placeVectorW : K.w.P.place = ⟨1, none, 14, .K1⟩
  indexMasksSends : K.idx.P.sent.size = 1
  vectorWSends : K.w.P.sent.size = 2
  stages : (one₀ Xs).ranges.stages.length = 4
  roundsBefore : roundsTo (descriptionFromSource Xs Nr Pl).first.blocksInOrder 17 = before
  roundsFirst : ((descriptionFromSource Xs Nr Pl).first.blocksInOrder.flatMap (·.rounds)).length = first
  beforeFirst : before ≤ first
  sharedPlan : K.send.P = parKey Xs Pl
  sendsOmega : 0 < (_root_.Desc.K14.withOmega K.send.P.S).size

/-- **AT THE THREE MEMBERS THE LAST WITNESS's WORDS ARE THE TERM.** st: a state of the last chain at which Omega's copy has the
number 11. The input is the filling's own instance. -/
theorem last_witness_words_are_the_term {place : Place} {before first : ℕ}
    (H : FilledWordsPremises (Bk := Bk) Xs Nr Pl K place before first) (st : S₃)
    (homega : st.loc.omega = 11) (k : Coins Bk) (w₀ : W₀) (rc : Rc) (heard : List Fmt.Drawn)
    (hlong : first ≤ heard.length) (o : ℕ) (ho : o ∈ [0, 9, 11]) (part : OnBytes.Part) (i : ℕ) :
    wordsKey (val₁Key Xs (fillH Xs Nr Pl K f Q x)) st
        (wit₃ Xs Nr Pl K (fillH Xs Nr Pl K f Q x) ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ k
          (⟨w₀, rc, x, ()⟩ : In1 W₀ Rc) heard) o part i =
      wordsAtKeyOwnTest K (numbersAtFullSize before first) k (⟨w₀, rc, x, ()⟩ : In1 W₀ Rc) heard o part
        i := by
  have a0 : sIdx = ⟨K.idx.P.place, 0⟩ := by rw [H.placeIndexMasks]; rfl
  have a9 : sW = ⟨K.w.P.place, 0⟩ := by rw [H.placeVectorW]; rfl
  have b1 : (numbersAtFullSize before first).indexMasksFirst + K.idx.P.sent.size ≤
      (numbersAtFullSize before first).vectorWFirst := by
    rw [H.indexMasksSends]
    show 0 + 1 ≤ 9
    decide
  have b2 : (numbersAtFullSize before first).vectorWFirst + K.w.P.sent.size ≤
      (numbersAtFullSize before first).omegaCopy := by
    rw [H.vectorWSends]
    show 9 + 2 ≤ 11
    decide
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  unfold wordsKey
  rcases ho with rfl | rfl | rfl
  · rw [if_neg (by rw [homega]; decide)]
    show val₁Key Xs (fillH Xs Nr Pl K f Q x) ((fillH Xs Nr Pl K f Q x).wit k w₀ rc
      (heard.take ((descriptionFromSource Xs Nr Pl).first.blocksInOrder.flatMap (·.rounds)).length) []) 0 part i = _
    rw [first_half_at_index_masks]
    have z : roundsTo (descriptionFromSource Xs Nr Pl).first.blocksInOrder 0 = 0 := rfl
    have t : (heard.take ((descriptionFromSource Xs Nr Pl).first.blocksInOrder.flatMap (·.rounds)).length).take 0 =
        heard.take 0 := by rw [List.take_zero, List.take_zero]
    rw [z, t, filled_message_word K.idx K.own₀ k _ heard 0 sIdx a0 H.book.rowIndexMasks
      H.book.indexMasksNotShared H.book.indexMasksNotLast (by rw [H.indexMasksSends]; decide)]
    exact (words_at_index_masks K (numbersAtFullSize before first) k _ heard part i b1 b2 0
      (by rw [H.indexMasksSends]; decide)).symm
  · rw [if_neg (by rw [homega]; decide)]
    show val₁Key Xs (fillH Xs Nr Pl K f Q x) ((fillH Xs Nr Pl K f Q x).wit k w₀ rc
      (heard.take ((descriptionFromSource Xs Nr Pl).first.blocksInOrder.flatMap (·.rounds)).length) []) 9 part i = _
    rw [first_half_at_vector_w Xs Nr Pl K f Q x H.stages, H.roundsBefore, H.roundsFirst,
      List.take_take, Nat.min_eq_left H.beforeFirst,
      filled_message_word K.w K.own₀ k _ heard before sW a9 H.book.rowVectorW
        H.book.vectorWNotShared H.book.vectorWNotLast (by rw [H.vectorWSends]; decide)]
    exact (words_at_vector_w K (numbersAtFullSize before first) k _ heard part i b2 0
      (by rw [H.vectorWSends]; decide)).symm
  · rw [if_pos homega.symm]
    show ℓ₂.get ((threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂).wit k
      (commonOf (⟨w₀, rc, x, ()⟩ : In1 W₀ Rc))
      (heard.drop ((descriptionFromSource Xs Nr Pl).first.blocksInOrder.flatMap (·.rounds)).length)) 2 part i = _
    rw [H.roundsFirst]
    exact (shared_half_at_omega Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂
      (numbersAtFullSize before first) k _ heard hlong H.sharedPlan H.sendsOmega part i).trans
      (words_at_omega_copy K (numbersAtFullSize before first) k _ heard part i).symm

end Joined

end ProofFile.Honest.K12.AtKey

end

#print axioms ProofFile.Honest.K12.AtKey.filled_message_word
#print axioms ProofFile.Honest.K12.AtKey.plan_number_of_index_masks
#print axioms ProofFile.Honest.K12.AtKey.plan_number_of_vector_w
#print axioms ProofFile.Honest.K12.AtKey.first_half_at_index_masks
#print axioms ProofFile.Honest.K12.AtKey.first_half_at_vector_w
#print axioms ProofFile.Honest.K12.AtKey.omega_tables_are_the_shared_words
#print axioms ProofFile.Honest.K12.AtKey.shared_half_at_omega
#print axioms ProofFile.Honest.K12.AtKey.FilledWordsPremises
#print axioms ProofFile.Honest.K12.AtKey.last_witness_words_are_the_term
