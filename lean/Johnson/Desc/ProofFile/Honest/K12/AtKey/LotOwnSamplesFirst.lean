-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/LotOwnSamplesFirst.lean: AT THE KEY FILE's OWN TEST, THE SAMPLE ROWS OF THE TWO
MEMBERS THAT THE FIRST CHAIN SENT (the index masks' message; W's message 0) SAY THEIR CLAIMS OF THE TERM
`wordsAtKeyOwnTest` (LotOwnWords.lean): two thirds of the premise hS of `says_at_stand` (OwnSays.lean), from the
verifier's own folds and ONE CLAUSE ON THE ROUNDS SEEN. No thread, no witness and no item's meaning is read.

  `AnswersSeen`                  THE CLAUSE, for one sending: the round behind the seeds' round holds the term that the
                                 sender's second move says
  `SendersAnswersSeen`           the clause at the two sendings, at the rows of which the term is made
  `answersSeen_of_longer`        the clause on a longer list of rounds gives it on the list's front
  `sampleSays_at_later`          a sampled message's rows that say their claims say them at a later statement, of any
                                 words that agree on that message
  `term_at_index_masks`, `term_at_vector_w`   the term at a message of a sending is the held words there
  `index_masks_sample_rows_say`, `vector_w_sample_rows_say`   THE TWO STATEMENTS
  `first_chain_members_sample_rows_say`   both, at the own group's two members

The road. The state in front of the own test is made by three folds of the verifier's: the first chain's, the last
chain's start, the last chain's first two blocks. The first fold is cut at the sending (`after_sending_says`,
LotOwnSamplesFirstLaw.lean); from there the sampled message stays (`SmpStay`) to the stand.

What stays a premise.
- `SendersAnswersSeen`. WHOSE: the frame's play | the second family of the threads (`Said`, Honest/Thread/Said.lean): a
  sentence on the rounds seen, which once true stays true, as `SaidOk` (Honest/Thread/SaidOk.lean). Its form at one step
  is in the library: the fifth clause of `step_at_block` (Honest/K1/Law/ExchangeAtPins.lean), at the rows `rowsLaid`,
  under `K1Seated` at the first chain's thread. IT CAN SAY NO: where the rows that the sender laid are not
  `rowsOfSending` (another cut of the purse; data that reads more of the front).
- `PlansAlike`: the prover's plan and the verifier's have the same notices and codes. Public.
- The numbers: where the two sendings stand; how many rounds stand in front of W's. Public.
  ONE NUMBER IN TWO SENSES: `N.challengesBefore…` counts CHALLENGES in `frontBeforeSending` (heard.take) and ROUNDS in
  `AnswersSeen` (seen[·]?). They are one number at a thread's stand: `Made` has m.seen.map (·.drawn) = m.st.heard
  (Honest/Thread/Thr.lean): each round seen bears one challenge.
- The sampled messages have answers (ha). Public.

Limits.
- SPEAKS OF ANSWERS, WHICH HANG ON THE PADS.
- The three folds are premises: that a run reaches such a state is not said here.
- Of Omega's copy, of the open rows and of `WordsTied` nothing is said here.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.LotOwnSamplesFirstLaw
import Johnson.Desc.ProofFile.Honest.K12.AtKey.LotOwnWords
import Johnson.RunOne.KeySmpStay
import E2E.KeyThreads
import E2E.KeyKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace ProofFile.Honest.K12.AtKey
open OnBytes (Statement Oracle OracleNotice)
open OnBytes.Slice (GE rdE)
open OnBytes.Means (Words Says AllSay SampleSays)
open VerifiableInference.Desc (Block OpenedColumn foldBlocks)
open VerifiableInference.Desc.K1 (Par seedsOf SmpStay)
open VerifiableInference.Desc.Key (Source LaterPlaces Claim FirstState descriptionFromSource sendW pieces rootsBefore batchRound)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Ground (By)
open VerifiableInference.Desc.First.Close (NamesOne)
open Johnson.Prover.Send (shapeAt answers held_old held_new)
open Johnson.RunOne.KeyKeeps (st₁ st₃)
open Johnson.RunOne.KeyWalk (flat_smp₁ flat_smp₃)
open Johnson.RunOne.KeySmp (start₃_same)
open Johnson.RunOne.KeyMsg (idx_named w_named bW)
open Johnson.RunOne.KeySendGood (parIdx parW gW idx_at w_at rounds_idx rounds_w)
open ProofFile.Honest.K1 (stAt)
open AtPublicFiles.KeyFile (KeyParts In1)
open AtPublicFiles.KeyTest (sIdx sW)
open _root_.Desc.K14 (St)

/-! ## 1 The clause -/

/-- **THE CLAUSE, FOR ONE SENDING.** seen: rounds, in the order of the play. roundOfSeeds: the number among them of the
sending's first round. The round behind it holds the term that the second move of `sendPart J` (Honest/K1/Part.lean)
says, at the rows V, at the seeds cut off the first round. WHOSE: this file's head. -/
def AnswersSeen {Wd X : Type} (J : K1.SendJob Wd X) (V : ℕ → Johnson.Prover.Send.Rows) (seen : List Fmt.RoundView)
    (roundOfSeeds : ℕ) : Prop :=
  ∀ ρ₁ ρ₂ : Fmt.RoundView, seen[roundOfSeeds]? = some ρ₁ → seen[roundOfSeeds + 1]? = some ρ₂ →
    ρ₂.vals = (answers J.P (stAt J.P J.first) J.first (Johnson.Prover.Send.held (fun _ _ _ => 0) J.first J.P V)
      (seedsOf J.P ρ₁)).map .answer

/-- The clause on a longer list of rounds gives it on the list's front. -/
theorem answersSeen_of_longer {Wd X : Type} {J : K1.SendJob Wd X} {V : ℕ → Johnson.Prover.Send.Rows}
    {front rest : List Fmt.RoundView} {n : ℕ} (h : AnswersSeen J V (front ++ rest) n) :
    AnswersSeen J V front n := by
  have up : ∀ (i : ℕ) (ρ : Fmt.RoundView), front[i]? = some ρ → (front ++ rest)[i]? = some ρ := by
    intro i ρ hi
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hi).1]
    exact hi
  exact fun ρ₁ ρ₂ g₁ g₂ => h ρ₁ ρ₂ (up _ _ g₁) (up _ _ g₂)

variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk : Type}

/-- **THE CLAUSE AT THE TWO SENDINGS**, at the rows of which `wordsAtKeyOwnTest` is made. The seeds' round of a sending
has the number of the challenges in front of the sending. -/
structure SendersAnswersSeen (K : KeyParts W₀ Rc X₀ X Wk) (N : OwnTestNumbers) (k : Coins Bk)
    (input : In1 W₀ Rc) (heard : List Fmt.Drawn) (seen : List Fmt.RoundView) : Prop where
  indexMasks : AnswersSeen K.idx
    (rowsOfSending k sIdx K.idx input K.own₀ heard N.challengesBeforeIndexMasks) seen
    N.challengesBeforeIndexMasks
  vectorW : AnswersSeen K.w
    (rowsOfSending k sW K.w input K.own₀ heard N.challengesBeforeVectorW) seen
    N.challengesBeforeVectorW

/-! ## 2 To a later statement; the term at a sending's message -/

/-- **A sampled message's rows that say their claims say them at a later statement**, of any words that agree on that
message. -/
theorem sampleSays_at_later {A B : Statement} (h : SmpStay A B) {o : ℕ} {x : Oracle}
    (hx : A.oracles[o]? = some x) (hs : x.sampled = true)
    (hN : ∀ q ∈ x.sampleRows.toList, NamesOne q o) (m m' : Words GE)
    (hm : ∀ part i, m' o part i = m o part i) (hA : AllSay rdE A x.sampleRows.toList m) :
    SampleSays rdE B o m' := by
  intro x' hx' r hr
  obtain ⟨y, hy, -, -, hyr⟩ := h.2 o x hx hs
  obtain rfl := Option.some.inj (hx'.symm.trans hy)
  rw [hyr] at hr
  exact (says_of_words B r (hN r hr) m m' hm).2 ((says_of_stay h hx hs r (hN r hr) m).2 (hA r hr))

section Term
variable (K : KeyParts W₀ Rc X₀ X Wk) (N : OwnTestNumbers) (k : Coins Bk) (input : In1 W₀ Rc)
  (heard : List Fmt.Drawn)

/-- The term at a message of the index masks' sending is the held words there, whatever lies beneath. -/
theorem term_at_index_masks (h₁ : N.indexMasksFirst + K.idx.P.sent.size ≤ N.vectorWFirst)
    (h₂ : N.vectorWFirst + K.w.P.sent.size ≤ N.omegaCopy) (j : ℕ) (hj : j < K.idx.P.sent.size)
    (w : Words GE) (part : OnBytes.Part) (i : ℕ) :
    wordsAtKeyOwnTest K N k input heard (N.indexMasksFirst + j) part i =
      Johnson.Prover.Send.held w N.indexMasksFirst K.idx.P
        (rowsOfSending k sIdx K.idx input K.own₀ heard N.challengesBeforeIndexMasks)
        (N.indexMasksFirst + j) part i := by
  unfold wordsAtKeyOwnTest
  rw [if_neg (by omega), held_old _ _ _ _ _ _ _ (by omega), held_new _ _ _ _ j hj,
    held_new _ _ _ _ j hj]

/-- The term at a message of W's sending is the held words there, whatever lies beneath. -/
theorem term_at_vector_w (h₂ : N.vectorWFirst + K.w.P.sent.size ≤ N.omegaCopy) (j : ℕ)
    (hj : j < K.w.P.sent.size) (w : Words GE) (part : OnBytes.Part) (i : ℕ) :
    wordsAtKeyOwnTest K N k input heard (N.vectorWFirst + j) part i =
      Johnson.Prover.Send.held w N.vectorWFirst K.w.P
        (rowsOfSending k sW K.w input K.own₀ heard N.challengesBeforeVectorW)
        (N.vectorWFirst + j) part i := by
  unfold wordsAtKeyOwnTest
  rw [if_neg (by omega), held_new _ _ _ _ j hj, held_new _ _ _ _ j hj]

end Term

/-- The two plans give a message one shape. -/
theorem shapeAt_of_alike {P Q : Par} (h : PlansAlike P Q) (j : ℕ) : shapeAt P j = shapeAt Q j := by
  unfold shapeAt
  rw [h.sent]

/-! ## 3 The two statements -/

section Stand
variable {Xs : Source} {Nr : H2U.PlaceNums} {Pl : LaterPlaces}
  (K : KeyParts W₀ Rc X₀ X Wk) (N : OwnTestNumbers) (k : Coins Bk) (input : In1 W₀ Rc)
  (heard : List Fmt.Drawn)

/-- From the first chain's end to the stand in front of the own test a sampled message stays. -/
theorem stays_to_own_test {x : (descriptionFromSource Xs Nr Pl).XiPub} {e₁ : FirstState} {e₂ : St} {s₀ st : S₃}
    {ft : ℕ} {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    (start : (descriptionFromSource Xs Nr Pl).start₃ x e₁ e₂ = .ok s₀)
    (last : foldBlocks ft ((descriptionFromSource Xs Nr Pl).second.blocksInOrder.take 2) s₀ rs cols = .ok (st, [], [])) :
    SmpStay (st₁ e₁) st.st := by
  have hsame : s₀.st = st₁ (show FirstState from e₁) := start₃_same start
  have hstay : SmpStay s₀.st st.st :=
    VerifiableInference.Desc.Keeps.foldBlocks_keeps (By SmpStay st₃) (fun _ => SmpStay.refl _)
      (fun _ _ _ p q => p.trans q) ft _ (fun b hb => flat_smp₃ b (List.mem_of_mem_take hb)) s₀ rs cols _
      last
  rw [hsame] at hstay
  exact hstay

/-- **THE INDEX MASKS' SENDING.** first, start, last: the verifier's three folds to the stand in front of the own test.
SPEAKS OF ANSWERS, WHICH HANG ON THE PADS. -/
theorem index_masks_sample_rows_say (alike : PlansAlike K.idx.P (parIdx Xs))
    (h₁ : N.indexMasksFirst + K.idx.P.sent.size ≤ N.vectorWFirst)
    (h₂ : N.vectorWFirst + K.w.P.sent.size ≤ N.omegaCopy) (hfirst : N.indexMasksFirst = 0)
    (hround : N.challengesBeforeIndexMasks = 0)
    {x : (descriptionFromSource Xs Nr Pl).XiPub} {e₁ : FirstState} {e₂ : St} {s₀ st : S₃} {ft : ℕ}
    {r₁ rs : List Fmt.RoundView} {c₁ cols : List OpenedColumn}
    (first : foldBlocks 0 (descriptionFromSource Xs Nr Pl).first.blocksInOrder ((descriptionFromSource Xs Nr Pl).start₁ x) r₁ c₁ = .ok (e₁, [], []))
    (start : (descriptionFromSource Xs Nr Pl).start₃ x e₁ e₂ = .ok s₀)
    (last : foldBlocks ft ((descriptionFromSource Xs Nr Pl).second.blocksInOrder.take 2) s₀ rs cols = .ok (st, [], []))
    (seen : AnswersSeen K.idx
      (rowsOfSending k sIdx K.idx input K.own₀ heard N.challengesBeforeIndexMasks) r₁
      N.challengesBeforeIndexMasks)
    (j : ℕ) (hj : j < K.idx.P.sent.size) (ha : (shapeAt K.idx.P j).answers ≠ 0) :
    SampleSays rdE st.st (N.indexMasksFirst + j) (wordsAtKeyOwnTest K N k input heard) := by
  have hj' : j < (parIdx Xs).sent.size := by
    rw [← alike.sent]
    exact hj
  have ha' : (shapeAt (parIdx Xs) j).answers ≠ 0 := by
    rw [← shapeAt_of_alike alike]
    exact ha
  rw [hround] at seen
  obtain ⟨a, s', r₀, r', c₀, c', g₁, -, -, z, hz, hzs, hzn, hzsay⟩ :=
    after_sending_says (descriptionFromSource Xs Nr Pl).first.blocksInOrder (parIdx Xs) _ 0 (idx_at Xs Nr Pl) (rounds_idx Xs)
      (idx_named _ _ _) (fun b hb => flat_smp₁ b (List.mem_of_mem_drop hb)) 0 first
      (rowsOfSending k sIdx K.idx input K.own₀ heard 0) K.idx.first 0
      (by rw [List.take_zero]; rfl)
      (fun ρ₁ ρ₂ q₁ q₂ => by
        rw [← answers_of_alike alike]
        exact seen ρ₁ ρ₂ q₁ q₂) j hj' ha'
  have ea : a = (descriptionFromSource Xs Nr Pl).start₁ x := by
    rw [List.take_zero] at g₁
    unfold foldBlocks at g₁
    exact congrArg Prod.fst (Except.ok.inj g₁).symm
  have hs0 : (st₁ a).oracles.size = N.indexMasksFirst := by
    rw [ea, hfirst]
    rfl
  rw [hs0] at hz hzn hzsay
  refine sampleSays_at_later (stays_to_own_test start last) hz hzs hzn _ _ (fun part i => ?_)
    (hzsay fun _ _ _ => 0)
  rw [term_at_index_masks K N k input heard h₁ h₂ j hj (fun _ _ _ => 0), held_of_alike alike, hround]

/-- **W's SENDING.** hcount: W's sending is the last of the first chain: behind its messages the statement ends.
SPEAKS OF ANSWERS, WHICH HANG ON THE PADS. -/
theorem vector_w_sample_rows_say {bw : Block FirstState Claim} {msg : Array OracleNotice}
    (hb : sendW Xs.Y.k.oneTime pieces (rootsBefore Xs.Y.D.1 (batchRound Xs.Y.D.1)) (gW Xs) = some bw)
    (hm : OnBytes.linMessageW Xs.Y.k.oneTime.lin = some msg)
    (alike : PlansAlike K.w.P (parW Xs msg))
    (h₂ : N.vectorWFirst + K.w.P.sent.size ≤ N.omegaCopy)
    (hround : N.challengesBeforeVectorW =
      (((descriptionFromSource Xs Nr Pl).first.blocksInOrder.take (bW Xs Nr Pl)).flatMap (·.rounds)).length)
    {x : (descriptionFromSource Xs Nr Pl).XiPub} {e₁ : FirstState} {e₂ : St} {s₀ st : S₃} {ft : ℕ}
    {r₁ rs : List Fmt.RoundView} {c₁ cols : List OpenedColumn}
    (first : foldBlocks 0 (descriptionFromSource Xs Nr Pl).first.blocksInOrder ((descriptionFromSource Xs Nr Pl).start₁ x) r₁ c₁ = .ok (e₁, [], []))
    (start : (descriptionFromSource Xs Nr Pl).start₃ x e₁ e₂ = .ok s₀)
    (last : foldBlocks ft ((descriptionFromSource Xs Nr Pl).second.blocksInOrder.take 2) s₀ rs cols = .ok (st, [], []))
    (hcount : N.vectorWFirst + K.w.P.sent.size = (st₁ e₁).oracles.size)
    (seen : AnswersSeen K.w
      (rowsOfSending k sW K.w input K.own₀ heard N.challengesBeforeVectorW) r₁
      N.challengesBeforeVectorW)
    (j : ℕ) (hj : j < K.w.P.sent.size) (ha : (shapeAt K.w.P j).answers ≠ 0) :
    SampleSays rdE st.st (N.vectorWFirst + j) (wordsAtKeyOwnTest K N k input heard) := by
  have hj' : j < (parW Xs msg).sent.size := by
    rw [← alike.sent]
    exact hj
  have ha' : (shapeAt (parW Xs msg) j).answers ≠ 0 := by
    rw [← shapeAt_of_alike alike]
    exact ha
  obtain ⟨a, s', r₀, r', c₀, c', -, g₂, hs', z, hz, hzs, hzn, hzsay⟩ :=
    after_sending_says (descriptionFromSource Xs Nr Pl).first.blocksInOrder (parW Xs msg) _ (bW Xs Nr Pl) (w_at Xs Nr Pl hb)
      (rounds_w hm hb) (w_named hm hb) (fun b hb' => flat_smp₁ b (List.mem_of_mem_drop hb')) 0 first
      (rowsOfSending k sW K.w input K.own₀ heard N.challengesBeforeVectorW) K.w.first
      N.challengesBeforeVectorW hround
      (fun ρ₁ ρ₂ q₁ q₂ => by
        rw [← answers_of_alike alike]
        exact seen ρ₁ ρ₂ q₁ q₂) j hj' ha'
  -- behind W's sending stands the seal alone, which hands the state on
  obtain ⟨blk, hl, -, -, -, hd⟩ := AtPublicFiles.AtFiles.flat_last (descriptionFromSource Xs Nr Pl).first
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
  have hdrop : (descriptionFromSource Xs Nr Pl).first.blocksInOrder.drop (bW Xs Nr Pl + 1) = [blk] := by
    have hl' : (descriptionFromSource Xs Nr Pl).first.blocksInOrder[bW Xs Nr Pl + 1]? = some blk := by
      have e₁' : (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length - 1 = bW Xs Nr Pl + 1 := by omega
      rw [← e₁']
      exact hl
    obtain ⟨hm', ev⟩ := List.getElem?_eq_some_iff.1 hl'
    rw [List.drop_eq_getElem_cons hm', ev, List.drop_of_length_le (by omega)]
  have g₃ : foldBlocks 0 ((descriptionFromSource Xs Nr Pl).first.blocksInOrder.drop (bW Xs Nr Pl + 1)) s' r' c' =
      .ok (e₁, [], []) := g₂
  rw [hdrop] at g₃
  obtain ⟨-, s'', n, hstep, hend⟩ := VerifiableInference.Desc.foldBlocks_cons_ok.1 g₃
  have es'' : s'' = e₁ := by
    unfold foldBlocks at hend
    exact congrArg Prod.fst (Except.ok.inj hend)
  obtain ⟨gs, hdc⟩ := _root_.Desc.K14.Law.step_decides 0 blk s' s'' _ _ n hstep
  rw [hd] at hdc
  have e₂' : s'' = s' := AtPublicFiles.KeyThread.end_same (S := FirstState)
    (fun t => [("end: no count of rows is owed", t.noneWaits)] ++
      VerifiableInference.Desc.Key.untestedButOwn t) s' s'' hdc
  have hsz : K.w.P.sent.size = (parW Xs msg).sent.size := by rw [alike.sent]
  have hs0 : (st₁ a).oracles.size = N.vectorWFirst := by
    rw [← es'', e₂', hs'] at hcount
    omega
  rw [hs0] at hz hzn hzsay
  refine sampleSays_at_later (stays_to_own_test start last) hz hzs hzn _ _ (fun part i => ?_)
    (hzsay fun _ _ _ => 0)
  rw [term_at_vector_w K N k input heard h₂ j hj (fun _ _ _ => 0), held_of_alike alike]

/-- **BOTH, AT THE OWN GROUP's TWO MEMBERS OF THE FIRST CHAIN**: the last message of the index masks' sending; message
0 of W's. seen: the clause on the first chain's rounds. SPEAKS OF ANSWERS, WHICH HANG ON THE PADS. -/
theorem first_chain_members_sample_rows_say {bw : Block FirstState Claim} {msg : Array OracleNotice}
    (hb : sendW Xs.Y.k.oneTime pieces (rootsBefore Xs.Y.D.1 (batchRound Xs.Y.D.1)) (gW Xs) = some bw)
    (hm : OnBytes.linMessageW Xs.Y.k.oneTime.lin = some msg)
    (alikeIndexMasks : PlansAlike K.idx.P (parIdx Xs)) (alikeVectorW : PlansAlike K.w.P (parW Xs msg))
    (h₁ : N.indexMasksFirst + K.idx.P.sent.size ≤ N.vectorWFirst)
    (h₂ : N.vectorWFirst + K.w.P.sent.size ≤ N.omegaCopy) (hfirst : N.indexMasksFirst = 0)
    (hroundIndexMasks : N.challengesBeforeIndexMasks = 0)
    (hroundVectorW : N.challengesBeforeVectorW =
      (((descriptionFromSource Xs Nr Pl).first.blocksInOrder.take (bW Xs Nr Pl)).flatMap (·.rounds)).length)
    {x : (descriptionFromSource Xs Nr Pl).XiPub} {e₁ : FirstState} {e₂ : St} {s₀ st : S₃} {ft : ℕ}
    {r₁ rs : List Fmt.RoundView} {c₁ cols : List OpenedColumn}
    (first : foldBlocks 0 (descriptionFromSource Xs Nr Pl).first.blocksInOrder ((descriptionFromSource Xs Nr Pl).start₁ x) r₁ c₁ = .ok (e₁, [], []))
    (start : (descriptionFromSource Xs Nr Pl).start₃ x e₁ e₂ = .ok s₀)
    (last : foldBlocks ft ((descriptionFromSource Xs Nr Pl).second.blocksInOrder.take 2) s₀ rs cols = .ok (st, [], []))
    (hcount : N.vectorWFirst + K.w.P.sent.size = (st₁ e₁).oracles.size)
    (seen : SendersAnswersSeen K N k input heard r₁)
    (sendsIndexMasks : 0 < K.idx.P.sent.size) (sendsVectorW : 0 < K.w.P.sent.size)
    (sampledIndexMasks : (shapeAt K.idx.P (K.idx.P.sent.size - 1)).answers ≠ 0)
    (sampledVectorW : (shapeAt K.w.P 0).answers ≠ 0) :
    SampleSays rdE st.st (N.indexMasksFirst + (K.idx.P.sent.size - 1))
        (wordsAtKeyOwnTest K N k input heard) ∧
      SampleSays rdE st.st N.vectorWFirst (wordsAtKeyOwnTest K N k input heard) :=
  ⟨index_masks_sample_rows_say K N k input heard alikeIndexMasks h₁ h₂ hfirst hroundIndexMasks first
      start last seen.indexMasks _ (by omega) sampledIndexMasks,
    vector_w_sample_rows_say K N k input heard hb hm alikeVectorW h₂ hroundVectorW first start last
      hcount seen.vectorW 0 sendsVectorW sampledVectorW⟩

end Stand

end ProofFile.Honest.K12.AtKey

#print axioms ProofFile.Honest.K12.AtKey.AnswersSeen
#print axioms ProofFile.Honest.K12.AtKey.answersSeen_of_longer
#print axioms ProofFile.Honest.K12.AtKey.SendersAnswersSeen
#print axioms ProofFile.Honest.K12.AtKey.sampleSays_at_later
#print axioms ProofFile.Honest.K12.AtKey.term_at_index_masks
#print axioms ProofFile.Honest.K12.AtKey.term_at_vector_w
#print axioms ProofFile.Honest.K12.AtKey.shapeAt_of_alike
#print axioms ProofFile.Honest.K12.AtKey.stays_to_own_test
#print axioms ProofFile.Honest.K12.AtKey.index_masks_sample_rows_say
#print axioms ProofFile.Honest.K12.AtKey.vector_w_sample_rows_say
#print axioms ProofFile.Honest.K12.AtKey.first_chain_members_sample_rows_say
