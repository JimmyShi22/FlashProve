-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/LotOwnTies.lean: THE TIE OF THE WORDS AT THE KEY FILE's OWN TEST, MEMBER BY
MEMBER: on a member's table the term `wordsAtKeyOwnTest` (LotOwnWords.lean) is what the job's own rows make at the
coins that the frame lends the test's second part (`wordsAt`, `plainMany`). General in the book, the parts, the
statement and the layout.

  `jobAtKeyOwnTest`       the job: `jobKWAt` (E2E/KeyProverSideOfOwnTest.lean) at the parts' sendings, `askTests`
  `jobAtLetters`, `job_at_letters`   the same with its numbers, its door and the first chain's count as letters
  `words_at_index_masks`, `words_at_vector_w`, `words_at_omega_copy`   the term at its three stretches of numbers
  `own_coins_cut`         where the book's row is the sender's count, the sender's own cut returns and is the term's
  `entry_of_carries`      what `carriesMessage` says, as equations
  `omega_sending_facts`, `omega_member_words`, `words_of_omega_are_sent`   Omega's member: the job's side at a job that is
                          a letter, and the words' side
  `tie_at_index_masks`, `tie_at_vector_w`, `tie_at_omega_copy`   THE THREE TIES

By what. `wordsAt_of_first_kind_member_at_purse` (AtFile/LotMemK1Words.lean), `member_held` (AtProof/HandedW.lean),
`Coins.lens₀`, `Coins.lens₁`, `Cs.cut_zero` (Honest/Law/Rule/RowLens.lean); at Omega `wordsAt_member`
(K12/WordsOfMember.lean), `sameCut_of_book` (K12/CutOfBook.lean), `rowsO_read` (Honest/K14/SendingsRows.lean), `msg_eq`,
`first_read` (AtFile/TieAtMembers.lean): the road of `tie_omega` (AtFile/OTie.lean), with the point read
behind the first chain's challenges.

Limits.
- A tie of a term to the lent coins. That a thread's witness is the term is not said here.
- NOT IN FRONT OF A LAW OVER COINS: `lendPart`'s return is a premise.
- The premises are LotOwnWords.lean's structures: none is shown to be met.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.LotOwnWords
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotMemK1Words

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.AtKey
open OnBytes (Statement Group Oracle GroupLayout)
open OnBytes.Means (Words tableSize)
open OnBytes.Slice (GE rdE)
open Johnson.Prover.Send (shapeAt)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Key (Source LaterPlaces Xi descriptionFromSource)
open Desc.K14 (first)
open Desc.K14.Honest
open Desc.K14.Law (parO)
open AtPublicFiles.KeyFile (KeyParts In1 In2 randK14)
open AtPublicFiles.KeyTest (sIdx sW)
open VerifiableInference.Desc.K12 (P12 T12)
open AtPublicFiles.KeyLay (jobKWAt jobKW pWK doorKW)
open AtFullSide.K12 (askTests)
open ProofFile.Honest.K14
open ProofFile.Honest.K12.Light
open ProofFile.Honest.K12.AtProof (member_held)
open ProofFile.Honest.K12.AtFile (ellOmegaB msg_eq first_read wordsAt_of_first_kind_member_at_purse)

variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk Wd V : Type}

/-- **The job at the key file's own test, at a prover's parts.** -/
abbrev jobAtKeyOwnTest (K : KeyParts W₀ Rc X₀ X Wk) (Xs : Source) (Nr : H2U.PlaceNums)
    (Pl : LaterPlaces) : ManyJob (Local W₀ Rc Xi Unit) X :=
  jobKWAt Xs Nr Pl K.idx K.w K.send id (askTests K)

/-- **The same job with its numbers, its door and the first chain's count as letters**: the ties are proved here. -/
abbrev jobAtLetters (K : KeyParts W₀ Rc X₀ X Wk) (q : P12)
    (door : Local W₀ Rc Xi Unit → Front X → T12) (firstChain : ℕ) :
    ManyJob (Local W₀ Rc Xi Unit) X :=
  jobKW q door K.idx K.w K.send id (askTests K) firstChain

/-- The job is that one at the chain's own three. -/
theorem job_at_letters (K : KeyParts W₀ Rc X₀ X Wk) (Xs : Source) (Nr : H2U.PlaceNums)
    (Pl : LaterPlaces) :
    jobAtKeyOwnTest K Xs Nr Pl = jobAtLetters K (pWK Pl) (doorKW Xs Nr Pl)
      ((descriptionFromSource Xs Nr Pl).first.blocksInOrder.flatMap (·.rounds)).length := rfl

section Term
variable (K : KeyParts W₀ Rc X₀ X Wk) (N : OwnTestNumbers) (k : Coins Bk) (input : In1 W₀ Rc)
  (heard : List Fmt.Drawn) (part : OnBytes.Part) (i : ℕ)

/-- The term at the copy's number. -/
theorem words_at_omega_copy :
    wordsAtKeyOwnTest K N k input heard N.omegaCopy part i =
      wordsOfOmegaAtKey K N k input heard part i := by
  show (if N.omegaCopy = N.omegaCopy then _ else _) = _
  rw [if_pos rfl]

/-- The term at a message of W's sending. -/
theorem words_at_vector_w (h : N.vectorWFirst + K.w.P.sent.size ≤ N.omegaCopy) (j : ℕ)
    (hj : j < K.w.P.sent.size) :
    wordsAtKeyOwnTest K N k input heard (N.vectorWFirst + j) part i =
      (rowsOfSending k sW K.w input K.own₀ heard N.challengesBeforeVectorW j).word
        (shapeAt K.w.P j) part i := by
  show (if N.vectorWFirst + j = N.omegaCopy then _ else
    if N.vectorWFirst ≤ N.vectorWFirst + j ∧ N.vectorWFirst + j < N.vectorWFirst + K.w.P.sent.size
      then (rowsOfSending k sW K.w input K.own₀ heard N.challengesBeforeVectorW
        (N.vectorWFirst + j - N.vectorWFirst)).word
          (shapeAt K.w.P (N.vectorWFirst + j - N.vectorWFirst)) part i
      else _) = _
  rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]

/-- The term at a message of the index masks' sending. -/
theorem words_at_index_masks (h₁ : N.indexMasksFirst + K.idx.P.sent.size ≤ N.vectorWFirst)
    (h₂ : N.vectorWFirst + K.w.P.sent.size ≤ N.omegaCopy) (j : ℕ) (hj : j < K.idx.P.sent.size) :
    wordsAtKeyOwnTest K N k input heard (N.indexMasksFirst + j) part i =
      (rowsOfSending k sIdx K.idx input K.own₀ heard N.challengesBeforeIndexMasks j).word
        (shapeAt K.idx.P j) part i := by
  show (if N.indexMasksFirst + j = N.omegaCopy then _ else
    if N.vectorWFirst ≤ N.indexMasksFirst + j ∧
        N.indexMasksFirst + j < N.vectorWFirst + K.w.P.sent.size then _
      else if N.indexMasksFirst ≤ N.indexMasksFirst + j ∧
          N.indexMasksFirst + j < N.indexMasksFirst + K.idx.P.sent.size
        then (rowsOfSending k sIdx K.idx input K.own₀ heard N.challengesBeforeIndexMasks
          (N.indexMasksFirst + j - N.indexMasksFirst)).word
            (shapeAt K.idx.P (N.indexMasksFirst + j - N.indexMasksFirst)) part i
        else _) = _
  rw [if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]

end Term

/-- **Where the book's row is the sender's count, in the first chain's table alone, the sender's own cut returns,
and it is the term's.** -/
theorem own_coins_cut (k : Coins Bk) (a : Addr) (J : K1.SendJob Wd X)
    (hd : dueAt Bk.first a = K1.dueR J.P J.ride) (h₂ : noRowIn Bk.shared a)
    (h₃ : noRowIn Bk.second a) :
    (k.look 0 a).2.cut ⟨0, 0⟩ (K1.dueR J.P J.ride) = some (ownCoinsOfSending k a J) := by
  obtain ⟨get, -, -, -, hk⟩ := Coins.lens₀ a _ hd h₂ h₃
  unfold ownCoinsOfSending
  rw [hk 0 (Or.inl rfl) k]
  show (get k).cut ⟨0, 0⟩ _ = some (((get k).cut ⟨0, 0⟩ _).getD default)
  rw [Cs.cut_zero]
  rfl

/-- What `carriesMessage` says, as equations. -/
theorem entry_of_carries {spender sender : Addr} {n message : ℕ}
    {P : VerifiableInference.Desc.K1.Par} {ride : ℕ → Option K1.Ride}
    (h : carriesMessage Bk spender n sender P ride message = true) :
    ∃ e, (carryE Bk spender)[n]? = some e ∧ e.owner = sender ∧
      e.start = K1.startR P ride message ∧
      e.count = K1.dueMsg P.codes (shapeAt P message) (ride message) := by
  unfold carriesMessage at h
  split at h
  · rename_i e he
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨e, he, h.1.1, h.1.2, h.2⟩
  · cases h

/-- What the plan says of "send o_omega"'s two messages. -/
theorem omega_sending_facts {Q : Desc.K14.P14} (plan : SharedPlanAtOwnTest Q) :
    (jobOmega ⟨Q, 0⟩).Q.sent.size = 2 ∧
      ((jobOmega ⟨Q, 0⟩).Q.sent.getD 0 default).shape = Q.par.S.omega ∧
      ((jobOmega ⟨Q, 0⟩).Q.sent.getD 1 default).shape = Q.par.S.sharedSplit ∧
      Q.par.S.sharedSplit.mainRows = 0 := by
  obtain ⟨layO, hP⟩ := plan.plan
  have hw : (Desc.K14.withOmega Q.S).size = 2 ∧
      (Desc.K14.withOmega Q.S)[0]? = some ⟨Q.S.omega, Q.S.omegaLeafClass⟩ ∧
      (Desc.K14.withOmega Q.S)[1]? = some ⟨Q.S.sharedSplit, Q.S.sharedSplitLeafClass⟩ :=
    Desc.K14.Honest.withOmega_two hP.facts.two
  have sOs : (jobOmega ⟨Q, 0⟩).Q.sent = Desc.K14.withOmega Q.S :=
    Desc.K14.Law.parK1_sent Q 5 _ _
  refine ⟨by rw [sOs]; exact hw.1, ?_, ?_, sp_noMain hP⟩
  · exact (shapeAt_of_get (jobOmega ⟨Q, 0⟩).Q 0 ⟨Q.par.S.omega, Q.par.S.omegaLeafClass⟩
      (by rw [sOs]; exact hw.2.1)).1
  · exact (shapeAt_of_get (jobOmega ⟨Q, 0⟩).Q 1
      ⟨Q.par.S.sharedSplit, Q.par.S.sharedSplitLeafClass⟩ (by rw [sOs]; exact hw.2.2)).1

/-- **The job's side at Omega's member**: at a job J that has "send o_omega"'s public data and, at the test's front,
its vector at the list l: the words that the job's rows make are the sender's coded table at l, read. J is a letter:
the number of "LIN point" in it is read by hJd alone. -/
theorem omega_member_words {W Y : Type} (Q : Desc.K14.P14) (plan : SharedPlanAtOwnTest Q)
    (J : SendJob) (hJQ : J.Q = (jobOmega ⟨Q, 0⟩).Q) (hJs : J.sort = (jobOmega ⟨Q, 0⟩).sort)
    (at_ : Addr) (fs : Option ℕ × Option ℕ) (ask : W → Ask) (w : W) (fr : Front Y)
    (l : List Fmt.Drawn)
    (hJd : J.data (⟨ask w, fr.heard, ()⟩ : State Ask Unit) =
      (jobOmega ⟨Q, 0⟩).data (⟨ask w, l, ()⟩ : State Ask Unit))
    (cs : Array OnBytes.E) (A : ManyJob W Y) (n : ℕ)
    (hn : A.mems[n]? = some (memOfSending J at_ 0 fs ask none)) (C : TestCoins)
    (sc : SameCut (jobOmega ⟨Q, 0⟩) 0 cs (C.mem n)) (S : Statement) (L : GroupLayout) (o : ℕ)
    (hfind : L.find o = some n) (y : Oracle) (hy : S.oracles[o]? = some y)
    (hys : y.shape = Light.shapeAt (jobOmega ⟨Q, 0⟩) 0) (hcd : S.codes = Q.codes)
    (pt : OnBytes.Part) (i : ℕ) (hi : i < tableSize S o pt) :
    ProofFile.Honest.K12.wordsAt S L (plainMany A w fr C) o pt i =
      rdE.val (wordsOf (jobOmega ⟨Q, 0⟩).Q.sent
        ((jobOmega ⟨Q, 0⟩).rows (⟨ask w, l, ()⟩ : State Ask Unit) cs) 0 pt i) := by
  obtain ⟨hsz, hs0, -, -⟩ := omega_sending_facts plan
  have hE := plan.length
  unfold ellOmegaB at hE
  rw [beq_iff_eq] at hE
  have hsh : Light.shapeAt J 0 = Light.shapeAt (jobOmega ⟨Q, 0⟩) 0 := by
    unfold Light.shapeAt
    rw [hJQ]
  have sc' : SameCut J 0 cs (C.mem n) := by
    unfold SameCut at sc ⊢
    rw [hsh, hJQ, hJs]
    exact sc
  have hrows : J.rows (⟨ask w, fr.heard, ()⟩ : State Ask Unit) cs =
      (jobOmega ⟨Q, 0⟩).rows (⟨ask w, l, ()⟩ : State Ask Unit) cs := by
    funext m
    unfold SendJob.rows
    rw [hJd, hJQ, hJs]
  have wM := wordsAt_member Q plan.fits J (Or.inr ⟨hJQ, hJs⟩) 0 (by rw [hJQ, hsz]; decide)
    Q.S.omegaRowsHigh (by rw [hJs]; rfl) at_ fs ask none w fr
    (⟨ask w, fr.heard, ()⟩ : State Ask Unit) rfl cs A n hn C sc' S L o hfind y hy
    (hys.trans hsh.symm) (by rw [hcd, hJQ]; rfl)
    (fun _ => by rw [hsh, hJQ]; exact hE)
    (fun hpos => absurd hpos (by
      rw [hsh]
      show ¬ 0 < ((jobOmega ⟨Q, 0⟩).Q.sent.getD 0 default).shape.maskRows
      rw [hs0, plan.shapes.omega.noMask]
      exact Nat.lt_irrefl 0)) pt i hi
  rw [hrows, hJQ] at wM
  exact wM

/-- **The words' side at Omega**: the term's tables at the copy are the sender's coded table, read, at the sender's
own purse and at the challenges behind the first chain's. -/
theorem words_of_omega_are_sent (K : KeyParts W₀ Rc X₀ X Wk) (N : OwnTestNumbers)
    (plan : SharedPlanAtOwnTest K.send.P) (k : Coins Bk) (input : In1 W₀ Rc)
    (heard : List Fmt.Drawn) (hne : heard.drop N.challengesOfFirstChain ≠ [])
    (hpt : (Desc.K14.drawn (firstRv (heard.drop N.challengesOfFirstChain))).length =
      K.send.P.par.S.kCol)
    (own : Cs (sendingPart (jobOmega ⟨K.send.P, 0⟩)).takes)
    (c1 : (k.look 1 ⟨sendPlace 5, 0⟩).2.cut ⟨0, 0⟩
      (sendingPart (jobOmega ⟨K.send.P, 0⟩)).takes = some own)
    (nO : (k.look 1 ⟨sendPlace 5, 0⟩).1.e = (sendingPart (jobOmega ⟨K.send.P, 0⟩)).takes.e)
    (pt : OnBytes.Part) (i : ℕ) :
    wordsOfOmegaAtKey K N k input heard pt i =
      rdE.val (wordsOf (jobOmega ⟨K.send.P, 0⟩).Q.sent
        ((jobOmega ⟨K.send.P, 0⟩).rows
          (⟨askTests K input, heard.drop N.challengesOfFirstChain, ()⟩ : State Ask Unit)
          (coinsE own).toArray) 0 pt i) := by
  obtain ⟨hsz, hs0, hs1, hnoSp⟩ := omega_sending_facts plan
  have mO := fun n => msg_eq k (jobOmega ⟨K.send.P, 0⟩) (sendPlace 5) n own c1 nO
  have rO := rowsO_read K.send.P (first K.send.P.codes input.x.key)
    (firstRv (heard.drop N.challengesOfFirstChain))
    (holds2 K.send.P K.weights (fun c => randK14 (K.rand c)) k (commonOfInput input))
    (askTests K input) (heard.drop N.challengesOfFirstChain) (coinsE own).toArray
    (by rw [hsz]) hs0 hs1 plan.shapes.omega hnoSp (first_read _ _ hne) hpt (fun _ _ => rfl)
    (by
      show readCoins _ _ (coinsOfMsg k _ _ 0) = _
      rw [mO 0]
      rfl)
    (by
      show readCoins _ _ (coinsOfMsg k _ _ 1) = _
      rw [mO 1]
      rfl) 0 (by rw [hsz]; decide) pt i
  refine Eq.trans ?_ rO.symm
  show (if 0 + 2 ≤ 2 ∧ 2 < 0 + 2 + (parO K.send.P).sent.size then _ else _) = _
  rw [if_pos ⟨by omega, by
    have e' : (parO K.send.P).sent.size = 2 := hsz
    rw [e']
    decide⟩]
  rfl

section Ties
variable (K : KeyParts W₀ Rc X₀ X Wk) (q : P12) (door : Local W₀ Rc Xi Unit → Front X → T12)
  (firstChain : ℕ) (N : OwnTestNumbers)

/-- **THE TIE AT THE INDEX MASKS' MESSAGE**, the job's member 0.
NOT IN FRONT OF A LAW OVER COINS: this file's head. -/
theorem tie_at_index_masks (reads : SendersReadInFront K N)
    (book : BookAtOwnTest Bk K q.place)
    (h₁ : N.indexMasksFirst + K.idx.P.sent.size ≤ N.vectorWFirst)
    (h₂ : N.vectorWFirst + K.w.P.sent.size ≤ N.omegaCopy) (hsends : 0 < K.idx.P.sent.size)
    (k : Coins Bk) (input : In1 W₀ Rc) (fr : Front X) (heard : List Fmt.Drawn)
    (hheard : fr.heard.take N.challengesBeforeIndexMasks =
      heard.take N.challengesBeforeIndexMasks)
    (c : (restPart (jobAtLetters K q door firstChain).toRun.toTest : Part V _ _).Coins)
    (hlp : lendPart Bk (Bk.rowsOf 2) (k.look 2) ⟨q.place, 1⟩
      (restPart (jobAtLetters K q door firstChain).toRun.toTest : Part V _ _) = .ok c)
    (S : Statement) (L : GroupLayout)
    (hfind : L.find (N.indexMasksFirst + (K.idx.P.sent.size - 1)) = some 0) (y : Oracle)
    (hy : S.oracles[N.indexMasksFirst + (K.idx.P.sent.size - 1)]? = some y)
    (hys : y.shape = shapeAt K.idx.P (K.idx.P.sent.size - 1)) (pt : OnBytes.Part) (i : ℕ) :
    wordsAtKeyOwnTest K N k input heard (N.indexMasksFirst + (K.idx.P.sent.size - 1)) pt i =
      ProofFile.Honest.K12.wordsAt S L (plainMany (jobAtLetters K q door firstChain) input fr
              (restCoins (jobAtLetters K q door firstChain).toRun.toTest c))
        (N.indexMasksFirst + (K.idx.P.sent.size - 1)) pt i := by
  have hm : K.idx.P.sent.size - 1 < K.idx.P.sent.size := Nat.sub_lt hsends Nat.one_pos
  obtain ⟨e, he, ho, hs, hc⟩ := entry_of_carries book.carriesIndexMasks
  have hcut := own_coins_cut k sIdx K.idx book.rowIndexMasks book.indexMasksNotShared
    book.indexMasksNotLast
  have hold := member_held k hlp he K.idx.P K.idx.ride _ hm hs hc
    (by rw [ho]; exact book.rowIndexMasks) (by rw [ho]; exact book.indexMasksNotShared)
    (by rw [ho]; exact book.indexMasksNotLast) (c₀ := ownCoinsOfSending k sIdx K.idx)
    (by rw [ho]; exact hcut)
  rw [words_at_index_masks K N k input heard pt i h₁ h₂ _ hm]
  exact (wordsAt_of_first_kind_member_at_purse K.idx id sIdx _ hm _ (jobAtLetters K q door firstChain) 0
    rfl input fr (restCoins (jobAtLetters K q door firstChain).toRun.toTest c) _
    (reads.indexMasks input fr (frontBeforeSending K.own₀ heard N.challengesBeforeIndexMasks) (by
      show _ = (heard.take _).take _
      rw [List.take_take, Nat.min_self]
      exact hheard))
    (ownCoinsOfSending k sIdx K.idx) hold.1 hold.2 S L _ hfind y hy hys pt i).symm

/-- **THE TIE AT W**, the job's member 1.
NOT IN FRONT OF A LAW OVER COINS: this file's head. -/
theorem tie_at_vector_w (reads : SendersReadInFront K N)
    (book : BookAtOwnTest Bk K q.place)
    (h₂ : N.vectorWFirst + K.w.P.sent.size ≤ N.omegaCopy) (hsends : 0 < K.w.P.sent.size)
    (k : Coins Bk) (input : In1 W₀ Rc) (fr : Front X) (heard : List Fmt.Drawn)
    (hheard : fr.heard.take N.challengesBeforeVectorW = heard.take N.challengesBeforeVectorW)
    (c : (restPart (jobAtLetters K q door firstChain).toRun.toTest : Part V _ _).Coins)
    (hlp : lendPart Bk (Bk.rowsOf 2) (k.look 2) ⟨q.place, 1⟩
      (restPart (jobAtLetters K q door firstChain).toRun.toTest : Part V _ _) = .ok c)
    (S : Statement) (L : GroupLayout) (hfind : L.find N.vectorWFirst = some 1) (y : Oracle)
    (hy : S.oracles[N.vectorWFirst]? = some y) (hys : y.shape = shapeAt K.w.P 0)
    (pt : OnBytes.Part) (i : ℕ) :
    wordsAtKeyOwnTest K N k input heard N.vectorWFirst pt i =
      ProofFile.Honest.K12.wordsAt S L (plainMany (jobAtLetters K q door firstChain) input fr
              (restCoins (jobAtLetters K q door firstChain).toRun.toTest c)) N.vectorWFirst pt i := by
  obtain ⟨e, he, ho, hs, hc⟩ := entry_of_carries book.carriesVectorW
  have hcut := own_coins_cut k sW K.w book.rowVectorW book.vectorWNotShared book.vectorWNotLast
  have hold := member_held k hlp he K.w.P K.w.ride 0 hsends hs hc
    (by rw [ho]; exact book.rowVectorW) (by rw [ho]; exact book.vectorWNotShared)
    (by rw [ho]; exact book.vectorWNotLast) (c₀ := ownCoinsOfSending k sW K.w)
    (by rw [ho]; exact hcut)
  have e0 := words_at_vector_w K N k input heard pt i h₂ 0 hsends
  rw [Nat.add_zero] at e0
  rw [e0]
  exact (wordsAt_of_first_kind_member_at_purse K.w id sW 0 hsends _ (jobAtLetters K q door firstChain) 1
    rfl input fr (restCoins (jobAtLetters K q door firstChain).toRun.toTest c) _
    (reads.vectorW input fr (frontBeforeSending K.own₀ heard N.challengesBeforeVectorW) (by
      show _ = (heard.take _).take _
      rw [List.take_take, Nat.min_self]
      exact hheard))
    (ownCoinsOfSending k sW K.w) hold.1 hold.2 S L _ hfind y hy hys pt i).symm

/-- **THE TIE AT OMEGA's COPY**, the job's member 2.
NOT IN FRONT OF A LAW OVER COINS: this file's head. -/
theorem tie_at_omega_copy (reads : SendersReadInFront K N)
    (book : BookAtOwnTest Bk K q.place) (plan : SharedPlanAtOwnTest K.send.P)
    (hfirst : N.challengesOfFirstChain = firstChain)
    (k : Coins Bk) (input : In1 W₀ Rc) (fr : Front X) (heard : List Fmt.Drawn)
    (hpoint : (fr.heard.drop N.challengesOfFirstChain).take 1 =
      (heard.drop N.challengesOfFirstChain).take 1)
    (hne : heard.drop N.challengesOfFirstChain ≠ [])
    (hpt : (Desc.K14.drawn (firstRv (heard.drop N.challengesOfFirstChain))).length =
      K.send.P.par.S.kCol)
    (c : (restPart (jobAtLetters K q door firstChain).toRun.toTest : Part V _ _).Coins)
    (hlp : lendPart Bk (Bk.rowsOf 2) (k.look 2) ⟨q.place, 1⟩
      (restPart (jobAtLetters K q door firstChain).toRun.toTest : Part V _ _) = .ok c)
    (S : Statement) (L : GroupLayout) (hfind : L.find N.omegaCopy = some 2) (y : Oracle)
    (hy : S.oracles[N.omegaCopy]? = some y)
    (hys : y.shape = Light.shapeAt (jobOmega ⟨K.send.P, 0⟩) 0) (hcd : S.codes = K.send.P.codes)
    (pt : OnBytes.Part) (i : ℕ) (hi : i < tableSize S N.omegaCopy pt) :
    wordsAtKeyOwnTest K N k input heard N.omegaCopy pt i =
      ProofFile.Honest.K12.wordsAt S L (plainMany (jobAtLetters K q door firstChain) input fr
              (restCoins (jobAtLetters K q door firstChain).toRun.toTest c)) N.omegaCopy pt i := by
  obtain ⟨get, -, -, -, hk⟩ := Coins.lens₁ (⟨sendPlace 5, 0⟩ : Addr) _ book.rowOmega
    book.omegaNotFirst book.omegaNotLast
  have c1 : (k.look 1 ⟨sendPlace 5, 0⟩).2.cut ⟨0, 0⟩
      (sendingPart (jobOmega ⟨K.send.P, 0⟩)).takes = some (get k) := by
    rw [hk 1 (Or.inl rfl) k]
    exact Cs.cut_zero _
  have c2 : (k.look 2 ⟨sendPlace 5, 0⟩).2.cut ⟨0, 0⟩
      (sendingPart (jobOmega ⟨K.send.P, 0⟩)).takes = some (get k) := by
    rw [hk 2 (Or.inr rfl) k]
    exact Cs.cut_zero _
  have nO : (k.look 1 ⟨sendPlace 5, 0⟩).1.e = (sendingPart (jobOmega ⟨K.send.P, 0⟩)).takes.e := by
    rw [hk 1 (Or.inl rfl) k]
  have sc : SameCut (jobOmega ⟨K.send.P, 0⟩) 0 (coinsE (get k)).toArray
      (stretches _ c.2.2 2) :=
    sameCut_of_book Bk _ _ _ _ c hlp _ (jobOmega ⟨K.send.P, 0⟩) (get k) c2 2 0 book.carriesOmega
  -- the point: the job reads it behind the first chain's challenges, the words at the head of what is left
  have hh : heardFrom (⟨askTests K input, fr.heard, ()⟩ : State Ask Unit)
      (firstChain + K.send.atPoint) 1 =
      heardFrom (⟨askTests K input, heard.drop N.challengesOfFirstChain, ()⟩ : State Ask Unit)
        0 1 := by
    unfold heardFrom
    show (fr.heard.drop _).take 1 = ((heard.drop N.challengesOfFirstChain).drop 0).take 1
    rw [reads.point, Nat.add_zero, ← hfirst, List.drop_zero]
    exact hpoint
  have hdata : (jobOmega ⟨K.send.P, firstChain + K.send.atPoint⟩).data
        (⟨askTests K input, fr.heard, ()⟩ : State Ask Unit) =
      (jobOmega ⟨K.send.P, 0⟩).data
        (⟨askTests K input, heard.drop N.challengesOfFirstChain, ()⟩ : State Ask Unit) := by
    funext n
    show Desc.K14.Honest.omegaAtE _ (elems (heardFrom _ _ 1)) _ =
      Desc.K14.Honest.omegaAtE _ (elems (heardFrom _ 0 1)) _
    rw [hh]
  rw [words_at_omega_copy]
  exact (words_of_omega_are_sent K N plan k input heard hne hpt (get k) c1 nO pt i).trans
    (omega_member_words K.send.P plan (jobOmega ⟨K.send.P, firstChain + K.send.atPoint⟩) rfl rfl _ _
      (askTests K) input fr _ hdata _ (jobAtLetters K q door firstChain) 2 rfl
      (restCoins (jobAtLetters K q door firstChain).toRun.toTest c) sc S L N.omegaCopy hfind y hy hys
      hcd pt i hi).symm

end Ties

end ProofFile.Honest.K12.AtKey

end

#print axioms ProofFile.Honest.K12.AtKey.jobAtKeyOwnTest
#print axioms ProofFile.Honest.K12.AtKey.jobAtLetters
#print axioms ProofFile.Honest.K12.AtKey.job_at_letters
#print axioms ProofFile.Honest.K12.AtKey.words_at_omega_copy
#print axioms ProofFile.Honest.K12.AtKey.words_at_vector_w
#print axioms ProofFile.Honest.K12.AtKey.words_at_index_masks
#print axioms ProofFile.Honest.K12.AtKey.own_coins_cut
#print axioms ProofFile.Honest.K12.AtKey.entry_of_carries
#print axioms ProofFile.Honest.K12.AtKey.omega_sending_facts
#print axioms ProofFile.Honest.K12.AtKey.omega_member_words
#print axioms ProofFile.Honest.K12.AtKey.words_of_omega_are_sent
#print axioms ProofFile.Honest.K12.AtKey.tie_at_index_masks
#print axioms ProofFile.Honest.K12.AtKey.tie_at_vector_w
#print axioms ProofFile.Honest.K12.AtKey.tie_at_omega_copy
