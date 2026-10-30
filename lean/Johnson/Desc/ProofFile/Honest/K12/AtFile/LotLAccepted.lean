-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLAccepted.lean

It states no goal. No property of the protocol is claimed.

`AcceptedS` AT THE FIRST CHAIN's CLOSING
PROXIMITY TEST (member 354), AT THE FIRST THREAD AS A VALUE (`firstThread`,
Honest/Thread/TheFirstThread.lean) LAID WITH THE FIRST CHAIN's SCRIPT AS A VALUE (`firstScriptAt`,
AtFullSide/K1/FirstScript.lean) at `Sz.ref`, at Said := `SaidOk`: `acceptedS_of_four` (LAcceptedOpens.lean)
called at that thread's letters, its premises paid but for three that are named.

  `acceptedS_at_first_thread`   the call

By what. LotLAcceptedFields.lean (hHanded, hOwn, say, agree); `letterAtL_head` (ClosingHead.lean);
`finishTable_at_firstThread` (LotLTableFirstThread.lean: hFixed); `storedWords_lt` (Honest/Law/Run.lean);
`ReadyInput`'s first clause (hValid); `leaves_outCore` (ClosingSeat.lean); `closing_at_every_place`
(LotLPublicPaid.lean: hc); `wordsBookB_at_base` (LotLBookLineAtBase.lean: the public test on the book that
the tie of the words asks); `blankGround_at_base` (LotLSeatPlaysPremises.lean).

Hypotheses. hh: the head at a return of the maker. hA: that return is the base prover's filling's at
`Sz.ref`. hf: pl is the finish. THREE NAMED PREMISES, each in the form in which its law
concludes it:
  hside    the side that the search finds at the test's place is the pair of the lot's job: the sentence
           of `L_found` (AtFullSide/K12/LettersFoundL.lean)
  hbook    the public test `closingBookTest` (LOpensBook.lean) at the maker's book
  hfive    AT EVERY STAND at which the way in returns T: the test `frontFiveB` on T's shape says yes
The first two are public: hside is called in LotLAcceptedPaid.lean (the rows beneath it are heavy), hbook in
LotLAcceptedOne.lean.

Limits.
- hfive IS A PREMISE ON EVERY STAND: one stand at which it fails makes it false, and then nothing is said.
- `AcceptedS` speaks of stands of the thread; that a stand is reached is not said.
- The full size, the format's second hash function and `Sz.ref` alone.
- All limits of LAcceptedOpens.lean hold here.
- At the base prover's filling's return, at its own type of random values: NOT AT THE ONLINE PROVER, whose
  filling reads this one through the coins' map.
- Beneath this file lie K2/Law/ClosingAtHead.lean with the files beneath it, and LAcceptedOpens.lean
  with the L*.lean files.
- The statements at the maker's return are typed at `OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit`: they cannot
  even be written at the online prover's return (`OnlineProverWithDescription FullSizeMatrix (protocolAtFiles files).EncodingRandomness Cells Unit Unit`,
  E2E/TheHonestProver.lean): no law through `OnlineProverParts.through` is made here.
- Nothing on completeness of the chain, soundness or hiding.

NOT IN FRONT OF A LAW OVER COINS: `acceptedS_at_first_thread` bears this label; the rule is at its
home, the head of Johnson/Bind/ForProver/FiveFieldsAt.lean. It calls `acceptedS_of_four`
(LAcceptedOpens.lean), which bears it.
This file's own ground, in the rule's terms.
- hh and hA speak of the public files, of the letters I and Op (how an index, an instance and the
  challenges are read, and one named member of the index's type) and of what the maker returns at
  the filling made of them. By their text they name no coin, no run's input (its index, its trace)
  and no Script: of neither kind.
- hf, hside and hbook speak of the finish, of the prover's side that the search finds at the test's
  place and of the book's entries: they name no coin.
- hfive is itself bound over all coins and every stand: by itself it picks among no coins.
- w, the run's input, is a letter under no premise in front. It holds the committer's coins (its
  field rc) and the hidden input (its fields w₀ and trace).
- numbers (the stated numbers of the falls) and fl (the fall, which stands inside `AcceptedS`) are
  letters under no premise.
- A run's coins k are bound inside the end, `AcceptedS`. Beside k it binds the letters s, m and E
  (the verifier's state, the state of the prover's side, the available tables) under `ThrS … 354 k s
  m E`: a premise of the first kind: it names k; by its text, at fixed s, m and E it can hold at
  some values of the coins and fail at others.
- `AcceptedS` binds besides y and cols under `T.Moved blk k m E ds y cols`: of the first kind.
- ds, the challenges, stands under `drawsFit` (no coin) and under `chainStopAt (T.φ.sees m.st.input)
  …`: no run's coin is among its arguments (`Part.stopAt`, Honest/Side.lean), but in the first chain
  the face shows a part's second stop the whole input of m (`Face.sees`, Honest/Frame.lean), which
  holds rc and the hidden input: of the first kind as far as such a stop reads rc, of the second as
  far as it reads the index or the trace; what the parts at 354 read is not fixed here. In
  `AcceptedS` ds stands besides under the fall, which reads s and ds: no coin.
- One clause of the invariant is of the second kind: the thread's `valid` says that the input of m
  is w and meets `ReadyInput` (Honest/Thread/ReadyInput.lean): the instance passes the description's
  test, the index is in range, the trace is the prover's own: it reads the hidden input and no coin.
- What lifts the bar: for s, m, E, y and cols the made terms would be those of the honest run at the
  border, as terms of w, k and the challenges, and the lemma would show the premises at them at
  every value of the coins. For ds, which no term of the prover's makes, the lemma would show that
  at each ds `chainStopAt … = none` holds at every value of rc or at none. None is known to this
  file: the bar is flat.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLAcceptedFields
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LAcceptedOpens
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLPublicPaid
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLBookLineAtBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K12.LotL
open VerifiableInference.Desc.K12 (T12 enterFinish)
open VerifiableInference.Desc.First (S)
open OnBytes.HonestTrace (Sz)
open H2K.Member (codesFull piLFull)
open H2K.JointK (outCore)
open ProofFile.Honest.Sh (testSh)
open ProofFile.Honest.FirstThread (HeadAtReturn FallNumbers firstLetters)
open ProofFile.Honest.K1 (LocB firstScriptAt readersB)
open ProofFile.Honest.K2 (SwitchPlace)
open ProofFile.Honest.K12.AtProof (finishAt jobL doorAtL startL idleT12 closingBookTest acceptedS_of_four
  closing_at_every_place)

variable {W₀ : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- hside, hbook AND hfive ARE PREMISES. **The closing proximity test is accepted at the first
thread.** -/
theorem acceptedS_at_first_thread (hh : HeadAtReturn files A) (I : WiderIn W₀) (Op : OnlineProverArguments)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref Op) = .ok A)
    (numbers : FallNumbers) (w : LocB W₀) {pl : SwitchPlace} (hf : finishAt A.Z A.G = some pl)
    (hside : (A.H.first.find? fun g => g.place == (H2U.p12OfMade A.Z.made).place) =
      some (proverSideOfProximityTest (jobL (H2U.p12OfMade A.Z.made) (doorAtL A.Z) (widerRows Sz.ref A.Z A.G)
                         (readersB I A.Z) (K2.lotClosingAt A.G.first.layout (K2.segmentsOf A.Z A.G)) pl)))
    (hbook : closingBookTest A.B pl ⟨(H2U.p12OfMade A.Z.made).place, 1⟩ = true)
    (hfive : ∀ k st m E T, ThrS (firstThreadAtTheFirstScript hh I Op numbers w) SaidOk 354 k st m E →
      enterFinish st = .ok T → frontFiveB piLFull codesFull (testSh T) = true)
    (fl : ℕ → S → List Fmt.Drawn → Option String) :
    AcceptedS (firstThreadAtTheFirstScript hh I Op numbers w) SaidOk fl 354 := by
  obtain ⟨blk, pre, t, hm, HL⟩ :
      ∃ blk pre t, hh.firstChain.blocksInOrder[354]? = some blk ∧
        LetterAtL (firstLetters hh ⟨firstScriptAt I Sz.ref Op A hh.firstChain, numbers⟩ w) 354
          (jobL (H2U.p12OfMade A.Z.made) (doorAtL A.Z) (widerRows Sz.ref A.Z A.G)
        (readersB I A.Z) (K2.lotClosingAt A.G.first.layout (K2.segmentsOf A.Z A.G)) pl)
          (outCore ProofFile.sameReply) (startL A.Z) idleT12 blk pre t :=
    letterAtL_head hh.head A.H _ _ _ _ _ _ _ _ _ _ w _ _ _ pl hside
  have hc := closing_at_every_place hh.head.toAtMg
  have hwords := AtProof.wordsBookB_at_base hh.head hA hf
  exact acceptedS_of_four hh.head (blankGround_at_base hh.head hA) hf
    (firstLetters hh ⟨firstScriptAt I Sz.ref Op A hh.firstChain, numbers⟩ w) (doorAtL A.Z)
    (readersB I A.Z) (outCore ProofFile.sameReply) (startL A.Z) idleT12 blk pre t HL hm rfl rfl
    (fun v => storedWords_lt A.H v.w₀ v.rc) (fun _ hv => hv.2.1)
    (finishOwnTree_at_first_thread hh I Op hA numbers w hf)
    (finishTable_at_firstThread hh hA hf numbers w).2.1
    (finishIsHanded_at_base hh I Op hA hf) hbook
    (fun k st m E T J' hJ c hT he hl => by
      have hsay := says_at_first_thread hh I Op hA numbers w hf hc hwords k st m E T J' hJ c hT he hl
      have hagree := agree_at_first_thread hh I Op hA numbers w hf k st m E T J' hJ c hT he hl
      subst hJ
      exact ⟨hfive k st m E T hT he, hsay, hagree, fun t' _ _ _ => leaves_outCore he t'⟩) fl

end ProofFile.Honest.K12.LotL

#print axioms ProofFile.Honest.K12.LotL.acceptedS_at_first_thread
