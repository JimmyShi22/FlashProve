-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLAcceptedFields.lean

It states no goal. No property of the protocol is claimed.

AT THE FIRST THREAD AS A VALUE
(`firstThread`, Honest/Thread/TheFirstThread.lean) LAID WITH THE FIRST CHAIN's SCRIPT AS A VALUE
(`firstScriptAt`, AtFullSide/K1/FirstScript.lean) at `Sz.ref`: what `acceptedS_of_four`
(LAcceptedOpens.lean) asks at the first chain's closing proximity test (member 354),
premise by premise, each a theorem of its own in that theorem's letters. That file is not imported
here: the rows beneath it are heavy.

  `finishIsHanded_at_base`          hHanded: at every run's coins the frame hands the finish's part coins
  `finishOwnTree_at_first_thread`   hOwn: `OwnTreesAt` at member 353, one tree: the finish's table 0
  `says_at_first_thread`            the field say of `StandLeft`: the rows that the test takes in say their
                                    claims of the words that the job's rows make
  `agree_at_first_thread`           the field agree: the two parts' coins agree

By what. `switch_lends_at_written` (AtFullSide/K14), `handed_isSome_book`, `book_is_written`,
`finish_is_written`, `lookDue_first` (LotLOwedLetters.lean, LotLOwedAtHead.lean);
`finishTable_at_firstThread` (LotLTableFirstThread.lean), `treesTo_353` (LotLTableHead.lean);
`says_head_L` (ClosingSaysAt.lean), `wordsTied_at_first_thread` (LotLScriptThread.lean),
`thrS_reach_below` (Honest/Thread/ReachAtHead.lean); `agree_at_L` (ClosingRun.lean),
`closingTestTies_at_base` (LotLSeatPlaysPremises.lean), `stages_L_shape` (ClosingHead.lean).

Hypotheses. hh: the head at a return of the maker. hA: that return is the base prover's filling's at
`Sz.ref`. hf: pl is the finish. `says_at_first_thread` also: hc, the statement of
`closing_at_head`; hwords, the public test `wordsBookB` at the maker's book: both as
`wordsTied_at_first_thread` asks them.

Limits.
- The full size, the format's second hash function and `Sz.ref` alone.
- hc and hwords are premises here.
- The last two speak of stands of the thread; that a stand is reached is not said.
- At the base prover's filling's return, at its own type of random values: NOT AT THE ONLINE PROVER,
  whose filling reads this one through the coins' map.
- The statements at the maker's return are typed at `OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit`: they cannot
  even be written at the online prover's return (`OnlineProverWithDescription FullSizeMatrix (protocolAtFiles files).EncodingRandomness Cells Unit Unit`,
  E2E/TheHonestProver.lean): no law through `OnlineProverParts.through` is made here.
- Nothing on completeness of the chain, soundness or hiding.

NOT IN FRONT OF A LAW OVER COINS: `finishOwnTree_at_first_thread`, `says_at_first_thread` and
`agree_at_first_thread` bear this label; the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean.
This file's own ground, in the rule's terms.
- hh and hA speak of the public files, of the letters I and Op (how an index, an instance and the
  challenges are read, and one named member of the index's type) and of what the maker returns at
  the filling made of them. By their text they name no coin, no run's input (its index, its trace)
  and no Script: of neither kind.
- hf, hc and hwords speak of the finish, of the closing's public test and of the book's entries:
  they name no coin.
- w, the run's input, is a letter under no premise in front. It holds the committer's coins (its
  field rc) and the hidden input (its fields w₀ and trace).
- numbers (the stated numbers of the falls) is a letter under no premise.
- A run's coins k are bound inside each end. Beside k `says_at_first_thread` and
  `agree_at_first_thread` bind the letters st, m and E (the verifier's state, the state of the
  prover's side, the available tables) under `ThrS … 354 k st m E`; `finishOwnTree_at_first_thread`,
  through `OwnTreesAt` (Honest/Thread/ScriptLots.lean), binds s, m and E under `ThrS … b' k s m E`
  at every border b' behind 353: premises of the first kind: they name k; by their text, at fixed
  states and tables they can hold at some values of the coins and fail at others.
- `says_at_first_thread` and `agree_at_first_thread` bind besides c under `lendRow … (k.look …) … =
  .ok c`, and the first R under `carryRows … (restCoins J' c.2.1).mem = .ok R`: of the first kind.
  J' under its equation, the record T under `enterFinish st = .ok T` and G' under `T.st.groups[T.g]?
  = some G'` name no coin.
- One clause of the invariant is of the second kind: the thread's `valid` says that the input of m
  is w and meets `ReadyInput` (Honest/Thread/ReadyInput.lean): the instance passes the description's
  test, the index is in range, the trace is the prover's own: it reads the hidden input and no coin.
- `finishIsHanded_at_base` bears none: it holds at every k and has no such premise.
- What lifts the bar. For c and R the made terms are what `lendRow` and `carryRows` return:
  `carryRows_returns_at_input` (LReturnsClosing.lean) shows, from the head, the ground and the
  finish, at the rows of `Sz.ref` and at every input whose instance passes the description's test,
  that the second returns whatever is lent. For the states, m and E the made terms would be those of
  the honest run at the border, as terms of w, k and the challenges, and the lemma would show the
  premises at them at every value of the coins. None is known to this file: so the bar is flat.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLScriptThread
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLTableFirstThread
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLSeatPlaysPremises
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLOwedAtHead
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingSaysAt
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K12.LotL
open OnBytes.Slice (rdE begun runRows)
open OnBytes.Means (layoutOf AllSay)
open VerifiableInference.Desc.K12 (T12 enterFinish)
open OnBytes.HonestTrace (Sz)
open H2K.Pub (sgOf)
open ProofFile.Honest.FirstThread (HeadAtReturn FallNumbers OwnTreesAt thrS_reach_below flat_length_head)
open ProofFile.Honest.K1 (LocB readersB)
open ProofFile.Honest.K2 (SwitchPlace)
open ProofFile.Honest.K12.AtProof (plainL finishAt jobL doorAtL heardL ClosingAtEveryPlace)

variable {W₀ : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- **hHanded: at every run's coins the frame hands the finish's part coins.** -/
theorem finishIsHanded_at_base (hh : HeadAtReturn files A) (I : WiderIn W₀) (Op : OnlineProverArguments)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref Op) = .ok A)
    {pl : SwitchPlace} (hf : finishAt A.Z A.G = some pl) :
    ∀ k : Coins A.B, (K2.handed 0 pl k).isSome = true := by
  intro k
  obtain ⟨-, hm⟩ := AtProof.finish_is_written hh.head.toAtMg (blankGround_at_base hh.head hA) hf
  have hl := AtFullSide.K14.switch_lends_at_written
    (AtProof.book_is_written hh.head.toAtMg (makersBook_at_base hh.head hA)) hm
  rw [AtProof.lookDue_first] at hl
  rw [AtProof.handed_isSome_book 0 (Nat.zero_le 1) pl k]
  exact hl

/-- **hOwn: the thread's table of the finish's one tree is the finish's table number 0.** -/
theorem finishOwnTree_at_first_thread (hh : HeadAtReturn files A) (I : WiderIn W₀) (Op : OnlineProverArguments)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref Op) = .ok A)
    (numbers : FallNumbers) (w : LocB W₀) {pl : SwitchPlace} (hf : finishAt A.Z A.G = some pl) :
    OwnTreesAt (firstThreadAtTheFirstScript hh I Op numbers w) SaidOk 353 1 fun j k v hd =>
      (pl.place, K2.switchTableAt A.B 0 (K2.coreSender K2.freshTable) (widerRows Sz.ref A.Z A.G)
        (readersB I A.Z) (K2.lotClosingAt A.G.first.layout (K2.segmentsOf A.Z A.G)) pl k v hd j) := by
  intro j hj b' k s m E _ _
  obtain rfl : j = 0 := by omega
  have e76 : treesTo (firstThreadAtTheFirstScript hh I Op numbers w).bs 353 + 0 = 76 := by
    show treesTo hh.firstChain.blocksInOrder 353 + 0 = 76
    rw [ProofFile.Honest.K12.treesTo_353 hh.head.toAtMg]
  rw [e76]
  unfold Thread.tableAt
  rw [(finishTable_at_firstThread hh hA hf numbers w).1]
  exact ⟨rfl, Table.same_refl _⟩

/-- hc AND hwords ARE PREMISES. **The field say: the rows that the test takes in say their claims of the
words that the job's rows make.** -/
theorem says_at_first_thread (hh : HeadAtReturn files A) (I : WiderIn W₀) (Op : OnlineProverArguments)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref Op) = .ok A)
    (numbers : FallNumbers) (w : LocB W₀) {pl : SwitchPlace} (hf : finishAt A.Z A.G = some pl)
    (hc : ClosingAtEveryPlace files A.Z hh.places hh.firstChain)
    (hwords : AtProof.wordsBookB A.B ⟨pl.place, 0⟩ ⟨(H2U.p12OfMade A.Z.made).place, 1⟩
      pl.front.length = true) :
    ∀ k st m E T (J' : TestJob (LocB W₀) Unit),
      J' = atStand (jobL (H2U.p12OfMade A.Z.made) (doorAtL A.Z) (widerRows Sz.ref A.Z A.G)
        (readersB I A.Z) (K2.lotClosingAt A.G.first.layout (K2.segmentsOf A.Z A.G)) pl) m.st.input
        (frontOf m) T →
      ∀ c : RowCoins [(firstPart J' : Part (LocB W₀) (LocB W₀) Unit), restPart J'],
      ThrS (firstThreadAtTheFirstScript hh I Op numbers w) SaidOk 354 k st m E →
      enterFinish st = .ok T →
      lendRow A.B (A.B.rowsOf (firstThreadAtTheFirstScript hh I Op numbers w).chain)
        (k.look (firstThreadAtTheFirstScript hh I Op numbers w).chain) J'.p.place
        [(firstPart J' : Part (LocB W₀) (LocB W₀) Unit), restPart J'] 0 = .ok c →
      ∀ R : Johnson.Prover.Send.Rows,
      AtProof.carryRows (widerRows Sz.ref A.Z A.G) (readersB I A.Z)
        (K2.lotClosingAt A.G.first.layout (K2.segmentsOf A.Z A.G)) pl m.st.input
        (heardL (frontOf m)) (restCoins J' c.2.1).mem = .ok R →
      ∀ G', T.st.groups[T.g]? = some G' →
      AllSay rdE (begun T.st T.g G') (runRows T.st G').toList
        (wordsAt (begun T.st T.g G') (layoutOf T.st G')
          (plainL R (J'.first m.st.input (frontOf m) (restCoins J' c.2.1)))) :=
  fun k st m E T J' hJ c hT he hl R ho G' hG' =>
    says_head_L hh.head A.H _ _ _ _ _ _ _ _ _ _ w hT.1
      (thrS_reach_below hh.head A.H _ _ _ _ _ _ _ _ _ _ w
        (by rw [flat_length_head hh.head]; decide) hT) he _ hG'
      (wordsTied_at_first_thread hh I Op hA numbers w hf hc hwords k st m E T J' hJ c hT he hl R ho
        G' hG')

/-- **The field agree: the two parts' coins agree.** -/
theorem agree_at_first_thread (hh : HeadAtReturn files A) (I : WiderIn W₀) (Op : OnlineProverArguments)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref Op) = .ok A)
    (numbers : FallNumbers) (w : LocB W₀) {pl : SwitchPlace} (hf : finishAt A.Z A.G = some pl) :
    ∀ k st m E T (J' : TestJob (LocB W₀) Unit),
      J' = atStand (jobL (H2U.p12OfMade A.Z.made) (doorAtL A.Z) (widerRows Sz.ref A.Z A.G)
        (readersB I A.Z) (K2.lotClosingAt A.G.first.layout (K2.segmentsOf A.Z A.G)) pl) m.st.input
        (frontOf m) T →
      ∀ c : RowCoins [(firstPart J' : Part (LocB W₀) (LocB W₀) Unit), restPart J'],
      ThrS (firstThreadAtTheFirstScript hh I Op numbers w) SaidOk 354 k st m E →
      enterFinish st = .ok T →
      lendRow A.B (A.B.rowsOf (firstThreadAtTheFirstScript hh I Op numbers w).chain)
        (k.look (firstThreadAtTheFirstScript hh I Op numbers w).chain) J'.p.place
        [(firstPart J' : Part (LocB W₀) (LocB W₀) Unit), restPart J'] 0 = .ok c →
      Agree J' m.st.input (frontOf m) J'.s₀ (firstRd J' c.1) (restCoins J' c.2.1) := by
  intro k st m E T J' hJ c _ _ hl
  subst hJ
  obtain ⟨a, u, rest, hs, hk⟩ := stages_L_shape
  have hst : (atStand (jobL (H2U.p12OfMade A.Z.made) (doorAtL A.Z) (widerRows Sz.ref A.Z A.G)
        (readersB I A.Z) (K2.lotClosingAt A.G.first.layout (K2.segmentsOf A.Z A.G)) pl) m.st.input
      (frontOf m) T).p.nums.stages = a :: u :: rest := by
    show (H2U.p12OfMade A.Z.made).nums.stages = _
    rw [Johnson.AtFull.Shape.p12_at_head hh.head.toAtMg]
    exact hs
  exact agree_at_L (H2U.p12OfMade A.Z.made) (widerRows Sz.ref A.Z A.G) (readersB I A.Z)
    (K2.lotClosingAt A.G.first.layout (K2.segmentsOf A.Z A.G)) pl _ rfl rfl rfl A.B _ _ c hl _ _
    (closingTestTies_at_base hh.head hA hf) (by rw [s₀_of_stages hst]; exact hk)

end ProofFile.Honest.K12.LotL

#print axioms ProofFile.Honest.K12.LotL.finishIsHanded_at_base
#print axioms ProofFile.Honest.K12.LotL.finishOwnTree_at_first_thread
#print axioms ProofFile.Honest.K12.LotL.says_at_first_thread
#print axioms ProofFile.Honest.K12.LotL.agree_at_first_thread
