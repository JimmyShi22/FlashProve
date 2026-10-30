-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLAcceptedOne.lean

It states no goal. No property of the protocol is claimed.

`AcceptedS` AT THE FIRST CHAIN's CLOSING
PROXIMITY TEST (member 354), AT THE FIRST THREAD AS A VALUE LAID WITH THE FIRST CHAIN's SCRIPT AS A VALUE at
`Sz.ref`, at Said := `SaidOk`, FROM ONE NAMED PREMISE: the test `frontFiveB` on the shape of the record on
entry. No finish is named: there is one.

  `acceptedS_at_first_thread_of_five`           the premise at every stand of the thread
  `acceptedS_at_first_thread_of_five_reached`   the premise at every reached state, at the seated place's
                                                own numbers

By what. `acceptedS_at_first_thread_of_two`, `acceptedS_at_first_thread_of_reached` (LotLAcceptedPaid.lean);
`closingBookTest_at_base` (LotLBookClosing.lean); `finish_at_base` (AtFullSide/K1/FirstScript.lean).

Hypotheses. hh: the head at a return of the maker. hA: that return is the base prover's filling's at
`Sz.ref`. hfive | hfiveReached: as in LotLAcceptedPaid.lean.

Limits.
- hfive IS A PREMISE ON EVERY STAND (hfiveReached: on every reached state at which the way in returns): one
  at which it fails makes it false, and then nothing is said.
- `AcceptedS` speaks of stands of the thread; that a stand is reached is not said.
- That hh can be met together with hA is not shown here.
- The full size, the format's second hash function and `Sz.ref` alone.
- At the base prover's filling's return, at its own type of random values: NOT AT THE ONLINE PROVER, whose
  filling reads this one through the coins' map.
- Beneath this file lie K2/Law/ClosingAtHead.lean with the files beneath it, and LAcceptedOpens.lean
  with the L*.lean files.
- The statements at the maker's return are typed at `OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit`: they cannot
  even be written at the online prover's return (`OnlineProverWithDescription FullSizeMatrix (protocolAtFiles files).EncodingRandomness Cells Unit Unit`,
  E2E/TheHonestProver.lean): no law through `OnlineProverParts.through` is made here.
- Nothing on completeness of the chain, soundness or hiding.

NOT IN FRONT OF A LAW OVER COINS: both bear this label; the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean. The laws that they call bear it.
This file's own ground, in the rule's terms.
- hh and hA speak of the public files, of the letters I and Op (how an index, an instance and the
  challenges are read, and one named member of the index's type) and of what the maker returns at
  the filling made of them. By their text they name no coin, no run's input (its index, its trace)
  and no Script: of neither kind.
- hfive is itself bound over all coins and every stand, hfiveReached over every reached state (a
  reach names no coin): by themselves they pick among no coins.
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
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLAcceptedPaid
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLBookClosing

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K12.LotL
open VerifiableInference.Desc.K12 (T12 enterFinish)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.HonestTrace (Sz)
open H2K.Member (codesFull piLFull)
open ProofFile.Honest.Sh (testSh)
open ProofFile.Honest.FirstThread (HeadAtReturn FallNumbers)
open ProofFile.Honest.K1 (LocB finish_at_base)
open ProofFile.Honest.K12.AtProof (closingBookTest_at_base)

variable {W₀ : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- hfive IS A PREMISE. **The closing proximity test is accepted at the first thread.** -/
theorem acceptedS_at_first_thread_of_five (hh : HeadAtReturn files A) (I : WiderIn W₀) (Op : OnlineProverArguments)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref Op) = .ok A)
    (numbers : FallNumbers) (w : LocB W₀)
    (hfive : ∀ k st m E T, ThrS (firstThreadAtTheFirstScript hh I Op numbers w) SaidOk 354 k st m E →
      enterFinish st = .ok T → frontFiveB piLFull codesFull (testSh T) = true)
    (fl : ℕ → S → List Fmt.Drawn → Option String) :
    AcceptedS (firstThreadAtTheFirstScript hh I Op numbers w) SaidOk fl 354 := by
  obtain ⟨pl, hf⟩ := finish_at_base hh.head hA
  exact acceptedS_at_first_thread_of_two hh I Op hA numbers w hf
    (closingBookTest_at_base hh.head hA hf) hfive fl

/-- hfiveReached IS A PREMISE. **The same, with the test on the shape asked at every reached state.** -/
theorem acceptedS_at_first_thread_of_five_reached (hh : HeadAtReturn files A) (I : WiderIn W₀) (Op : OnlineProverArguments)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref Op) = .ok A)
    (numbers : FallNumbers) (w : LocB W₀)
    (hfiveReached : ∀ {p : ProofFile.InstPub} {s : S},
      Reach 0 (hh.firstChain.blocksInOrder.map below) (ProofFile.startS A.Z) 354 (p, s) →
      ∀ {t : T12}, enterFinish s = .ok t →
        frontFiveB (H2U.p12OfMade A.Z.made) codesFull (testSh t) = true)
    (fl : ℕ → S → List Fmt.Drawn → Option String) :
    AcceptedS (firstThreadAtTheFirstScript hh I Op numbers w) SaidOk fl 354 := by
  obtain ⟨pl, hf⟩ := finish_at_base hh.head hA
  exact acceptedS_at_first_thread_of_reached hh I Op hA numbers w hf
    (closingBookTest_at_base hh.head hA hf) hfiveReached fl

end ProofFile.Honest.K12.LotL

#print axioms ProofFile.Honest.K12.LotL.acceptedS_at_first_thread_of_five
#print axioms ProofFile.Honest.K12.LotL.acceptedS_at_first_thread_of_five_reached
