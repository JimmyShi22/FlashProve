-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLAcceptedWhole.lean

It states no goal. No property of the protocol is claimed.

`AcceptedS` AT THE FIRST CHAIN's CLOSING
PROXIMITY TEST (member 354), AT THE FIRST THREAD AS A VALUE (`firstThread`, Honest/Thread/TheFirstThread.lean)
LAID WITH THE FIRST CHAIN's SCRIPT AS A VALUE (`firstScriptAt`, AtFullSide/K1/FirstScript.lean) at `Sz.ref`, at
Said := `SaidOk`: NO PREMISE BUT THE HEAD AT A RETURN OF THE MAKER AND THAT RETURN. One call.

  `firstShapeTest_at_first_thread`   hfive: at every stand at which the way in returns T, the test
                                     `frontFiveB` on T's shape says yes
  `acceptedS_at_first_thread_whole`  the end

By what. `acceptedS_at_first_thread_of_five` (LotLAcceptedOne.lean); `closingRecordLaid_at_every_stand`
(LotLShapeHeadTop.lean), `firstShapeTest_of_closingRecordLaid` (LotLShapeBoolsStand.lean).

Hypotheses. hh: the head at a return of the maker. hA: that return is the base prover's filling's at
`Sz.ref`.

Limits.
- `AcceptedS` speaks of stands of the thread; that a stand is reached is not said: at no stand it says
  nothing.
- That hh can be met together with hA is not shown here.
- At Said := `SaidOk` alone. The full size, the format's second hash function and `Sz.ref` alone.
- It says that where the prover's side has moved and no fall or stop is met, the verifier's member steps:
  of one member of one chain. Nothing on the chain.
- All limits of LAcceptedOpens.lean hold here.
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
- w, the run's input, is a letter under no premise in front. It holds the committer's coins (its
  field rc) and the hidden input (its fields w₀ and trace).
- numbers (the stated numbers of the falls) and fl (the fall, which stands inside `AcceptedS`) are
  letters under no premise.
- A run's coins k are bound inside each end. Beside k it binds the letters st | s, m and E (the
  verifier's state, the state of the prover's side, the available tables) under `ThrS … 354 k st m
  E`: a premise of the first kind: it names k; by its text, at fixed st, m and E it can hold at some
  values of the coins and fail at others. In `firstShapeTest_at_first_thread` the record T under
  `enterFinish st = .ok T` names no coin.
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
- What lifts the bar: for the state, m, E, y and cols the made terms would be those of the honest
  run at the border, as terms of w, k and the challenges, and the lemma would show the premises at
  them at every value of the coins. For ds, which no term of the prover's makes, the lemma would
  show that at each ds `chainStopAt … = none` holds at every value of rc or at none. None is known
  to this file: the bar is flat.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLAcceptedOne
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLShapeHeadTop

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K12.LotL
open VerifiableInference.Desc.K12 (T12 enterFinish)
open VerifiableInference.Desc.First (S)
open OnBytes.HonestTrace (Sz)
open H2K.Member (codesFull piLFull)
open ProofFile.Honest.Sh (testSh)
open ProofFile.Honest.FirstThread (HeadAtReturn FallNumbers)
open ProofFile.Honest.K1 (LocB)

variable {W₀ : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- **hfive: at every stand of the first thread in front of the test, the test on the shape of the record
on entry says yes.** -/
theorem firstShapeTest_at_first_thread (hh : HeadAtReturn files A) (I : WiderIn W₀) (Op : OnlineProverArguments)
    (numbers : FallNumbers) (w : LocB W₀) :
    ∀ k st m E T, ThrS (firstThreadAtTheFirstScript hh I Op numbers w) SaidOk 354 k st m E →
      enterFinish st = .ok T → frontFiveB piLFull codesFull (testSh T) = true :=
  fun k st m E T hT he => firstShapeTest_of_closingRecordLaid
    (closingRecordLaid_at_every_stand hh.head A.H _ _ _ _ _ _ _ _ _ _ w SaidOk k st m E T hT he)

/-- **The closing proximity test is accepted at the first thread.** -/
theorem acceptedS_at_first_thread_whole (hh : HeadAtReturn files A) (I : WiderIn W₀) (Op : OnlineProverArguments)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref Op) = .ok A)
    (numbers : FallNumbers) (w : LocB W₀)
    (fl : ℕ → S → List Fmt.Drawn → Option String) :
    AcceptedS (firstThreadAtTheFirstScript hh I Op numbers w) SaidOk fl 354 :=
  acceptedS_at_first_thread_of_five hh I Op hA numbers w
    (firstShapeTest_at_first_thread hh I Op numbers w) fl

end ProofFile.Honest.K12.LotL

#print axioms ProofFile.Honest.K12.LotL.firstShapeTest_at_first_thread
#print axioms ProofFile.Honest.K12.LotL.acceptedS_at_first_thread_whole
