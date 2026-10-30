-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLAcceptedPaid.lean

It states no goal. No property of the protocol is claimed.

THE TWO ENDS OF THE FIRST CHAIN's CLOSING
PROXIMITY TEST (member 354) THAT SPEAK OF WHAT THE PROVER SAYS, AT THE FIRST THREAD AS A VALUE LAID WITH THE
FIRST CHAIN's SCRIPT AS A VALUE at `Sz.ref`, at Said := `SaidOk`: `PlaysS` outright, and `AcceptedS` with the
side at the test's place paid.

  `playsS_at_first_thread`             `PlaysS` at 354: no premise but hh and hA
  `acceptedS_at_first_thread_of_two`   `AcceptedS` at 354: left: hbook and hfive
  `acceptedS_at_first_thread_of_reached`   the same, with hfive asked at every REACHED state at which the
                                       way in returns, at the seated place's own numbers

By what. `closingTestPlays_at_firstThread_paid`, `closingTestSide_at_base` (LotLSeatPlaysPaid.lean);
`playsS_of` (Honest/Thread/PaysS.lean); `acceptedS_at_first_thread` (LotLAccepted.lean); `thrS_reach_below`
(Honest/Thread/ReachAtHead.lean), `p12_at_head` (Johnson/AtFull/Shape/TestNumbersAtHead.lean).

Hypotheses. hh: the head at a return of the maker. hA: that return is the base prover's filling's at
`Sz.ref`. The second also: hf: pl is the finish; hbook: the public test `closingBookTest` (LOpensBook.lean)
says yes at the maker's book; hfive: AT EVERY STAND at which the way in returns T the test
`frontFiveB` on T's shape says yes. The third: hfiveReached: the same test at every state that is reached at
border 354 by the wrapped members' steps and at which the way in returns: a wider range than hfive's. IT IS
STATED IN THE FORM OF THE CONCLUSION OF `frontFive_at_L` (at the stored files `VerifierAndGoals.storedPublicFiles`
alone; not held here). No law in these files concludes it: they give the test at
stands, which is hfive's form.

Limits.
- hfive IS A PREMISE ON EVERY STAND: one stand at which it fails makes it false, and then nothing is said.
- All three speak of stands of the thread; that a stand is reached is not said.
- That hh can be met together with hA is not shown here.
- The full size, the format's second hash function and `Sz.ref` alone.
- The rows beneath are heavy: AtFullSide/K12/StatedAtHeadW.lean and the files on the closing.
- At the base prover's filling's return, at its own type of random values: NOT AT THE ONLINE PROVER, whose
  filling reads this one through the coins' map.
- Beneath this file lie K2/Law/ClosingAtHead.lean with the files beneath it, and LAcceptedOpens.lean
  with the L*.lean files.
- The statements at the maker's return are typed at `OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit`: they cannot
  even be written at the online prover's return (`OnlineProverWithDescription FullSizeMatrix (protocolAtFiles files).EncodingRandomness Cells Unit Unit`,
  E2E/TheHonestProver.lean): no law through `OnlineProverParts.through` is made here.
- Nothing on completeness of the chain, soundness or hiding.

NOT IN FRONT OF A LAW OVER COINS: all three bear this label; the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean. The laws that they call bear it.
This file's own ground, in the rule's terms.
- hh and hA speak of the public files, of the letters I and Op (how an index, an instance and the
  challenges are read, and one named member of the index's type) and of what the maker returns at
  the filling made of them. By their text they name no coin, no run's input (its index, its trace)
  and no Script: of neither kind.
- hf and hbook speak of the finish and of the book's entries: they name no coin.
- hfive is itself bound over all coins and every stand, hfiveReached over every reached state (a
  reach names no coin): by themselves they pick among no coins.
- w, the run's input, is a letter under no premise in front. It holds the committer's coins (its
  field rc) and the hidden input (its fields w₀ and trace).
- numbers (the stated numbers of the falls) and fl (the fall, which stands inside `AcceptedS`) are
  letters under no premise.
- A run's coins k are bound inside the ends, `PlaysS` and `AcceptedS`. Beside k they bind the
  letters s, m and E (the verifier's state, the state of the prover's side, the available tables)
  under `ThrS … 354 k s m E`: a premise of the first kind: it names k; by its text, at fixed s, m
  and E it can hold at some values of the coins and fail at others.
- `Plays` | `PlaysS` binds besides l under `chainSteps … (k.look T.chain) … = .ok l`: of the first
  kind.
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
- What lifts the bar: for s, m, E, l, y and cols the made terms would be those of the honest run at
  the border, as terms of w, k and the challenges, and the lemma would show the premises at them at
  every value of the coins. For ds, which no term of the prover's makes, the lemma would show that
  at each ds `chainStopAt … = none` holds at every value of rc or at none. None is known to this
  file: the bar is flat.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLAccepted
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLSeatPlaysPaid
import Johnson.Desc.ProofFile.Honest.Thread.PaysS

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K12.LotL
open VerifiableInference.Desc.K12 (T12 enterFinish)
open VerifiableInference.Desc.First (S)
open OnBytes.HonestTrace (Sz)
open H2K.Member (codesFull piLFull)
open ProofFile.Honest.Sh (testSh)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile.Honest.FirstThread (HeadAtReturn FallNumbers thrS_reach_below flat_length_head)
open ProofFile.Honest.K1 (LocB)
open ProofFile.Honest.K2 (SwitchPlace)
open ProofFile.Honest.K12.AtProof (finishAt closingBookTest)

variable {W₀ : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- **The closing proximity test plays at the first thread.** -/
theorem playsS_at_first_thread (hh : HeadAtReturn files A) (I : WiderIn W₀) (Op : OnlineProverArguments)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref Op) = .ok A)
    (numbers : FallNumbers) (w : LocB W₀) :
    PlaysS (firstThreadAtTheFirstScript hh I Op numbers w) SaidOk 354 :=
  playsS_of _ _ (closingTestPlays_at_firstThread_paid hh hA numbers w)

/-- hbook AND hfive ARE PREMISES. **The closing proximity test is accepted at the first thread.** -/
theorem acceptedS_at_first_thread_of_two (hh : HeadAtReturn files A) (I : WiderIn W₀) (Op : OnlineProverArguments)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref Op) = .ok A)
    (numbers : FallNumbers) (w : LocB W₀) {pl : SwitchPlace} (hf : finishAt A.Z A.G = some pl)
    (hbook : closingBookTest A.B pl ⟨(H2U.p12OfMade A.Z.made).place, 1⟩ = true)
    (hfive : ∀ k st m E T, ThrS (firstThreadAtTheFirstScript hh I Op numbers w) SaidOk 354 k st m E →
      enterFinish st = .ok T → frontFiveB piLFull codesFull (testSh T) = true)
    (fl : ℕ → S → List Fmt.Drawn → Option String) :
    AcceptedS (firstThreadAtTheFirstScript hh I Op numbers w) SaidOk fl 354 :=
  acceptedS_at_first_thread hh I Op hA numbers w hf (closingTestSide_at_base hh.head hA hf) hbook hfive
    fl

/-- hbook AND hfiveReached ARE PREMISES. **The same, with the test on the shape asked at every reached
state.** -/
theorem acceptedS_at_first_thread_of_reached (hh : HeadAtReturn files A) (I : WiderIn W₀) (Op : OnlineProverArguments)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref Op) = .ok A)
    (numbers : FallNumbers) (w : LocB W₀) {pl : SwitchPlace} (hf : finishAt A.Z A.G = some pl)
    (hbook : closingBookTest A.B pl ⟨(H2U.p12OfMade A.Z.made).place, 1⟩ = true)
    (hfiveReached : ∀ {p : ProofFile.InstPub} {s : S},
      Reach 0 (hh.firstChain.blocksInOrder.map below) (ProofFile.startS A.Z) 354 (p, s) →
      ∀ {t : T12}, enterFinish s = .ok t →
        frontFiveB (H2U.p12OfMade A.Z.made) codesFull (testSh t) = true)
    (fl : ℕ → S → List Fmt.Drawn → Option String) :
    AcceptedS (firstThreadAtTheFirstScript hh I Op numbers w) SaidOk fl 354 :=
  acceptedS_at_first_thread_of_two hh I Op hA numbers w hf hbook
    (fun k st m E T hT he => by
      rw [← Johnson.AtFull.Shape.p12_at_head hh.head.toAtMg]
      exact hfiveReached (thrS_reach_below hh.head A.H _ _ _ _ _ _ _ _ _ _ w
        (by rw [flat_length_head hh.head]; decide) hT) he) fl

end ProofFile.Honest.K12.LotL

#print axioms ProofFile.Honest.K12.LotL.playsS_at_first_thread
#print axioms ProofFile.Honest.K12.LotL.acceptedS_at_first_thread_of_two
#print axioms ProofFile.Honest.K12.LotL.acceptedS_at_first_thread_of_reached
