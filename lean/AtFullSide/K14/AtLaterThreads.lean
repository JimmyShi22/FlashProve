-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K14/AtLaterThreads.lean: the linear claim (kind K14): THE STRUCTURE FiveAtBorder
(Johnson/Desc/ProofFile/Honest/Thread/FiveAtBorder.lean) AT THE TWO LATER CHAINS' THREADS WITH THEIR
FIELDS AT THE VALUES sharedParts AND lastParts (Honest/Thread/TheLaterThreads.lean): at the members
1 to 8 of the shared chain, and at the member 0 of the last chain.

  five_at_sharedParts **at the members 1 to 8 of the shared chain**, at the maker's return at the
                      filling onlineProverPartsInUse, at the committer's made input:
                      five_at_sharedThread_made (AtFullSide/K14/FiveAtSharedThread.lean)
  pin_lastParts, pin₁_lastParts   at lastParts' meaning a pin that holds at some strings holds at
                      all: a shared message's pin reads no string (pin_at_reads); the first chain's
                      pin reads nothing of the strings either (ansJT_rows, Honest/Thread/Ans.lean).
                      These two are the premises hPin and hPin₁ of five_at_lastThread_door
                      (Honest/K14/FiveAtLastThread.lean) at that value

  five_at_lastParts   **at the member 0 of the last chain**, at any filling: five_at_lastThread_laid
                      (Honest/K14/FiveAtLastThreadLaid.lean): lastParts lays the item ev as evAll
                      and the item dot as dotI, so that theorem's two layings hold by unfolding, and
                      its two premises on the pins are the two facts above. It stands under h
                      (HeadAtReturn: the library's hypothesis at the full size, at the format's
                      second hash function)

WHAT STAYS A PREMISE. Of five_at_sharedParts, on the letters that sharedParts leaves open
(LaterLetters): htab: table is tableShared at the filling's two readers; h0, h1: fixed is 1 at own
0, and 4 at own 1 and 2; late: every rider begins at border 10 or later: the chain has one list of
riders, so nothing rides at the borders 0 to 9, nor in front of the member 9. Of five_at_lastParts:
late: every rider that LastLetters holds begins at border 2 or later; so no fact that is shown where
the chain is entered and read by a later member can ride there.

TWO LIMITS AT THE LAST CHAIN (Honest/K14/SecondFour.lean's head has them at length). (1) NEITHER
THIS FILE NOR ANY FILE THAT IT IMPORTS SHOWS THE INVARIANT AT BORDER 0, from which each of the five
starts. It holds five items (the pins
of the index masks' message, of W and of Omega; ev; dot), of which ExchangeS takes ev and dot; the
form, which is fillZ's test; the order; the trees taken over; that the input is valid; and the rider
at border 0, from which AcceptedS takes secondDoor's tests. All of it is owed where the chain is
entered. Of the rider, second_door_at_terms (AtFullSide/K14/DoorAtTerms.lean) has the sentence from
the two earlier threads' ends; of fillZ's test, first_door_at_end
(AtFullSide/K14/FirstDoorAtEnd.lean) has eight of its clauses. (2) BehindS AND ExchangeS HOLD
VACUOUSLY WHEREVER fillZ's TEST AT BORDER 0 IS FALSE, and neither this file nor any file that it
imports evaluates that test at a state.

NOT IN FRONT OF A LAW OVER COINS (the rule: Johnson/Bind/ForProver/FiveFieldsAt.lean's head), of
five_at_sharedParts. The ground: the tie of the key to the coins (the first kind) is lifted: the key
is the term oodSh that the committer makes, by validAt_made. But the seed sd is a letter beside the
coins, and the thread's invariant, from which each of the five starts, is a premise on the letters
that are left: L's rest, keeps and riders, the two test jobs JU and JO in its table, and `Said`:
each may read the coins, and no lemma here shows the invariant at every value of the coins: the bar
is flat. "The index is in range" is of the second kind: it reads the hidden index and no coin.

What is not claimed. That any premise holds. That either thread's invariant holds at any state. That
a run's explicit input is the library's xiAt. Nothing on completeness, soundness or hiding.
Terms. letter, border: lean/GLOSSARY.md. A thread is the invariant along a chain with its parameters
(Honest/Thread/Thr.lean). A member is a sub-protocol of a chain's flat list, numbered from 0.
-/
import AtFullSide.K14.FiveAtSharedThread
import Johnson.Desc.ProofFile.Honest.K14.FiveAtLastThreadLaid
import Johnson.Desc.ProofFile.Honest.Thread.TheLaterThreads
import Johnson.Desc.ProofFile.Honest.Thread.Ans

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K14
open OnBytes (TableKey)
open ProofFile (SecondHashFunctionArgument)
open ProofFile.Honest ProofFile.Honest.K14
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts IndexReaders LaterLetters LastLetters
  sharedThread lastThread sharedParts lastParts)
open ProofFile.Honest.K12 (TestJob)
open ProofFile.Honest.K12.AtFile (tableShared)
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.Third (S₃)
open Bind.ForProver (shapeOf)
open Desc.K14 (St)

/-- **FiveAtBorder at a member b, 1 ≤ b ≤ 8, of the shared chain's thread at sharedParts**, at the
committer's made input: at every index w₀, all coins rc, every seed sd and all bytes of the request.
htab: table is tableShared at the filling's readers. h0, h1: fixed is 1 at own 0, and 4 at own 1 and
2. late: every rider begins at border 10 or later.
NOT IN FRONT OF A LAW OVER COINS (the file's head). -/
theorem five_at_sharedParts {files : VerifierAndGoals.PublicFiles} {W₀ : Type} (I : WiderIn W₀) (o' : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL (onlineProverPartsInUse I o' S O) = .ok A)
    (h : HeadAtReturn files A) (L : LaterLetters A) (w₀ : W₀) (rc : IndexCommitterCoins)
    (sd : Bind.ForProver.Seed (shapeOf A.Z) × ℕ) (bytes : ByteArray × ByteArray)
    {JU JO : TestJob (Common W₀ IndexCommitterCoins TableKey) Unit}
    (htab : L.table =
      tableShared (qAt A.Z h.places) (I.weights A.Z) (randNow (qAt A.Z h.places)) JU JO ())
    (h0 : L.fixed (.own 0) = 1) (h1 : ∀ i, i < 2 → L.fixed (.own (1 + i)) = 4)
    (late : ∀ c ∈ L.riders, 10 ≤ c.lo)
    (Said : Nat → Coins A.B → Mid (Common W₀ IndexCommitterCoins TableKey) Unit → Prop)
    (fall : Nat → St → List Fmt.Drawn → Option String) (b : Nat) (hb1 : 1 ≤ b) (hb8 : b ≤ 8) :
    FiveAtBorder (sharedThread h ⟨I.weights A.Z, randNow (qAt A.Z h.places)⟩ (sharedParts h L)
      ⟨w₀, rc, A.H.key (Bind.ForProver.xiAt (shapeOf A.Z) A.Z ⟨I.weights A.Z w₀, rc, sd⟩ bytes)⟩)
      Said fall b :=
  five_at_sharedThread_made I o' S O hA h (sharedParts h L) w₀ rc sd bytes htab h0 h1
    (cs := L.riders) (fun _ _ _ => Iff.rfl) late Said fall b hb1 hb8

section last
variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
  (h : HeadAtReturn files A) (first : FirstThreadParts A) (L : LastLetters A)

/-- At lastParts' meaning a shared message's pin that holds at some strings holds at all. -/
theorem pin_lastParts (inp : Local W₀ Rc ProofFile.Inst Tr) (a b : Nat) (e : St) (y y' : Strs)
    (v : FirstThread.WtF) (hp : ((lastParts h first L).meaning inp).pin a b e y v) :
    ((lastParts h first L).meaning inp).pin a b e y' v := hp

/-- At lastParts' meaning a pin of the first chain that holds at some strings holds at all. -/
theorem pin₁_lastParts (inp : Local W₀ Rc ProofFile.Inst Tr) (a b : Nat) (q : ProofFile.InstPub × P5J.TS)
    (y y' : Strs) (v : FirstThread.WtF)
    (hp : ((lastParts h first L).meaning inp).pin₁ a b q y v) :
    ((lastParts h first L).meaning inp).pin₁ a b q y' v :=
  ansJT_rows (P5J.At.cs A.Z) (P5J.At.arr A.Z) (seats := P5J.At.seats A.Z) (p := q.1) (p' := q.1)
    (s := q.2) (s' := q.2) (y := y) (y' := y') (fun _ _ _ => rfl) hp

/-- **FiveAtBorder at the member 0 of the last chain's thread at lastParts.** BehindS and ExchangeS
hold vacuously wherever fillZ's test at border 0 is false; ExchangeS takes the items ev and dot, and
AcceptedS secondDoor's tests, from the invariant in front. late: every rider that L holds begins at
border 2 or later. -/
theorem five_at_lastParts (reads : IndexReaders W₀ Rc) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (fall : Nat → S₃ → List Fmt.Drawn → Option String) (late : ∀ c ∈ L.riders, 2 ≤ c.lo) :
    FiveAtBorder (lastThread h first reads (lastParts h first L) w) Said fall 0 :=
  five_at_lastThread_laid h first reads (lastParts h first L) w Said fall (fun _ => rfl)
    (fun _ => rfl)
    (fun inp a b q _ _ v hp => pin₁_lastParts h first L inp a b q _ _ v hp)
    (fun inp a b e _ _ v hp => pin_lastParts h first L inp a b e _ _ v hp)
    (cs := L.riders) (fun _ _ _ => Iff.rfl) late

end last

end AtFullSide.K14

#print axioms AtFullSide.K14.five_at_sharedParts
#print axioms AtFullSide.K14.pin_lastParts
#print axioms AtFullSide.K14.pin₁_lastParts
#print axioms AtFullSide.K14.five_at_lastParts
