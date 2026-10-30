-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
AtFullSide/K12/PlaysAtTreesAtTheLetters.lean

It states no goal. No property of the protocol is claimed.

AT A MEMBER OF THE PROOF FILE's LAST CHAIN WITH A NEW TREE THE SENDER PLAYS, AT THE LETTERS AS DEFINITIONS
(AtFullSide/Honest/TheLettersLast.lean): at `thread₃ h P R`, AT THE LETTER WITHOUT THE TIE, `said₃Field`; and so at `said₃`,
which adds the tie. From one named premise, the three widths. Two theorems; no definition.

  `playsAtTrees_at_the_letters`        at `said₃Field`
  `playsAtTrees_at_the_letters_tied`   at `said₃`

By what. `playsS_at_the_last_chains_test` (PlaysAtTreesAtTheLastThread.lean), which stands at `lastThread` at any parts and
any letter Said with the clause on the field; `last_fresh` (AtFullSide/Honest/TheLettersFit.lean): members 0, 1 and 3 of
`thread₃` send no tree; `second_flat` (K12/AtFile/WLetter.lean): the chain has four members; `lastFront_is_front`
(TheLettersFit.lean): the count in front; `field_of_said_W` (K12/AtFile/WField.lean); `playsS_mono`
(Honest/Thread/SaidMono.lean). The job: the field ownIsTheFilling of `OpenLast` says that P.ownMany is the filling's job,
and `jobAtFill` is a function. `last h P` is `lastLettersOf` (K12/AtFile/WLaidDefs.lean) at that job and that count: the three
equations on the parts hold by unfolding.

Hypotheses. h: the head at a return of the maker. made: that return is the base prover's filling's, at matrixInput, Sz.ref
and openHonest. widths: `WidthsAt` (K12/AtFile/WTable.lean) at the first Script's table and the shared letters' table. P, a
value of `OpenLast`, holds two propositions of its own: ownIsTheFilling and depths. Two instances: `Inhabited P5J.TS`,
`Inhabited Desc.K14.St`: `endsAt`, the thread's field ends, is made by choice with a default.

Limits.
- widths IS A PREMISE HERE: PlaysAtTreesAtTheLettersWidthsShown.lean shows it.
- That there is a value of `OpenLast` is not shown here: it owes its field depths.
- `PlaysS` speaks of stands of the thread; that a stand is reached is not said: at no stand it says nothing.
- That h can be met together with made is not shown here.
- At the base prover's return, at its own type of random values: NOT AT THE ONLINE PROVER, whose filling reads this one
  through the coins' map.
- The full size and the format's second hash function alone. Of one member of one chain. Nothing on the chain.
- All limits of PlaysAtTreesAtTheLastThread.lean hold here.
- Nothing on completeness of the chain, soundness or hiding.

NOT IN FRONT OF A LAW OVER COINS: both bear this label; the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean. They inherit it from `playsS_at_the_last_chains_test`, which they call.
This file's own ground, in the rule's terms.
- h and made speak of the public files and of what the maker returns at a filling written out. By their text they name no
  coin, no run's input and no Script: of neither kind. widths is itself bound over all coins: by itself it picks among no
  coins; so is P's field depths; P's field ownIsTheFilling names no coin.
- O, P and R are letters under no other premise; O stands under P's field depths, which speaks of the shared letters' table.
  R's field own, the run's input, holds the committer's coins (rc) and the
  hidden input (w₀, trace); no premise says that R is what `ready` returns.
- The thread's field ends is `endsAt`: a function of the coins k and the input, made by choice from the two earlier
  threads: a term, no letter.
- A run's coins k are bound inside the end, `PlaysS`. Beside k it binds the letters s, m and E (the verifier's state, the
  state of the prover's side, the available tables) under `ThrS … b k s m E`: a premise of the first kind: it names k; by
  its text, at fixed s, m and E it can hold at some values of the coins and fail at others. Its letter names k through
  `BaseTied`, and in the second theorem through `TiedToEnds` as well.
- `PlaysS` binds besides l under the return of `chainSteps … (k.look …) …`: of the first kind.
- ds, the challenges, stands under `drawsFit` (no coin) and under `chainStopAt (T.φ.sees m.st.input) …`: no run's coin is
  among its arguments, but in the second chain the face shows a part's second stop the whole input of m: of the first kind
  as far as such a stop reads rc, of the second as far as it reads the index or the trace; what the parts at number 2 read
  is not fixed here. Where the field playsAtTrees₃ is spent (`saidNextThree`, AtFullSide/Honest/ThreadsAtTheTerm.lean)
  `chainStop_none` at `quiet_second_at_return` is called beside it for this premise: their statements are not read here.
- One clause of the invariant, the thread's `valid`, has two halves. The first says that the input of m IS R.own: it compares
  the whole input, which holds rc: at a fixed m it holds at one value of the committer's coins and fails at the others: of the
  first kind: m is tied to rc as well as to k. The second says that this input meets `ReadyInput`
  (Honest/Thread/ReadyInput.lean): it reads the hidden input and no coin: of the second kind.
- What lifts the bar: for s, m, E and l the made terms would be those of the honest run at the border, and the lemma would
  show the premises at them at every value of the coins; for ds the lemma would show that the stop's answer does not hang
  on rc. None is known to this file: the bar is flat.
-/
import AtFullSide.K12.PlaysAtTreesAtTheLastThread
import AtFullSide.Honest.TheLettersFit
import Johnson.Desc.ProofFile.Honest.Thread.SaidMono

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K12
open AtPublicFiles.AtFiles
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.K12
open ProofFile.Honest.K12.AtFile
open ProofFile.Honest.Term (matrixInput)
open OnBytes (TableKey)
open AtFullSide.Honest.TheLetters

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]
variable {Z : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- **At a member of the last chain with a new tree the sender plays, at the letters as definitions, at the letter without
the tie.** -/
theorem playsAtTrees_at_the_letters (h : HeadAtReturn Z A)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest) = .ok A)
    (O : OpenShared A) (P : OpenLast h O) (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit)
    (widths : WidthsAt (firstRounds h) (toCommon (A := A)) (first h).script.table
      (later (h := h) O).table) :
    ∀ b, b < (thread₃ h P R).bs.length → (thread₃ h P R).fresh b ≠ [] →
      PlaysS (thread₃ h P R) (said₃Field h P R) b := by
  obtain ⟨M, hM, key⟩ := playsS_at_the_last_chains_test (W₂ := Common FullSizeMatrix IndexCommitterCoins TableKey) h matrixInput
    OnBytes.HonestTrace.Sz.ref openHonest made
  obtain rfl : M = P.ownMany := Option.some.inj (hM.symm.trans P.ownIsTheFilling)
  intro b hb hne
  obtain ⟨f0, f1, f3⟩ := last_fresh h P R
  have hl : (thread₃ h P R).bs.length = 4 := by
    show (P5J.F0T OnBytes.secondHashFunction A.Z h.places h.firstChain).second.blocksInOrder.length = 4
    rw [second_flat]
    rfl
  rw [hl] at hb
  obtain rfl : b = 2 := by
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl
    · exact absurd f0 hne
    · exact absurd f1 hne
    · rfl
    · exact absurd f3 hne
  exact key (first h) (reads h) (lastParts h (first h) (last h P)) R.own _ (firstRounds h) (lastFront h)
    (toCommon (A := A)) (first h).script.table (later (h := h) O).table (first h).script.fixed
    (later (h := h) O).fixed () rfl rfl rfl (lastFront_is_front h P R) widths
    (field_of_said_W _ _ 2 fun _ _ hS => hS)

/-- **The same at `said₃`**, the letter with the tie. -/
theorem playsAtTrees_at_the_letters_tied (h : HeadAtReturn Z A)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest) = .ok A)
    (O : OpenShared A) (P : OpenLast h O) (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit)
    (widths : WidthsAt (firstRounds h) (toCommon (A := A)) (first h).script.table
      (later (h := h) O).table) :
    ∀ b, b < (thread₃ h P R).bs.length → (thread₃ h P R).fresh b ≠ [] →
      PlaysS (thread₃ h P R) (said₃ h P R) b :=
  fun b hb hne => playsS_mono _ (fun _ _ _ hS => hS.1)
    (playsAtTrees_at_the_letters h made O P R widths b hb hne)

end AtFullSide.K12

#print axioms AtFullSide.K12.playsAtTrees_at_the_letters
#print axioms AtFullSide.K12.playsAtTrees_at_the_letters_tied
