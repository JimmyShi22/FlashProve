-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
AtFullSide/K12/PlaysAtTreesAtTheLastThread.lean

It states no goal. No property of the protocol is claimed.

AT A MEMBER OF THE PROOF FILE's LAST CHAIN WITH A NEW TREE THE SENDER PLAYS, AT THE LETTER WITHOUT THE TIE: the field
playsAtTrees₃ of ThreadFields (AtFullSide/Honest/ThreadsAtTheTerm.lean; as a proposition of its own:
`Socket.playsAtTrees₃`, AtFullSide/Honest/TheSocketStatements.lean), IN ITS OWN TEXT, at the base prover's return, from
five named premises on the last thread's parts. Two theorems; no definition.

  `playsS_at_the_last_chains_test`    `PlaysS` at number 2, at `lastThread h first reads parts w`, at any letter Said at
                                      which the clause on the field holds
  `playsAtTrees_at_the_last_thread`   the field's text, at `threadThree` and `saidThree`
                                      (AtFullSide/Honest/TheThreeThreads.lean), at the parts as a letter: a general form;
                                      PlaysAtTreesAtTheLetters.lean calls the first theorem, not this one

By what. Number 2 alone can have a new tree: `fresh_nil_off_the_test` (PlaysAtTreesFresh.lean). At number 2:
`playsS_at_W`, `enters_at_W` (K12/AtFile/WAccepted.lean); the letters of the test: `letter_at_filling`
(K12/AtFile/WFilling.lean); the old trees: `old_at_term`, the new trees: `trees_at_term` (K12/AtFile/WTable.lean); the
book: `book_laid` (AtFullSide/K12/LettersTwelve.lean); the clause on the field: `field_of_said_W`
(K12/AtFile/WField.lean): it asks that the letter gives `SaidField` at `BaseTied`, and `saidThree` is that, to the
letter: the tie that `saidThreeTied` adds is not read. `threadThree h first reads last R` is `lastThread h first reads last
R.own`.

Hypotheses. h: the head at a return of the maker. hA: that return is the base prover's filling's; at I := matrixInput,
S := Sz.ref, O := openHonest the filling is `matrixFilling` (E2E/ThruAtTerm.lean), and hA is the premise that the laws
on the three threads call made: whoever builds a value over h alone must hold it beside h. THE FIVE NAMED
PREMISES, each on the letter last, with the job M of the filling:
  takenIsWritten    last.taken = takenLast
  tableIsLaid       last.table = lastTable r₁ toCommon tb₁ tb₂ (ownLast M.toRun.toTest own₀ n₀)
  fixedIsLaid       last.fixed = lastFixed r₁ fx₁ fx₂ fun τ => n₀ + seedRound M.toRun.toTest.p.nums.stages τ
  roundsInFront     n₀ is the thread's count of rounds in front of the chain
  widths            `WidthsAt`: the three taken trees' tables have the widths 3, 12 and 36 at all coins, inputs and
                    challenges
They are five of the premises of `five_at_base_rest` (K12/AtFile/WBase.lean), in its letters; its `StandRest` and its
premise on the riders are not asked.

Limits.
- THE FIVE ARE PREMISES: none is shown here. The first three are equations on the letter last: a value of the last
  thread's parts meets them by how it is laid or not at all.
- `PlaysS` speaks of stands of the thread; that a stand is reached is not said: at no stand it says nothing.
- That h can be met together with hA is not shown here.
- At the base prover's filling's return, at its own type of random values: NOT AT THE ONLINE PROVER, whose filling
  reads this one through the coins' map.
- The full size and the format's second hash function alone. Of one member of one chain. Nothing on the chain.
- All limits of WAccepted.lean, WTable.lean, WFilling.lean and WField.lean hold here.
- Nothing on completeness of the chain, soundness or hiding.

NOT IN FRONT OF A LAW OVER COINS: both bear this label; the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean. The laws that they call bear it.
This file's own ground, in the rule's terms.
- h and hA speak of the public files, of the letters I, S and O and of what the maker returns at the filling made of
  them. By their text they name no coin, no run's input and no Script: of neither kind.
- The first four named premises are equations between letters: they name no coin. widths is itself bound over all
  coins: by itself it picks among no coins.
- w (in the second theorem R, whose field own is the run's input) is a letter under no premise in front. The input
  holds the committer's coins (its field rc) and the hidden input (its fields w₀ and trace). R is what `ready` returns
  at some coins; no premise here says so.
- In the second theorem the thread's parts, the field ends among them, are the letter last: under no premise but the
  first three named ones, which do not read ends.
- A run's coins k are bound inside the end, `PlaysS`. Beside k it binds the letters s, m and E (the verifier's state,
  the state of the prover's side, the available tables) under `ThrS … b k s m E`: a premise of the first kind: it names
  k; by its text, at fixed s, m and E it can hold at some values of the coins and fail at others. In the second
  theorem its letter is `saidThree`, which names k through `BaseTied`.
- `PlaysS` binds besides l under the return of `chainSteps … (k.look …) …`: of the first kind.
- ds, the challenges, stands under `drawsFit` (no coin) and under `chainStopAt (T.φ.sees m.st.input) …`: no run's coin is
  among its arguments (`Part.stopAt`, Honest/Side.lean), but in the second chain, as in the first, the face shows a
  part's second stop the whole input of m (`Face.sees`, Honest/Frame.lean), which holds rc and the hidden input: of the
  first kind as far as such a stop reads rc, of the second as far as it reads the index or the trace; what the parts at
  number 2 read is not fixed here. Where the field playsAtTrees₃ is spent (`saidNextThree`,
  AtFullSide/Honest/ThreadsAtTheTerm.lean) `chainStop_none` at `quiet_second_at_return` is called beside it for this premise:
  their statements are not read here.
- In the first theorem the premise on the field is itself bound over all coins and every stand: by itself it picks among
  no coins.
- One clause of the invariant, the thread's `valid`, has two halves. The first says that the input of m IS w (in the second
  theorem R.own): it compares the whole input, which holds rc: at a fixed m it holds at one value of the committer's coins
  and fails at the others: of the first kind: m is tied to rc as well as to k. The second says that this input meets
  `ReadyInput` (Honest/Thread/ReadyInput.lean): it reads the hidden input and no coin: of the second kind.
- What lifts the bar: for s, m, E and l the made terms would be those of the honest run at the border, as terms of the
  input, k and the challenges, and the lemma would show the premises at them at every value of the coins. For ds, which
  no term of the prover's makes, the lemma would show that at each ds `chainStopAt … = none` holds at every value of rc or
  at none. None is known to this file: the bar is flat.
-/
import AtFullSide.K12.PlaysAtTreesFresh
import AtFullSide.Honest.TheThreeThreads
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WTable
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WField

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K12
open ProofFile.Honest
open ProofFile.Honest.K12
open ProofFile.Honest.K12.AtFile
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.Third (S₃)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts IndexReaders LastThreadParts lastThread lastWitness)
open AtFullSide.Honest (threadThree saidThree)
open ToldDesc (ownAt)

variable {W₀ : Type}

/-- **`PlaysS` at the last chain's own test, at the base prover**, from the five named premises and the clause on the
field. -/
theorem playsS_at_the_last_chains_test {W₂ : Type} {files : VerifierAndGoals.PublicFiles}
    {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} (h : HeadAtReturn files A) (I : WiderIn W₀)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A) :
    ∃ M, jobAtFill A.Z h.places h.firstChain I S O A.G = some M ∧
      ∀ (first : FirstThreadParts A) (reads : IndexReaders W₀ IndexCommitterCoins) (parts : LastThreadParts A)
        (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
        (Said : ℕ → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
        (r₁ n₀ : ℕ) (toCommon : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → W₂)
        (tb₁ : Fmt.TreeSource → Coins A.B → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → List Fmt.Drawn →
          Place × Table)
        (tb₂ : Fmt.TreeSource → Coins A.B → W₂ → List Fmt.Drawn → Place × Table)
        (fx₁ fx₂ : Fmt.TreeSource → ℕ) (own₀ : Unit),
        parts.taken = takenLast →
        parts.table = lastTable r₁ toCommon tb₁ tb₂ (ownLast M.toRun.toTest own₀ n₀) →
        parts.fixed = lastFixed r₁ fx₁ fx₂ (fun τ => n₀ + seedRound M.toRun.toTest.p.nums.stages τ) →
        n₀ = (lastThread h first reads parts w).front →
        WidthsAt r₁ toCommon tb₁ tb₂ →
        FieldAtW h.description (lastThread h first reads parts w) Said 2 →
        PlaysS (lastThread h first reads parts w) Said 2 := by
  obtain ⟨M, hM, hp, ⟨f, hf⟩, hl, -, hR, hL⟩ :=
    letter_at_filling (Wt := ProofFile.Honest.FirstThread.WtF) h.head I S O hA
  refine ⟨M, hM, ?_⟩
  intro first reads parts w Said r₁ n₀ toCommon tb₁ tb₂ fx₁ fx₂ own₀ ht htb hfx hn hW hF
  have eT : lastThread h first reads parts w = lastAt (Zp := A.Z) (Np := h.places) (cF := h.firstChain) A.H h.sharedNumbers parts.meaning
      h.lastMeaning h.lastForm (fun s => OnBytes.Means.InOrder s.st) parts.ends (lastWitness h first reads) r₁ n₀
      toCommon tb₁ tb₂ fx₁ fx₂ M.toRun.toTest own₀ 0 h.description.t₁ h.description.t₂
      (ProofFile.Honest.ReadyInput h.description A.H) parts.rides
      (ProofFile.Honest.K14.kpSecond (ToldDesc.p14At A.Z) parts.keeps) w := by
    unfold lastThread
    rw [ht, htb, hfx]
  rw [eT] at hn hF ⊢
  have H₀ := hL h.sharedNumbers parts.meaning h.lastMeaning h.lastForm
    (fun s => OnBytes.Means.InOrder s.st) parts.ends (lastWitness h first reads)
    (lastTable r₁ toCommon tb₁ tb₂ (ownLast M.toRun.toTest own₀ n₀))
    (lastFixed r₁ fx₁ fx₂ fun τ => n₀ + seedRound M.toRun.toTest.p.nums.stages τ) 0 h.description.t₁
    h.description.t₂ (ProofFile.Honest.ReadyInput h.description A.H) parts.rides
    (ProofFile.Honest.K14.kpSecond (ToldDesc.p14At A.Z) parts.keeps) w
  have hfresh : M.fresh.isNone = false := by
    rw [hf]
    rfl
  refine playsS_at_W h.head.toAtMg H₀ hF (book_laid h.head hA) hp f hf hl ?_ ?_
  · intro k st m E u
    rw [hp]
    exact old_at_term A.H h.sharedNumbers parts.meaning h.lastMeaning h.lastForm
      (fun s => OnBytes.Means.InOrder s.st) parts.ends (lastWitness h first reads) r₁ n₀ toCommon tb₁ tb₂
      fx₁ fx₂ _ own₀ 0 h.description.t₁ h.description.t₂ (ProofFile.Honest.ReadyInput h.description A.H)
      parts.rides (ProofFile.Honest.K14.kpSecond (ToldDesc.p14At A.Z) parts.keeps) w h.head.toAtMg hW u.1
  · intro blk hb k st m E ds y cols u hd hMoved
    obtain rfl : blk = ((ownAt h.places).retype : Block S₃ ProofFile.Cl) :=
      Option.some.inj (hb.symm.trans H₀.member)
    exact trees_at_term A.H h.sharedNumbers parts.meaning h.lastMeaning h.lastForm
      (fun s => OnBytes.Means.InOrder s.st) parts.ends (lastWitness h first reads) r₁ n₀ toCommon tb₁ tb₂
      fx₁ fx₂ _ own₀ 0 h.description.t₁ h.description.t₂ (ProofFile.Honest.ReadyInput h.description A.H)
      parts.rides (ProofFile.Honest.K14.kpSecond (ToldDesc.p14At A.Z) parts.keeps) w h.head.toAtMg hn H₀.seat hp
      hfresh hR H₀.half H₀.member k st m E ds y cols u.1 (enters_at_W H₀ hF u).2 hd hMoved

/-- **At a member of the last chain with a new tree the sender plays, at the letter without the tie**: the text of the
field playsAtTrees₃, from the five named premises. -/
theorem playsAtTrees_at_the_last_thread {W₂ : Type} {files : VerifierAndGoals.PublicFiles}
    {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} (h : HeadAtReturn files A) (I : WiderIn W₀)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A) :
    ∃ M, jobAtFill A.Z h.places h.firstChain I S O A.G = some M ∧
      ∀ (first : FirstThreadParts A) (reads : IndexReaders W₀ IndexCommitterCoins) (last : LastThreadParts A)
        (R : Ready W₀ IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit)
        (r₁ n₀ : ℕ) (toCommon : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → W₂)
        (tb₁ : Fmt.TreeSource → Coins A.B → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → List Fmt.Drawn →
          Place × Table)
        (tb₂ : Fmt.TreeSource → Coins A.B → W₂ → List Fmt.Drawn → Place × Table)
        (fx₁ fx₂ : Fmt.TreeSource → ℕ) (own₀ : Unit)
        (_takenIsWritten : last.taken = takenLast)
        (_tableIsLaid : last.table = lastTable r₁ toCommon tb₁ tb₂ (ownLast M.toRun.toTest own₀ n₀))
        (_fixedIsLaid : last.fixed =
          lastFixed r₁ fx₁ fx₂ (fun τ => n₀ + seedRound M.toRun.toTest.p.nums.stages τ))
        (_roundsInFront : n₀ = (threadThree h first reads last R).front)
        (_widths : WidthsAt r₁ toCommon tb₁ tb₂),
        ∀ b, b < (threadThree h first reads last R).bs.length →
          (threadThree h first reads last R).fresh b ≠ [] →
          PlaysS (threadThree h first reads last R) (saidThree h first reads last R) b := by
  obtain ⟨M, hM, key⟩ := playsS_at_the_last_chains_test (W₂ := W₂) h I S O hA
  refine ⟨M, hM, ?_⟩
  intro first reads last R r₁ n₀ toCommon tb₁ tb₂ fx₁ fx₂ own₀ ht htb hfx hn hW b hb hne
  obtain rfl : b = 2 := by
    by_contra hc
    exact hne (fresh_nil_off_the_test OnBytes.secondHashFunction A.Z h.places h.firstChain _ rfl hb hc)
  exact key first reads last R.own _ r₁ n₀ toCommon tb₁ tb₂ fx₁ fx₂ own₀ ht htb hfx hn hW
    (field_of_said_W _ _ 2 fun _ _ hS => hS)

end AtFullSide.K12

#print axioms AtFullSide.K12.playsS_at_the_last_chains_test
#print axioms AtFullSide.K12.playsAtTrees_at_the_last_thread
