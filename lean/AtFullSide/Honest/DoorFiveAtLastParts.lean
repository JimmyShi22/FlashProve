-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/DoorFiveAtLastParts.lean: THE FIVE ITEMS WITH WHICH THE LAST CHAIN's THREAD BEGINS
HOLD AT THE DOOR: at a run's three threads (`threadOne`, `threadTwo`, `threadThree`,
AtFullSide/Honest/TheThreeThreads.lean), where the last thread's parts are `lastParts`
(Johnson/Desc/ProofFile/Honest/Thread/TheLaterThreads.lean): wherever the first and the shared
thread's invariants hold at their chains' ends, each item of `startLast`
(Johnson/Desc/Last/BordersLast.lean: the index masks' pin, W's pin, (Eval), (Dot), Omega's pin)
holds of the last chain's witness, at the two chains' last states. Statements with their proofs; no
definition.

Main names.
  `five_at_the_threads`: the five at the threads at an input w, under R, hx, hwt (what (Dot) asks of
    the sending of the message W: see AtFullSide/K14/DotAtLastParts.lean).
  `seated_w_at_firstScript`: R at the first chain's Script at the base prover (`firstScriptAt`,
    AtFullSide/K1/FirstScript.lean), from the maker's return and the head at the return.
  `door_five_at_run`: **the five at a run's two earlier threads, in the meaning of `lastParts`, at
    every strings**: from the maker's return at the filling `onlineProverPartsInUse`, the head at the
    return, `ready`'s return (hR), hQ (the parts' Script is `firstScriptAt`), hO (the pile's
    filler), hrw (the readers' reader of the index is the filling's).
  `door_five_at_lastParts`: the same in the letters in which the threads' debts at a run are
    gathered: at the last thread at `lastParts`.
  `door_items_at_lastParts`: the library's law on the door's items (`items_at_letters`,
    AtFullSide/K13/DoorAtLetters.lean) with its premise on the five paid by that statement: the
    items that are open at the last thread's first border hold at the stand with which the thread
    begins. Its four other premises (on what is available and on depths along the two earlier walks)
    stay.

From where each item comes. The two pins of the first chain and Omega's pin:
AtFullSide/K14/PinsAtLastParts.lean. (Eval): AtFullSide/K13/EvAtLastParts.lean. (Dot):
AtFullSide/K14/DotAtLastParts.lean; that law carries a letter, a string of some frame, of which
nothing is read: it is laid here at the frame without a tree.

Limits. NOT IN FRONT OF A LAW OVER COINS: the statements speak of one run's values, at one run's
coins. Conditional on the two invariants at their chains' ends, which hold four of the five
sentences among their clauses; these are moved to the last chain's witness, and no debt on them is
paid; (Dot) is made of what the two hold. That the invariants hold at any run is not shown here. At
`lastParts` alone. The full size, and the hash function `OnBytes.secondHashFunction`, alone.

What is not claimed. None of these is one of the library's goals. Nothing on soundness, completeness
or hiding.
-/
import AtFullSide.Honest.TheThreeThreads
import AtFullSide.K1.FirstScript
import AtFullSide.K13.EvAtLastParts
import AtFullSide.K14.DotAtLastParts
import AtFullSide.K14.PinsAtLastParts
import AtFullSide.K13.DoorAtLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.Honest
open OnBytes
open ProofFile ProofFile.Honest ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Strs Block)
open VerifiableInference.Desc.Sound (Mem)
open VerifiableInference.Desc.Last (ItemL startLast)
open VerifiableInference.Desc.K13.Law (wMsgFull)
open VerifiableInference.Desc.Third (S₃)
open Desc.K14 (St)
open P5J (TS)
open ProofFile.Honest.K1 (K1Seated PlaceIn firstScriptAt k1Seated_first jobWAt witB)
open ProofFile.Honest.K13 (pileAnyK3 wDataAt)

/-- R, hx and hwt are premises. **The five items of the last chain's start, at the threads at an
input w.** -/
theorem five_at_the_threads {W₀ Rc Tr X₀ X' Wt₂ : Type} {files : VerifierAndGoals.PublicFiles}
    {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'} (hd : HeadAtReturn files A) (first₁ : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (parts : SharedThreadParts A Wt₂) (L : LastLetters A)
    (w : Local W₀ Rc ProofFile.Inst Tr)
    {first : ℕ} {blk₆ : Block TS ProofFile.Cl} {wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst}
    {own₀ : X'} {seats₀ : List (ℕ × ℕ)} {ms : List Mem} {rad : ℕ → ℕ}
    (R : K1Seated (firstLetters hd first₁ w) 356 blk₆ wit
      (K1.wJobAt A.Z.first (K1.wGp A.Z) 4 wMsgFull first (wDataAt pileAnyK3 A.Z A.G)) own₀ .w
      (P5J.At.arr A.Z) seats₀ ms rad)
    (hx : (wit w).x = w.x) (hwt : (wit w).R.weights = reads.weights w.w₀)
    {k : Coins A.B} {e₁ : TS} {m₁ : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E₁ : Env}
    {e₂ : St} {m₂ : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E₂ : Env}
    (u₁ : Thr (firstThread hd first₁ w) hd.description.first.blocksInOrder.length k e₁ m₁ E₁)
    (u₂ : Thr (sharedThread hd reads parts ⟨w.w₀, w.rc, A.H.key w.x⟩)
      hd.description.shared.blocksInOrder.length k e₂ m₂ E₂) (s₃ : S₃) (ds : List Fmt.Drawn) (y : Strs) :
    ∀ i ∈ startLast, ItemL.holds hd.sharedNumbers ((lastParts hd first₁ L).meaning w)
      hd.lastMeaning i (w.x.pub, e₁) e₂ s₃ y
      (lastWitness hd first₁ reads k w (m₁.st.heard ++ m₂.st.heard ++ ds)) := by
  have e358 : hd.description.first.blocksInOrder.length = 358 := AtFullSide.K13.len358 hd.head
  obtain ⟨pI, pV⟩ := AtFullSide.K14.pins_first_at_lastParts hd first₁ reads L w u₁ m₂.st.heard ds y
  intro i hi
  simp only [startLast, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · exact pI
  · exact pV
  · exact AtFullSide.K13.ev_at_lastParts hd first₁ reads L w u₁ m₂.st.heard ds w.x.pub y
  · exact AtFullSide.K14.dot_at_lastParts hd first₁ reads parts L w (F := ⟨0, [], id, 0⟩)
      (VerifiableInference.Desc.Sound.tabBack 0 fun _ => none, fun _ => []) R hx hwt (e358 ▸ u₁) u₂
      ds y
  · exact AtFullSide.K14.pinO_at_lastParts hd first₁ reads parts L w u₁ u₂ ds y

variable {W₀ : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {I : WiderIn W₀}
  {S : OnBytes.HonestTrace.Sz} {Op : OnlineProverArguments}

/-- hQ and hO are premises. **The sending of the message W is seated at number 356 of the first
thread**, at the first chain's Script at the base prover. -/
theorem seated_w_at_firstScript
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (hQ : first.script = firstScriptAt I S Op A h.firstChain) (hO : Op.pile = pileAnyK3)
    (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells) :
    ∃ blk rad, K1Seated (firstLetters h first w) 356 blk (witB I A.Z)
      (K1.wJobAt A.Z.first (K1.wGp A.Z) 4 wMsgFull (K1.lotNo OnBytes.secondHashFunction A.Z ⟨1, none, 4, .K1⟩)
        (wDataAt pileAnyK3 A.Z A.G)) () .w (P5J.At.arr A.Z) (P5J.At.seats A.Z)
      (P5J.At.ms A.Z files.lay) rad := by
  obtain ⟨-, -, blk, R⟩ := k1Seated_first h.head hA
    (fallsAfterBatching (firstFalls A first.numbers) h.firstChain)
    (VerifiableInference.Desc.K2.Honest.carryExact A.Z (P5J.At.arr A.Z)) 0 h.description.t₁
    h.description.t₂ 339 (ReadyInput h.description A.H)
    (ridersOf (csHead nextSlotBehindTheHead (digitsStand A.Z) (heardByAttention A.Z)))
    (kpBy (firstClauses h)) w
  have eL : firstLetters h first w = lettersHead h.head A.H (firstScriptAt I S Op A h.firstChain)
      (fallsAfterBatching (firstFalls A first.numbers) h.firstChain)
      (VerifiableInference.Desc.K2.Honest.carryExact A.Z (P5J.At.arr A.Z)) 0 h.description.t₁
      h.description.t₂ 339 (ReadyInput h.description A.H)
      (ridersOf (csHead nextSlotBehindTheHead (digitsStand A.Z) (heardByAttention A.Z)))
      (kpBy (firstClauses h)) w := by
    unfold firstLetters
    rw [hQ]
  rw [← eL] at R
  have eJ : jobWAt Op A.Z A.G = K1.wJobAt A.Z.first (K1.wGp A.Z) 4 wMsgFull
      (K1.lotNo OnBytes.secondHashFunction A.Z ⟨1, none, 4, .K1⟩) (wDataAt pileAnyK3 A.Z A.G) := by
    unfold jobWAt
    rw [hO]
  rw [eJ] at R
  exact ⟨blk, _, R⟩

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- hR, hQ, hO and hrw are premises. **The five items of the last chain's start hold at the door, at
a run's two earlier threads**, in the meaning of `lastParts`, at every strings y. -/
theorem door_five_at_run
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (h : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ IndexCommitterCoins)
    {Wt : Type} (shared : SharedThreadParts A Wt) (L : LastLetters A)
    (R : Ready W₀ IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit)
    (hQ : first.script = firstScriptAt I S Op A h.firstChain) (hO : Op.pile = pileAnyK3)
    (hrw : reads.weights = I.weights A.Z) {w₀ : W₀} {rc : IndexCommitterCoins} {x : ProofFile.Inst} {k : Coins A.B}
    (hR : ready h.description A.B A.H w₀ rc x k = .ok R) :
    ∀ e₁ m₁ E₁ e₂ m₂ E₂,
      ThrS (threadOne h first R) (saidOne h first R) h.description.first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS (threadTwo h reads shared R) (saidTwo h reads shared R)
        h.description.shared.blocksInOrder.length k e₂ m₂ E₂ →
      ∀ s₃ ds y, ∀ i ∈ startLast,
        ItemL.holds h.sharedNumbers ((lastParts h first L).meaning R.own) h.lastMeaning i
          (x.pub, e₁) e₂ s₃ y
          (lastWitness h first reads k R.own (m₁.st.heard ++ m₂.st.heard ++ ds)) := by
  intro e₁ m₁ E₁ e₂ m₂ E₂ u₁ u₂ s₃ ds y
  obtain ⟨-, tr, -, hown, hcom, -, -, -⟩ := ready_ok hR
  have ex : R.own.x = x := by rw [hown]
  have ec : R.common = ⟨R.own.w₀, R.own.rc, A.H.key R.own.x⟩ := by rw [hcom, hown]
  obtain ⟨blk, rad, Rw⟩ := seated_w_at_firstScript hA h first hQ hO R.own
  have u₂' : Thr (sharedThread h reads shared ⟨R.own.w₀, R.own.rc, A.H.key R.own.x⟩)
      h.description.shared.blocksInOrder.length k e₂ m₂ E₂ := ec ▸ u₂.1
  have key := five_at_the_threads h first reads shared L R.own Rw rfl
    (by rw [hrw]; rfl) u₁.1 u₂' s₃ ds y
  rw [ex] at key
  exact key

/-- The premises are those of `door_five_at_run`. **The same in the letters in which the threads'
debts at a run are gathered**: at the last thread at `lastParts`, and at that thread's own strings.
-/
theorem door_five_at_lastParts
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (h : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ IndexCommitterCoins)
    {Wt : Type} (shared : SharedThreadParts A Wt) (L : LastLetters A)
    (R : Ready W₀ IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit)
    (hQ : first.script = firstScriptAt I S Op A h.firstChain) (hO : Op.pile = pileAnyK3)
    (hrw : reads.weights = I.weights A.Z) {w₀ : W₀} {rc : IndexCommitterCoins} {x : ProofFile.Inst} {k : Coins A.B}
    (hR : ready h.description A.B A.H w₀ rc x k = .ok R) :
    ∀ e₁ m₁ E₁ e₂ m₂ E₂,
      ThrS (threadOne h first R) (saidOne h first R) h.description.first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS (threadTwo h reads shared R) (saidTwo h reads shared R)
        h.description.shared.blocksInOrder.length k e₂ m₂ E₂ →
      ∀ s₃ ds, ∀ i ∈ startLast,
        ItemL.holds h.sharedNumbers
          ((lastParts h first L).meaning R.own) h.lastMeaning i
          (x.pub, e₁) e₂ s₃
          ((threadThree h first reads (lastParts h first L) R).strs (envThird E₁ E₂))
          (lastWitness h first reads k R.own (m₁.st.heard ++ m₂.st.heard ++ ds)) :=
  fun e₁ m₁ E₁ e₂ m₂ E₂ u₁ u₂ s₃ ds =>
    door_five_at_run hA h first reads shared L R hQ hO hrw hR e₁ m₁ E₁ e₂ m₂ E₂ u₁ u₂ s₃ ds _

/-- ho₁, ho₂, hd₁, hd₂ and the premises of `door_five_at_lastParts` are premises. **The items that
are open at the last thread's first border hold at the stand with which that thread begins**, at the
last thread whose field on the two earlier chains' ends is laid at the run (`lastAtRun`): the law
asks that field at just that term. The library's law on the door's items (`items_at_letters`) with
its premise on the five paid. -/
theorem door_items_at_lastParts
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (h : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ IndexCommitterCoins)
    {Wt : Type} (shared : SharedThreadParts A Wt) (L : LastLetters A)
    (R : Ready W₀ IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit)
    (hQ : first.script = firstScriptAt I S Op A h.firstChain) (hO : Op.pile = pileAnyK3)
    (hrw : reads.weights = I.weights A.Z) {w₀ : W₀} {rc : IndexCommitterCoins} {x : ProofFile.Inst} {k : Coins A.B}
    (hR : ready h.description A.B A.H w₀ rc x k = .ok R)
    (ho₁ : ∀ b, b ≤ h.description.first.blocksInOrder.length →
      (threadOne h first R).opensAvailable b = true)
    (ho₂ : ∀ b, b ≤ h.description.shared.blocksInOrder.length →
      (threadTwo h reads shared R).opensAvailable b = true)
    (hd₁ : ∀ k b, b ≤ h.description.first.blocksInOrder.length → ∀ m,
      WalkedTo (threadOne h first R) (firstStand A.H R) k b m →
      DepthsAt (threadOne h first R) b k m)
    (hd₂ : ∀ k b, b ≤ h.description.shared.blocksInOrder.length → ∀ m,
      WalkedTo (threadTwo h reads shared R) (sharedStand A.H R) k b m →
      DepthsAt (threadTwo h reads shared R) b k m) :
    ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₃,
      ThrS (threadOne h first R) (saidOne h first R) h.description.first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS (threadTwo h reads shared R) (saidTwo h reads shared R)
        h.description.shared.blocksInOrder.length k e₂ m₂ E₂ →
      h.description.start₃ x.pub e₁ e₂ = .ok s₃ →
      (threadThree h first reads (lastAtRun h first reads shared (lastParts h first L) R) R).Items
        ((threadThree h first reads
          (lastAtRun h first reads shared (lastParts h first L) R) R).opened 0) k s₃
        (R.start₃ A.H m₁ m₂) (envThird E₁ E₂) :=
  AtFullSide.K13.items_at_letters h.head A.H first.script _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hR rfl ho₁ ho₂ hd₁ hd₂ fun e₁ m₁ E₁ e₂ m₂ E₂ u₁ u₂ s₃ ds =>
      door_five_at_run hA h first reads shared L R hQ hO hrw hR e₁ m₁ E₁ e₂ m₂ E₂ u₁ u₂ s₃ ds _

end AtFullSide.Honest

#print axioms AtFullSide.Honest.five_at_the_threads
#print axioms AtFullSide.Honest.seated_w_at_firstScript
#print axioms AtFullSide.Honest.door_five_at_run
#print axioms AtFullSide.Honest.door_five_at_lastParts
#print axioms AtFullSide.Honest.door_items_at_lastParts
