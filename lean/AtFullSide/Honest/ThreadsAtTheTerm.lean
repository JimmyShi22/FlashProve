-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/ThreadsAtTheTerm.lean: the hypotheses on the three threads, at the base prover.

The online part has three chains, the first, the shared and the second. A thread (Honest/Thread/
Thr.lean) is the invariant that ties the verifier's state at each border of a chain to the honest
prover's run. ThreadsCJ is what the rule for the whole file asks of the three invariants.

1. The three threads and what is said at each are TheThreeThreads.lean's.
2. ThreadDebts lists what the three threads owe there, at one run that ready has returned.
   TheThreadDebts is that list at the run on shapes and at firstFalls.
3. fromThreadsAtTheTerm lays the value of FromThreadsJ from it, and threadsAtTheTerm the value of
   ThreadsCJ. Sits, what is said at the two starts and carried at the first two chains, the
   invariants at the two starts and the door are laid here from the fields.
4. The third family says nothing at the shared and the second chain. All of this holds for nothing
   where a field can't be met: the fields are hypotheses.
-/
import AtFullSide.Honest.DoorAtTheTerm
import AtFullSide.Honest.DoorFormAtTheTerm
import AtFullSide.Honest.DoorTiedAtTheTerm
import AtFullSide.Honest.TheThreeThreads
import Johnson.AtFull.Shape.RuleAtTable
import Johnson.Desc.ProofFile.Honest.Thread.DepthsOfWalk
import Johnson.Desc.ProofFile.Honest.Thread.DoorOfEnds
import Johnson.Desc.ProofFile.Honest.Thread.EntersFirst
import Johnson.Desc.ProofFile.Honest.Thread.FitsAtTerm
import Johnson.Desc.ProofFile.Honest.Thread.FromThreadsJ
import Johnson.Desc.ProofFile.Honest.Thread.LastChainFields
import Johnson.Desc.ProofFile.Honest.Thread.NextTied
import Johnson.Desc.ProofFile.Honest.Thread.NoStopOfSenders
import Johnson.Desc.ProofFile.Honest.Thread.OpensOfPlan
import Johnson.Desc.ProofFile.Honest.Thread.QuietAtBase
import Johnson.Desc.ProofFile.Honest.Thread.TheLaterThreads

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace AtFullSide.Honest
open ProofFile.Honest ProofFile.Honest.FirstThread
open OnBytes.HonestTrace (ScriptTies ServesAt)
open Inst.Model Inst.Model.All

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

variable {W₀ : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (h : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ IndexCommitterCoins)
  {Wt : Type} (shared : SharedThreadParts A Wt) (last : LastThreadParts A)
  (R : Ready W₀ IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit)

variable (J₁ : Nat → h.description.S₁ → Prop) (f₁ : List (Fall h.description.S₁))
  (f₂ : List (Fall h.description.S₂)) (f₃ : List (Fall h.description.S₃))
  (w₀ : W₀) (rc : IndexCommitterCoins) (x : ProofFile.Inst) (k : Coins A.B)

/-- **What the three threads owe at one run for the run to return**, but for two fields. -/
structure ThreadFieldsP : Prop where
  /-- each tree available at a border is fixed by the challenges heard there -/
  fix₁ : ∀ b, b ≤ h.firstChain.blocksInOrder.length → ∀ j, j < treesTo h.firstChain.blocksInOrder b →
    first.script.fixed (.own j) ≤ roundsTo h.firstChain.blocksInOrder b
  fix₂ : ∀ b, b ≤ h.description.shared.blocksInOrder.length → ∀ j, j < treesTo h.description.shared.blocksInOrder b →
    shared.fixed (.own j) ≤ roundsTo h.description.shared.blocksInOrder b
  fix₃ : ∀ b, b ≤ h.description.second.blocksInOrder.length →
    ∀ σ ∈ (threadThree h first reads last R).hand b,
    (threadThree h first reads last R).fixed σ ≤
      (threadThree h first reads last R).front +
        roundsTo (threadThree h first reads last R).bs b
  /-- each tree in the second chain's list of taken trees is declared as taken over -/
  takenAre : ∀ σ ∈ last.taken, ∃ c j, σ = Fmt.TreeSource.taken c j
  /-- the first chain's four hypotheses at every member. -/
  owes₁ : OwesS (threadOne h first R) (saidOne h first R)
  /-- the shared chain's -/
  owes₂ : OwesS (threadTwo h reads shared R) (saidTwo h reads shared R)
  /-- the second chain's -/
  owes₃ : OwesS (threadThree h first reads last R) (saidThreeTied h first reads shared last R)
  /-- at a member of the second chain with a new tree the sender plays, at the letter without the tie -/
  playsAtTrees₃ : ∀ b, b < (threadThree h first reads last R).bs.length →
    (threadThree h first reads last R).fresh b ≠ [] →
    PlaysS (threadThree h first reads last R) (saidThree h first reads last R) b
  /-- every member that sends a root has a side -/
  rootedSides : rootedAll h.description A.H = true
  /-- what the kinds' laws ask of the run's own input -/
  tied : TiedAtRun (A := A) reads R.own R.common
  /-- at the second chain: each source that a round opens and takes over stands in the list of taken
  trees -/
  opensTaken : ∀ d ∈ (threadThree h first reads last R).bs.flatMap (·.rounds), ∀ o ∈ d.opens,
    ∀ c j, o.2 = .taken c j → o.2 ∈ (threadThree h first reads last R).taken
  /-- the instance's start is fit -/
  startFit : h.description.okStart x = true
  /-- the request's bytes parse -/
  requestParses : (_root_.Meaning.backReq (h.head.𝔇.reqB x.pub)).isSome = true
  /-- the request is served, and the Script meets the honest trace -/
  served : ∃ (i : Cm.Idx) (s : Instance ppref), ServesAt (P5J.At.X A.Z) i s ∧
    ScriptTies files A.Z h.firstChain first.script k R.own i s
  /-- at the run's own input, the last chain's ends are what the two threads give -/
  endsAtRun : ∀ k hd, last.ends k R.own hd = (lastAtRun h first reads shared last R).ends k R.own hd
  /-- at the door: the trees taken over, the items and the riders at the second chain's first state -/
  doorTrees : ∀ e₁ m₁ E₁ e₂ m₂ E₂,
    ThrS (threadOne h first R) (saidOne h first R) h.description.first.blocksInOrder.length k e₁ m₁ E₁ →
    ThrS (threadTwo h reads shared R) (saidTwo h reads shared R)
      h.description.shared.blocksInOrder.length k e₂ m₂ E₂ →
    (threadThree h first reads last R).Trees (threadThree h first reads last R).taken k
      (R.start₃ A.H m₁ m₂) (envThird E₁ E₂)
  doorFive : ∀ e₁ m₁ E₁ e₂ m₂ E₂,
    ThrS (threadOne h first R) (saidOne h first R) h.description.first.blocksInOrder.length k e₁ m₁ E₁ →
    ThrS (threadTwo h reads shared R) (saidTwo h reads shared R)
      h.description.shared.blocksInOrder.length k e₂ m₂ E₂ →
    ∀ s₃ ds, ∀ i ∈ VerifiableInference.Desc.Last.startLast,
      VerifiableInference.Desc.Last.ItemL.holds h.sharedNumbers
        (last.meaning R.own) h.lastMeaning i (x.pub, e₁) e₂ s₃
        ((threadThree h first reads last R).strs (envThird E₁ E₂))
        (lastWitness h first reads k R.own (m₁.st.heard ++ m₂.st.heard ++ ds))
  doorRides : ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₃,
    ThrS (threadOne h first R) (saidOne h first R) h.description.first.blocksInOrder.length k e₁ m₁ E₁ →
    ThrS (threadTwo h reads shared R) (saidTwo h reads shared R)
      h.description.shared.blocksInOrder.length k e₂ m₂ E₂ →
    h.description.start₃ x.pub e₁ e₂ = .ok s₃ → last.rides 0 R.own s₃

/-- **What the three threads owe at one run for the run to return.** The two further fields are laid
at the term's letters in ThreadsPaidAtTheTerm.lean. -/
structure ThreadDebtsP : Prop extends ThreadFieldsP h first reads shared last R x k where
  /-- the shared chain's invariant at its start; at sharedParts: enters_sharedParts -/
  enters₂ : Enters₂ h.description A.H (threadTwo h reads shared R) w₀ rc x k R
  /-- the depths of the columns that a border of the second chain reads fit -/
  depths₃ : ∀ b blk, (threadThree h first reads last R).bs[b]? = some blk →
    ∀ k s m E ds y cols, Thr (threadThree h first reads last R) b k s m E →
    SaidField (threadThree h first reads last R)
      (BaseTied h.description (threadThree h first reads last R)) b k m →
    drawsFit blk.rounds ds = true →
    (threadThree h first reads last R).Moved blk k m E ds y cols →
    DepthsAt (threadThree h first reads last R) (b + 1) k (y.2.took cols)

/-- **What the verifier's steps owe at one run**: the yes at each chain, and the third family. It is
J₁ at the first chain and says nothing at the two others. -/
structure ThreadFields : Prop extends ThreadFieldsP h first reads shared last R x k where
  /-- the yes at every member of the first chain. Holder: `first_chain_at_first`, conditional -/
  yes₁ : ∀ b, b < (threadOne h first R).bs.length →
    AcceptedJ (threadOne h first R) (saidOne h first R) J₁ (fallsBy f₁ h.description.first.blocksInOrder) b
  /-- J₁ one member on. Holder: the same (Scope/FirstChainAtFirst.lean; hyes, Rest: premises) -/
  carry₁ : ∀ b, b < (threadOne h first R).bs.length →
    NextJ (threadOne h first R) (saidOne h first R) J₁ (fallsBy f₁ h.description.first.blocksInOrder) b
  /-- the yes at every member of the shared chain -/
  yes₂ : YesS (threadTwo h reads shared R) (saidTwo h reads shared R)
    (fallsBy f₂ h.description.shared.blocksInOrder)
  /-- the yes at every member of the second chain -/
  yes₃ : YesS (threadThree h first reads last R) (saidThreeTied h first reads shared last R)
    (fallsBy f₃ h.description.second.blocksInOrder)
  /-- J₁ at the first state. -/
  startJ : J₁ 0 (h.description.start₁ (h.description.pub x))

/-- **What the three threads owe at one run, with the yes.** -/
structure ThreadDebts : Prop extends ThreadDebtsP h first reads shared last R w₀ rc x k where
  /-- the yes at every member of the first chain. Holder: `first_chain_at_first`, conditional -/
  yes₁ : ∀ b, b < (threadOne h first R).bs.length →
    AcceptedJ (threadOne h first R) (saidOne h first R) J₁ (fallsBy f₁ h.description.first.blocksInOrder) b
  /-- J₁ one member on. Holder: the same (Scope/FirstChainAtFirst.lean; hyes, Rest: premises) -/
  carry₁ : ∀ b, b < (threadOne h first R).bs.length →
    NextJ (threadOne h first R) (saidOne h first R) J₁ (fallsBy f₁ h.description.first.blocksInOrder) b
  /-- the yes at every member of the shared chain -/
  yes₂ : YesS (threadTwo h reads shared R) (saidTwo h reads shared R)
    (fallsBy f₂ h.description.shared.blocksInOrder)
  /-- the yes at every member of the second chain -/
  yes₃ : YesS (threadThree h first reads last R) (saidThreeTied h first reads shared last R)
    (fallsBy f₃ h.description.second.blocksInOrder)
  /-- J₁ at the first state. -/
  startJ : J₁ 0 (h.description.start₁ (h.description.pub x))
  /-- the second chain's start says yes -/
  doorYes : ∀ e₁ m₁ E₁ e₂ m₂ E₂,
    ThrS (threadOne h first R) (saidOne h first R) h.description.first.blocksInOrder.length k e₁ m₁ E₁ →
    ThrS (threadTwo h reads shared R) (saidTwo h reads shared R)
      h.description.shared.blocksInOrder.length k e₂ m₂ E₂ →
    J₁ h.description.first.blocksInOrder.length e₁ →
    ∃ s₃, h.description.start₃ (h.description.pub x) e₁ e₂ = .ok s₃

/-- **The third family at the first chain**: the state has the shape that the run on shapes gives. -/
abbrev shapesAtFirst (base : ProofFile.PureBase) : Nat → h.description.S₁ → Prop :=
  shapeJ (Johnson.AtFull.Shape.firstZA (Johnson.AtFull.Shape.Tab.g A.Z base.G₀)
    (Johnson.AtFull.Shape.Tab.vals A.Z base.G₀)) Johnson.AtFull.Shape.startShA

/-- **The hypotheses at the term's letters**: the shared and the second chain's parts are
sharedParts and lastParts, the third family is the run on shapes, the first chain's falls are
firstFalls, and the shared and the second chain have no fall. -/
abbrev TheThreadDebts (base : ProofFile.PureBase) (later : LaterLetters A) (lastLetters : LastLetters A) :=
  ThreadDebts h first reads (sharedParts h later) (lastParts h first lastLetters) R
    (shapesAtFirst h base) (firstFalls A first.numbers) [] [] w₀ rc x k

variable {h first reads shared last R J₁ f₁ f₂ f₃ w₀ rc x k}

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- The run's input at the first chain is the instance. -/
theorem ownInput (hR : ready h.description A.B A.H w₀ rc x k = .ok R) : R.own.x = x := by
  obtain ⟨-, tr, -, hown, -, -, -, -⟩ := ready_ok hR
  rw [hown]

theorem fitsOne (D : ThreadFieldsP h first reads shared last R x k) :
    (threadOne h first R).fits h.description.first.blocksInOrder.length = true :=
  fits_firstThread h first R.own D.fix₁

theorem fitsTwo (D : ThreadFieldsP h first reads shared last R x k) :
    (threadTwo h reads shared R).fits h.description.shared.blocksInOrder.length = true :=
  fits_sharedThread h reads shared R.common D.fix₂

theorem fitsThree (D : ThreadFieldsP h first reads shared last R x k) :
    (threadThree h first reads last R).fits h.description.second.blocksInOrder.length = true :=
  fits_lastThread h first reads _ R.own D.takenAre D.fix₃

theorem depthsOne (D : ThreadFieldsP h first reads shared last R x k)
    (c : Coins A.B) (b : Nat) (_ : b ≤ h.description.first.blocksInOrder.length)
    (m : Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit)
    (hw : WalkedTo (threadOne h first R) (firstStand A.H R) c b m) :
    DepthsAt (threadOne h first R) b c m :=
  depthsAt_first (head_planOk h.head) _ rfl (fitsOne D)
    (half_of_rooted (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 D.rootedSides).1).1) hw

theorem depthsTwo (D : ThreadFieldsP h first reads shared last R x k)
    (c : Coins A.B) (b : Nat) (_ : b ≤ h.description.shared.blocksInOrder.length)
    (m : Mid (Common W₀ IndexCommitterCoins OnBytes.TableKey) Unit)
    (hw : WalkedTo (threadTwo h reads shared R) (sharedStand A.H R) c b m) :
    DepthsAt (threadTwo h reads shared R) b c m :=
  depthsAt_shared (head_planOk h.head) _ rfl (fitsTwo D)
    (half_of_rooted (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 D.rootedSides).1).2) hw

theorem opensOne (D : ThreadFieldsP h first reads shared last R x k)
    (b : Nat) (_ : b ≤ h.description.first.blocksInOrder.length) :
    (threadOne h first R).opensAvailable b = true :=
  opensAvailable_first (head_planOk h.head) _ rfl (roots_of_fits (fitsOne D)) b

theorem opensTwo (D : ThreadFieldsP h first reads shared last R x k)
    (b : Nat) (_ : b ≤ h.description.shared.blocksInOrder.length) :
    (threadTwo h reads shared R).opensAvailable b = true :=
  opensAvailable_shared (head_planOk h.head) _ rfl (roots_of_fits (fitsTwo D)) b

/-- What is said at the second chain is carried: what saidNext_tied_at does, from the members with a
new tree. -/
theorem saidNextThree {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A)
    (D : ThreadDebtsP h first reads shared last R w₀ rc x k) (b : Nat) :
    SaidNext (threadThree h first reads last R) (saidThree h first reads last R) b := by
  intro blk hblk k s m E ds y cols hA hS hd hM
  have hj := lt_of_member _ hblk
  have hT : TreesNext (threadThree h first reads last R)
      (saidThree h first reads last R) b := by
    by_cases hf : (threadThree h first reads last R).fresh b = []
    · exact treesNext_of_fresh_nil _ hf
    · exact treesNext_of_playsS _ (D.playsAtTrees₃ b hj hf)
        (fun _ _ _ _ => chainStop_none (fun y hy _ => quiet_second_at_return made y hy) _ _)
  have hTr := hT blk hblk k s m E ds y cols hA hS hd hM
  have hD := D.depths₃ b blk hblk k s m E ds y cols hA hS hd hM
  obtain ⟨hOk, base, hB, hL⟩ := hS
  exact ⟨saidNext_ok _ b blk hblk k s m E ds y cols hA hOk hd hM, base,
    baseTied_kept _ _ b blk hblk k m E ds y cols base hM hB,
    field_all_next _ (fitsThree D.toThreadFieldsP) (Nat.le_of_lt hj) hblk hA hM hTr hL
      (opensAvailable_second (head_planOk h.head) _ rfl (roots_of_fits (fitsThree D.toThreadFieldsP)) D.opensTaken
        (b + 1)) hD⟩

/-- What is said at the first chain is carried. -/
theorem nextOne {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A)
    (D : ThreadFieldsP h first reads shared last R x k) :
    ∀ b, SaidNext (threadOne h first R) (saidOne h first R) b :=
  saidNext_walk_of_owes _ (fitsOne D) D.owes₁ (noStop_first h.head A.H _ _ _ _ _ _ _ _ _ _ _ (quiet_at_return made))
    (fun b _ => baseNil_kept _ b)
    (fun b hb => opensOne D (b + 1) hb) (fun b hb k m => depthsOne D k (b + 1) hb m)

/-- What is said at the shared chain is carried. -/
theorem nextTwo {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A)
    (D : ThreadFieldsP h first reads shared last R x k) :
    ∀ b, SaidNext (threadTwo h reads shared R) (saidTwo h reads shared R) b :=
  saidNext_walk_of_owes _ (fitsTwo D) D.owes₂
    (fun _ _ _ _ _ _ _ => chainStop_none (fun y hy _ => quiet_shared_at_return made y hy) _ _)
    (fun b _ => baseNil_kept _ b)
    (fun b hb => opensTwo D (b + 1) hb) (fun b hb k m => depthsTwo D k (b + 1) hb m)

/-- The first thread holds at the start. -/
theorem entersOne (D : ThreadFieldsP h first reads shared last R x k)
    (hR : ready h.description A.B A.H w₀ rc x k = .ok R) :
    Enters₁ h.description A.H (threadOne h first R) w₀ rc x k R := by
  obtain ⟨i, s, Sv, Ti⟩ := D.served
  exact enters_firstThread hR D.startFit D.requestParses Sv Ti

/-- The door, with the tie. -/
theorem doorAtTheTerm (D : ThreadFieldsP h first reads shared last R x k)
    (hR : ready h.description A.B A.H w₀ rc x k = .ok R) :
    DoorBehindS h.description A.H (threadOne h first R) (threadTwo h reads shared R)
      (threadThree h first reads last R) (saidOne h first R) (saidTwo h reads shared R)
      (saidThreeTied h first reads shared last R) x k R :=
  have hends := ends_of_run h first reads shared last R x k hR (opensOne D) (opensTwo D) (depthsOne D)
    (depthsTwo D) D.endsAtRun
  door_tied_at_term h first reads shared last R hR <| door_of_ends h.head A.H first.script
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hR (key_at_return h x) rfl rfl rfl
    (sits_at_head h.head A.H first.script _ _ _ _ _ _ _ _ _ R.own _ _ rfl rfl rfl rfl rfl (fitsOne D)
      (fitsTwo D) (fitsThree D))
    hends D.doorTrees (door_form_paid h first reads shared last R x k hends)
    (door_items_at_term h first reads shared last R x k hends D.doorFive) D.doorRides
    (readyInput_of_ready hR D.startFit)

/-- **The value of ThreadsP at the term's threads**: what the run's return reads. -/
def threadsPAtTheTerm {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A)
    (D : ThreadDebtsP h first reads shared last R w₀ rc x k)
    (hR : ready h.description A.B A.H w₀ rc x k = .ok R) :
    ThreadsP h.description A.B A.H w₀ rc x k R :=
  have F : ThreadFieldsP h first reads shared last R x k := D.toThreadFieldsP
  have hs : Sits h.description A.H (threadOne h first R) (threadTwo h reads shared R)
      (threadThree h first reads last R) :=
    sits_at_head h.head A.H first.script _ _ _ _ _ _ _ _ _ R.own _ _ rfl rfl rfl rfl rfl (fitsOne F)
      (fitsTwo F) (fitsThree F)
  { I₁ := ThrS (threadOne h first R) (saidOne h first R)
    I₂ := ThrS (threadTwo h reads shared R) (saidTwo h reads shared R)
    I₃ := ThrS (threadThree h first reads last R) (saidThreeTied h first reads shared last R)
    h₁ := playsS₁ hs (head_planOk h.head) D.owes₁ (nextOne made F)
    h₂ := playsS₂ hs (head_planOk h.head) D.owes₂ (nextTwo made F)
    h₃ := playsS₃ hs (head_planOk h.head) D.owes₃
      (fun b => next_tied_at_term h first reads shared last R (saidNextThree made D b))
    a₁ := ⟨entersOne F hR, saidWalk_start _ rfl rfl⟩
    a₂ := ⟨D.enters₂, saidWalk_start _ rfl rfl⟩
    a₃ := doorAtTheTerm F hR }

/-- **The value of FromThreadsJ at the term's threads.** -/
theorem fromThreadsAtTheTerm {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A)
    (D : ThreadDebts h first reads shared last R J₁ f₁ f₂ f₃ w₀ rc x k)
    (hR : ready h.description A.B A.H w₀ rc x k = .ok R) :
    FromThreadsJ h.description A.H (threadOne h first R) (threadTwo h reads shared R)
      (threadThree h first reads last R) (saidOne h first R) (saidTwo h reads shared R)
      (saidThreeTied h first reads shared last R) J₁ (fun _ _ => True) (fun _ _ => True) f₁ f₂ f₃ w₀ rc x k R
    where
  sits := sits_at_head h.head A.H first.script _ _ _ _ _ _ _ _ _ R.own _ _ rfl rfl rfl rfl rfl
    (fitsOne D.toThreadFieldsP) (fitsTwo D.toThreadFieldsP) (fitsThree D.toThreadFieldsP)
  owes₁ := D.owes₁
  owes₂ := D.owes₂
  owes₃ := D.owes₃
  next₁ := nextOne made D.toThreadFieldsP
  next₂ := nextTwo made D.toThreadFieldsP
  next₃ := fun b => next_tied_at_term h first reads shared last R
    (saidNextThree made D.toThreadDebtsP b)
  yes₁ := D.yes₁
  yes₂ := fun b hb => acceptedJ_of _ _ _ (D.yes₂ b hb)
  yes₃ := fun b hb => acceptedJ_of _ _ _ (D.yes₃ b hb)
  carry₁ := D.carry₁
  carry₂ := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial
  carry₃ := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial
  enters₁ := entersOne D.toThreadFieldsP hR
  enters₂ := D.enters₂
  said₁ := saidWalk_start _ rfl rfl
  said₂ := saidWalk_start _ rfl rfl
  j₁ := D.startJ
  j₂ := trivial
  j₃ := fun _ _ _ _ _ _ => trivial
  door := doorAtTheTerm D.toThreadFieldsP hR
  doorYes := fun e₁ m₁ E₁ e₂ m₂ E₂ u₁ u₂ j _ => D.doorYes e₁ m₁ E₁ e₂ m₂ E₂ u₁ u₂ j
  finYes := fun e₁ m₁ E₁ e₂ m₂ E₂ e₃ m₃ E₃ u₁ u₂ u₃ _ _ _ =>
    fin_yes_at_term h first reads shared last R x k (ownInput hR) D.startFit e₁ m₁ E₁ e₂ m₂ E₂ e₃ m₃
      E₃ u₁ u₂ ⟨u₃.1, u₃.2.1⟩

/-- **The value of ThreadsCJ at the term's threads.** -/
def threadsAtTheTerm {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A)
    (D : ThreadDebts h first reads shared last R J₁ f₁ f₂ f₃ w₀ rc x k)
    (hR : ready h.description A.B A.H w₀ rc x k = .ok R) :
    ThreadsCJ h.description A.B A.H w₀ rc x k R :=
  (fromThreadsAtTheTerm made D hR).threadsCJ (head_planOk h.head)

/-- **At every tied run**: a value of ThreadsCJ with these lists of falls, at every input of the
relation Tied at which ready returns and the hypotheses `ThreadDebts` hold. The second chain's parts
are given for each run: what it reads of the two earlier chains' ends hangs on the run. -/
theorem threadsAtEveryRun {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A) {last : Ready W₀ IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit →
                       LastThreadParts A} {Tied : W₀ → IndexCommitterCoins → ProofFile.Inst → Prop}
    (D : ∀ w₀ rc x k R, Tied w₀ rc x → ready h.description A.B A.H w₀ rc x k = .ok R →
      ThreadDebts h first reads shared (last R) R J₁ f₁ f₂ f₃ w₀ rc x k) :
    ∀ w₀ rc x k R, Tied w₀ rc x → ready h.description A.B A.H w₀ rc x k = .ok R →
      ∃ T : ThreadsCJ h.description A.B A.H w₀ rc x k R, T.f₁ = f₁ ∧ T.f₂ = f₂ ∧ T.f₃ = f₃ :=
  fun w₀ rc x k R ht hR =>
    threadsCJ_of_threads (head_planOk h.head) (fromThreadsAtTheTerm made (D w₀ rc x k R ht hR) hR)

end AtFullSide.Honest

#print axioms AtFullSide.Honest.fromThreadsAtTheTerm
#print axioms AtFullSide.Honest.threadsAtTheTerm
#print axioms AtFullSide.Honest.threadsAtEveryRun
