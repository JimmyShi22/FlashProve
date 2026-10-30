-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/DoorAtTheTerm.lean: WHAT THE DOOR LAYS AT THE THREE THREADS OF ONE RUN. The three
threads are the values of AtFullSide/Honest/TheThreeThreads.lean: the values of lettersHead,
lettersShared and lettersLast at a return of the maker. Here the form, the items and the file's last
test are called at these letters, in the words that ThreadsAtTheTerm.lean spends.

  lettersTwo, lettersThree   the letters of the two later threads of the run
  ends_at_term, ends_of_run   the letter ends is the two earlier chains' last states

  door_form_at_term    the form at the second chain's first border
  door_items_at_term   its five items
  begun_at_term        the shared thread begins at the description's start
  fin_yes_at_term      the file's last test says yes

What these are. Conditional lemmas. None is one of the library's goals. They say nothing of
soundness, completeness or hiding.

Limits.
  * Each keeps the premises of the lemma that it calls, at the stands, named as there.
  * That the second chain's start says yes is in DoorYesAtTheTerm.lean of this folder.
-/
import AtFullSide.Honest.TheThreeThreads
import AtFullSide.K13.DoorAtLetters
import AtFullSide.K13.DoorYesAtEnds
import E2E.FinThirdClause

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace AtFullSide.Honest
open ProofFile.Honest ProofFile.Honest.FirstThread
open AtFullSide.K13

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

variable {W₀ : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (h : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ IndexCommitterCoins)
  {Wt : Type} (shared : SharedThreadParts A Wt) (last : LastThreadParts A)
  (R : Ready W₀ IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit)
  (x : ProofFile.Inst) (k : Coins A.B)

/-- **The shared thread begins at the description's own start.** -/
theorem begun_at_term : ∀ (k : Coins A.B) w hd s₀, (threadTwo h reads shared R).begun k w hd s₀ →
    ∃ p, s₀ = h.description.start₂ p :=
  fun _ w _ _ hb => ⟨⟨ByteArray.empty, w.key⟩, hb⟩

/-- **The file's last test says yes.** hw: the run's instance is x. hok: its start is fit. -/
theorem fin_yes_at_term (hw : R.own.x = x) (hok : h.description.okStart x = true) :
    ∀ e₁ m₁ E₁ e₂ m₂ E₂ e₃ m₃ E₃,
      ThrS (threadOne h first R) (saidOne h first R) h.description.first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS (threadTwo h reads shared R) (saidTwo h reads shared R)
        h.description.shared.blocksInOrder.length k e₂ m₂ E₂ →
      ThrS (threadThree h first reads last R) (saidThree h first reads last R)
        h.description.second.blocksInOrder.length k e₃ m₃ E₃ →
      h.description.fin x e₁ e₂ e₃ = true :=
  finYes_of_parts h.head A.H first.script _ _ _ _ _ _ _ _ _ _ (ξ := x)
    (by
      rw [Johnson.AtFull.Shape.flat_len h.head]
      decide)
    hw rfl rfl rfl (fun e₁ m₁ E₁ u₁ => by
      have i₁ : m₁.st.input = R.own := u₁.1.2.2.2.2.2.2.1
      have hq := req_at_first_end h.head A.H first.script _ _ _ _ _ _ _ _ _ _ u₁.1
      rw [i₁, hw] at hq
      exact AtPublicFiles.Start.third_of_okStart hok hq)

/-- The shared chain's letters of the run, as sharedThread lays them. -/
abbrev lettersTwo :=
  SharedThread.lettersShared A.Z h.places h.firstChain A.H h.sharedNumbers
    (fun v => ProofFile.Honest.K14.mgWords shared.lens (VerifiableInference.Desc.K1.qAt A.Z h.places)
      h.sharedNumbers (shared.meaning v))
    (ProofFile.Honest.K14.form2 (VerifiableInference.Desc.K1.qAt A.Z h.places) shared.shape)
    (fun d => (_root_.Desc.K14.ended d).isSome) (fun s => OnBytes.Means.InOrder s.st)
    (ProofFile.Honest.K14.witL shared.lens (VerifiableInference.Desc.K1.qAt A.Z h.places)
      (sentFirstOf A.Z h.places)
      (ProofFile.Honest.K14.holds2 (VerifiableInference.Desc.K1.qAt A.Z h.places) reads.weights
        reads.rand) shared.rest)
    shared.table shared.fixed h.description.t₁ h.description.t₂
    (fun v => A.H.inRange v.w₀ = true) shared.rides
    (ProofFile.Honest.K14.kp2 (VerifiableInference.Desc.K1.qAt A.Z h.places) (sentFirstOf A.Z h.places)
      shared.keeps)
    R.common

/-- The second chain's letters of the run, as lastThread lays them. -/
abbrev lettersThree :=
  LastThread.lettersLast A.Z h.places h.firstChain A.H h.sharedNumbers last.meaning h.lastMeaning
    h.lastForm (fun s => OnBytes.Means.InOrder s.st) last.taken last.ends
    (lastWitness h first reads) last.table last.fixed 0
    h.description.t₁ h.description.t₂ (ReadyInput h.description A.H) last.rides
    (ProofFile.Honest.K14.kpSecond (ToldDesc.p14At A.Z) last.keeps) R.own

/-- What the door's two calls share: the two earlier chains' ends are what the letter ends says. -/
theorem ends_at_term {w₀ : W₀} {rc : IndexCommitterCoins}
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
    ∀ e₁ m₁ E₁ e₂ m₂ E₂, ThrS (threadOne h first R) (saidOne h first R) h.description.first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS (threadTwo h reads shared R) (saidTwo h reads shared R)
        h.description.shared.blocksInOrder.length k e₂ m₂ E₂ →
      (lastAtRun h first reads shared last R).ends k R.own (m₁.st.heard ++ m₂.st.heard) =
        ((x.pub, e₁), e₂) :=
  ends_at_door h.head A.H first.script _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hR rfl rfl rfl ho₁ ho₂
    hd₁ hd₂

/-- **The letter ends of the second chain at the run names the two states.** hrun: at the run's own
input it says what the function of lastAtRun says. -/
theorem ends_of_run {w₀ : W₀} {rc : IndexCommitterCoins}
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
      DepthsAt (threadTwo h reads shared R) b k m)
    (hrun : ∀ k hd, last.ends k R.own hd = (lastAtRun h first reads shared last R).ends k R.own hd)
    :
    ∀ e₁ m₁ E₁ e₂ m₂ E₂, ThrS (threadOne h first R) (saidOne h first R) h.description.first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS (threadTwo h reads shared R) (saidTwo h reads shared R)
        h.description.shared.blocksInOrder.length k e₂ m₂ E₂ →
      last.ends k R.own (m₁.st.heard ++ m₂.st.heard) = ((x.pub, e₁), e₂) :=
  fun e₁ m₁ E₁ e₂ m₂ E₂ u₁ u₂ => (hrun k _).trans
    (ends_at_term h first reads shared last R x k hR ho₁ ho₂ hd₁ hd₂ e₁ m₁ E₁ e₂ m₂ E₂ u₁ u₂)

/-- **The form at the second chain's first border.** -/
theorem door_form_at_term
    (hends : ∀ e₁ m₁ E₁ e₂ m₂ E₂, ThrS (threadOne h first R) (saidOne h first R) h.description.first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS (threadTwo h reads shared R) (saidTwo h reads shared R)
        h.description.shared.blocksInOrder.length k e₂ m₂ E₂ →
      last.ends k R.own (m₁.st.heard ++ m₂.st.heard) = ((x.pub, e₁), e₂))
    (hfirst : ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₃, ThrS (threadOne h first R) (saidOne h first R) h.description.first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS (threadTwo h reads shared R) (saidTwo h reads shared R)
        h.description.shared.blocksInOrder.length k e₂ m₂ E₂ →
      h.description.start₃ x.pub e₁ e₂ = .ok s₃ →
      ∀ f, VerifiableInference.Desc.Third.firstOfS e₁ = some f →
        VerifiableInference.Desc.Last.firstDoorB f = true)
    (hshared : ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₃, ThrS (threadOne h first R) (saidOne h first R) h.description.first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS (threadTwo h reads shared R) (saidTwo h reads shared R)
        h.description.shared.blocksInOrder.length k e₂ m₂ E₂ →
      h.description.start₃ x.pub e₁ e₂ = .ok s₃ → ∀ e, Desc.K14.ended e₂ = some e →
        VerifiableInference.Desc.Last.sharedDoorB (ProofFile.pAt A.Z)
          (VerifiableInference.Desc.Third.sharedOfEnd e) = true) :
    ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₃, ThrS (threadOne h first R) (saidOne h first R) h.description.first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS (threadTwo h reads shared R) (saidTwo h reads shared R)
        h.description.shared.blocksInOrder.length k e₂ m₂ E₂ →
      h.description.start₃ x.pub e₁ e₂ = .ok s₃ →
      (threadThree h first reads last R).Form 0 k s₃ (R.start₃ A.H m₁ m₂) := by
  intro e₁ m₁ E₁ e₂ m₂ E₂ s₃ u₁ u₂ hs
  exact form_at_door (firstLetters h first R.own) (lettersTwo h reads shared R)
    (lettersThree h first reads last R) (LLT25.c2 h.places).rounds rfl rfl rfl rfl u₁.1 u₂.1
    (hends e₁ m₁ E₁ e₂ m₂ E₂ u₁ u₂) hs
    (hfirst e₁ m₁ E₁ e₂ m₂ E₂ s₃ u₁ u₂ hs) (hshared e₁ m₁ E₁ e₂ m₂ E₂ s₃ u₁ u₂ hs)
    (fun _ h => h)

/-- **The five items at the second chain's first border.** -/
theorem door_items_at_term
    (hends : ∀ e₁ m₁ E₁ e₂ m₂ E₂, ThrS (threadOne h first R) (saidOne h first R) h.description.first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS (threadTwo h reads shared R) (saidTwo h reads shared R)
        h.description.shared.blocksInOrder.length k e₂ m₂ E₂ →
      last.ends k R.own (m₁.st.heard ++ m₂.st.heard) = ((x.pub, e₁), e₂))
    (five : ∀ e₁ m₁ E₁ e₂ m₂ E₂, ThrS (threadOne h first R) (saidOne h first R) h.description.first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS (threadTwo h reads shared R) (saidTwo h reads shared R)
        h.description.shared.blocksInOrder.length k e₂ m₂ E₂ →
      ∀ s₃ ds, ∀ i ∈ VerifiableInference.Desc.Last.startLast,
        VerifiableInference.Desc.Last.ItemL.holds h.sharedNumbers (last.meaning R.own) h.lastMeaning
          i (x.pub, e₁) e₂ s₃ ((threadThree h first reads last R).strs (envThird E₁ E₂))
          (lastWitness h first reads k R.own (m₁.st.heard ++ m₂.st.heard ++ ds))) :
    ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₃, ThrS (threadOne h first R) (saidOne h first R) h.description.first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS (threadTwo h reads shared R) (saidTwo h reads shared R)
        h.description.shared.blocksInOrder.length k e₂ m₂ E₂ →
      h.description.start₃ x.pub e₁ e₂ = .ok s₃ →
      (threadThree h first reads last R).Items
        ((threadThree h first reads last R).opened 0) k s₃ (R.start₃ A.H m₁ m₂)
        (envThird E₁ E₂) :=
  fun e₁ m₁ E₁ e₂ m₂ E₂ s₃ u₁ u₂ _ =>
    items_at_door (firstLetters h first R.own) (lettersTwo h reads shared R)
      (lettersThree h first reads last R) (H := A.H) (ξ := x) (k := k) (R := R) rfl rfl rfl hends
      five e₁ m₁ E₁ e₂ m₂ E₂ s₃ u₁ u₂

end AtFullSide.Honest

#print axioms AtFullSide.Honest.ends_at_term
#print axioms AtFullSide.Honest.ends_of_run
#print axioms AtFullSide.Honest.door_form_at_term
#print axioms AtFullSide.Honest.door_items_at_term
#print axioms AtFullSide.Honest.begun_at_term
#print axioms AtFullSide.Honest.fin_yes_at_term
