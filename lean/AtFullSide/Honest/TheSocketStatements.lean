-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/TheSocketStatements.lean: each field of ThreadFields (ThreadsAtTheTerm.lean) as a
proposition of its own, at the same letters, so that TheOneObject.lean can name it as one socket.
-/
import AtFullSide.Honest.ThreadsAtTheTerm

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace AtFullSide.Honest.Socket
open ProofFile.Honest ProofFile.Honest.FirstThread
open OnBytes.HonestTrace (ScriptTies ServesAt)
open Inst.Model Inst.Model.All

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

variable {W₀ : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (h : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ IndexCommitterCoins)
  {Wt : Type} (shared : SharedThreadParts A Wt) (last : LastThreadParts A)
  (R : Ready W₀ IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit)
  (J₁ : Nat → h.description.S₁ → Prop) (f₁ : List (Fall h.description.S₁))
  (f₂ : List (Fall h.description.S₂)) (f₃ : List (Fall h.description.S₃))
  (x : ProofFile.Inst) (k : Coins A.B)

/-- each tree available at a border is fixed by the challenges heard there -/
abbrev fix₁ : Prop :=
  ∀ b, b ≤ h.firstChain.blocksInOrder.length → ∀ j, j < treesTo h.firstChain.blocksInOrder b →
    first.script.fixed (.own j) ≤ roundsTo h.firstChain.blocksInOrder b

abbrev fix₂ : Prop :=
  ∀ b, b ≤ h.description.shared.blocksInOrder.length → ∀ j, j < treesTo h.description.shared.blocksInOrder b →
    shared.fixed (.own j) ≤ roundsTo h.description.shared.blocksInOrder b

abbrev fix₃ : Prop :=
  ∀ b, b ≤ h.description.second.blocksInOrder.length →
    ∀ σ ∈ (threadThree h first reads last R).hand b,
    (threadThree h first reads last R).fixed σ ≤
    (threadThree h first reads last R).front +
    roundsTo (threadThree h first reads last R).bs b

/-- each tree in the second chain's list of taken trees is declared as taken over -/
abbrev takenAre : Prop :=
  ∀ σ ∈ last.taken, ∃ c j, σ = Fmt.TreeSource.taken c j

/-- the first chain's four debts at every member. -/
abbrev owes₁ : Prop :=
  OwesS (threadOne h first R) (saidOne h first R)

/-- the shared chain's. -/
abbrev owes₂ : Prop :=
  OwesS (threadTwo h reads shared R) (saidTwo h reads shared R)

/-- the second chain's. -/
abbrev owes₃ : Prop :=
  OwesS (threadThree h first reads last R) (saidThreeTied h first reads shared last R)

/-- at a member of the second chain with a new tree the sender plays, at the letter without the tie -/
abbrev playsAtTrees₃ : Prop :=
  ∀ b, b < (threadThree h first reads last R).bs.length →
    (threadThree h first reads last R).fresh b ≠ [] →
    PlaysS (threadThree h first reads last R) (saidThree h first reads last R) b

/-- every member that sends a root has a side -/
abbrev rootedSides : Prop :=
  rootedAll h.description A.H = true

/-- what the kinds' laws ask of the run's own input -/
abbrev tied : Prop :=
  TiedAtRun (A := A) reads R.own R.common

/-- at the second chain: each source that a round opens and takes over stands in the list of taken trees -/
abbrev opensTaken : Prop :=
  ∀ d ∈ (threadThree h first reads last R).bs.flatMap (·.rounds), ∀ o ∈ d.opens,
    ∀ c j, o.2 = .taken c j → o.2 ∈ (threadThree h first reads last R).taken

/-- the yes at every member of the first chain. -/
abbrev yes₁ : Prop :=
  ∀ b, b < (threadOne h first R).bs.length →
    AcceptedJ (threadOne h first R) (saidOne h first R) J₁ (fallsBy f₁ h.description.first.blocksInOrder) b

/-- J₁ one member on. -/
abbrev carry₁ : Prop :=
  ∀ b, b < (threadOne h first R).bs.length →
    NextJ (threadOne h first R) (saidOne h first R) J₁ (fallsBy f₁ h.description.first.blocksInOrder) b

/-- the yes at every member of the shared chain. -/
abbrev yes₂ : Prop :=
  YesS (threadTwo h reads shared R) (saidTwo h reads shared R)
    (fallsBy f₂ h.description.shared.blocksInOrder)

/-- the yes at every member of the second chain. -/
abbrev yes₃ : Prop :=
  YesS (threadThree h first reads last R) (saidThreeTied h first reads shared last R)
    (fallsBy f₃ h.description.second.blocksInOrder)

/-- the instance's start is fit -/
abbrev startFit : Prop :=
  h.description.okStart x = true

/-- the request's bytes parse -/
abbrev requestParses : Prop :=
  (_root_.Meaning.backReq (h.head.𝔇.reqB x.pub)).isSome = true

/-- the request is served, and the Script meets the honest trace -/
abbrev served : Prop :=
  ∃ (i : Cm.Idx) (s : Instance ppref), ServesAt (P5J.At.X A.Z) i s ∧
    ScriptTies files A.Z h.firstChain first.script k R.own i s

/-- J₁ at the first state. -/
abbrev startJ : Prop :=
  J₁ 0 (h.description.start₁ (h.description.pub x))

/-- at the door: the trees taken over, the form, the items and the riders at the second chain's first state -/
abbrev doorTrees : Prop :=
  ∀ e₁ m₁ E₁ e₂ m₂ E₂,
    ThrS (threadOne h first R) (saidOne h first R) h.description.first.blocksInOrder.length k e₁ m₁ E₁ →
    ThrS (threadTwo h reads shared R) (saidTwo h reads shared R)
    h.description.shared.blocksInOrder.length k e₂ m₂ E₂ →
    (threadThree h first reads last R).Trees (threadThree h first reads last R).taken k
    (R.start₃ A.H m₁ m₂) (envThird E₁ E₂)

abbrev doorFive : Prop :=
  ∀ e₁ m₁ E₁ e₂ m₂ E₂,
    ThrS (threadOne h first R) (saidOne h first R) h.description.first.blocksInOrder.length k e₁ m₁ E₁ →
    ThrS (threadTwo h reads shared R) (saidTwo h reads shared R)
    h.description.shared.blocksInOrder.length k e₂ m₂ E₂ →
    ∀ s₃ ds, ∀ i ∈ VerifiableInference.Desc.Last.startLast,
    VerifiableInference.Desc.Last.ItemL.holds h.sharedNumbers
    (last.meaning R.own) h.lastMeaning i (x.pub, e₁) e₂ s₃
    ((threadThree h first reads last R).strs (envThird E₁ E₂))
    (lastWitness h first reads k R.own (m₁.st.heard ++ m₂.st.heard ++ ds))

abbrev doorRides : Prop :=
  ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₃,
    ThrS (threadOne h first R) (saidOne h first R) h.description.first.blocksInOrder.length k e₁ m₁ E₁ →
    ThrS (threadTwo h reads shared R) (saidTwo h reads shared R)
    h.description.shared.blocksInOrder.length k e₂ m₂ E₂ →
    h.description.start₃ x.pub e₁ e₂ = .ok s₃ → last.rides 0 R.own s₃

end AtFullSide.Honest.Socket
