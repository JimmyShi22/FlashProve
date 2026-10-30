-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/TheLettersLast.lean: the second chain's letters of the proof file, as definitions. The head of
TheLetters.lean says what the letters are. OpenLast is a structure of named holes.
-/
import AtFullSide.Honest.TheLettersShared
import AtFullSide.K12.LettersAtHead
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WLaidDefs
import Johnson.Desc.ProofFile.Honest.K14.TiedToEnds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.Honest.TheLetters
open AtPublicFiles.AtFiles
open ProofFile.Honest ProofFile.Honest.FirstThread
open AtFullSide.Honest

open ProofFile.Honest.Term (matrixInput)
open VerifiableInference.Desc (Place Block)
open OnBytes (TableKey)
open VerifierAndGoals (PublicFiles)

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]
variable {Z : PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (h : HeadAtReturn Z A)

/-! ## The last chain -/

/-- The challenges that the first chain hears. -/
abbrev firstRounds : ℕ :=
  (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length).length

/-- The challenges in front of the second chain's own test: the two earlier chains'. It is the second
thread's front (lastFront_is_front), at which IOP's five_at_base_rest pins the argument. -/
abbrev lastFront : ℕ :=
  firstRounds h + (declsTo h.description.shared.blocksInOrder h.description.shared.blocksInOrder.length).length

/-- The shared chain's input at a run's input. -/
abbrev toCommon (v : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) : Common FullSizeMatrix IndexCommitterCoins TableKey :=
  ⟨v.w₀, v.rc, A.H.key v.x⟩

/-- The first chain's first stand at an input: firstStand, read off the input alone. -/
def standOne (v : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (_ : Coins A.B) :
    Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit :=
  ⟨⟨v, [], A.H.own₀⟩, [], [], some []⟩

/-- The shared chain's first stand at an input: sharedStand, read off the input alone. -/
def standTwo (c : Common FullSizeMatrix IndexCommitterCoins TableKey) (_ : Coins A.B) :
    Mid (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit :=
  { startShared A.H c with opened := some [] }

/-- **What the last chain is handed, at an input**: the two earlier chains' last states, by endsBy,
at the threads and stands of that input. The two Inhabited instances give endsBy's default, which it
returns only where no two such states exist: at a run where each chain has one state for each run
(endsAre_endsBy), neither instance is read, so no value of them is named here. -/
def endsAt (O : OpenShared A) (k : Coins A.B) (w : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
    (heard : List Fmt.Drawn) : (ProofFile.InstPub × P5J.TS) × Desc.K14.St :=
  let both := endsBy (firstThread h (first h) w)
    (SaidWalk (firstThread h (first h) w) BaseNil (standOne (A := A) w))
    h.description.first.blocksInOrder.length
    (sharedThread h (reads h) (shared h O) (toCommon (A := A) w))
    (SaidWalk (sharedThread h (reads h) (shared h O) (toCommon (A := A) w)) BaseNil
      (standTwo (A := A) (toCommon (A := A) w)))
    h.description.shared.blocksInOrder.length id (toCommon (A := A)) k w heard
  ((w.x.pub, both.1), both.2)

/-- **The named holes of the last chain.** An OpenLast is data and one proposition, depths: it is a
premise of what follows. -/
structure OpenLast (O : OpenShared A) where
  /-- the chain's own test, as the job of the filling -/
  ownMany : ProofFile.Honest.K12.Light.ManyJob (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit
  ownIsTheFilling : AtFullSide.K12.jobAtFill A.Z h.places h.firstChain matrixInput
    OnBytes.HonestTrace.Sz.ref openHonest A.G = some ownMany
  /-- the tables' depths, by lastLetters_depths -/
  depths : ∀ d ∈ A.F.second.blocksInOrder.flatMap (·.rounds), ∀ o ∈ d.opens, ∀ k w hd,
    (ProofFile.Honest.K12.AtFile.lastTable (firstRounds h) (toCommon (A := A))
      (first h).script.table (later (h := h) O).table
      (ProofFile.Honest.K12.AtFile.ownLast ownMany.toRun.toTest () (lastFront h)) o.2 k w hd).2.logLength =
        o.1.a

/-- **lastAt**: one value of LastLetters, with no letter for the run: ends is endsAt, and the own
test's clause of keeps says nothing, since nothing of that test spends it (IOP). -/
def last {O : OpenShared A} (P : OpenLast h O) : LastLetters A :=
  ProofFile.Honest.K12.AtFile.lastLettersOf (firstRounds h) (lastFront h) (toCommon (A := A))
    (first h).script.table (later (h := h) O).table (first h).script.fixed
    (later (h := h) O).fixed P.ownMany.toRun.toTest () (endsAt h O) (lastRiders h.places [])
    (lastKeeps fun _ _ _ => True) P.depths

section Run
variable {O : OpenShared A} (P : OpenLast h O)
  (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit)

abbrev thread₃ := lastThread h (first h) (reads h) (lastParts h (first h) (last h P)) R.own

/-- The field letter at the columns of the two earlier chains, without the tie. -/
abbrev said₃Field : Nat → Coins A.B → Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop :=
  SaidField (thread₃ h P R) (BaseTied h.description (thread₃ h P R))

/-- said₃: that letter, with the tie to the two ends. -/
abbrev said₃ : Nat → Coins A.B → Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop :=
  fun b k m => said₃Field h P R b k m ∧
    ProofFile.Honest.K14.TiedToEnds (thread₁ h R) (said₁ h R) h.description.first.blocksInOrder.length
      (thread₂ h R (O := O)) (said₂ h R (O := O)) h.description.shared.blocksInOrder.length id
      (fun v => ⟨v.w₀, v.rc, A.H.key v.x⟩) (thread₃ h P R).front b k m

end Run

end AtFullSide.Honest.TheLetters
