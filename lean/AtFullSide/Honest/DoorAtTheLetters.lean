-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/DoorAtTheLetters.lean: TWO OF THE DOOR's SENTENCES AT THE NAMED LETTERS
(`TheLetters`, TheLetters.lean and TheLettersFirst.lean of this folder): at the threads `thread₁ h
R`, `thread₂ h R`, `thread₃ h P R` and what is said at the first two, at every return R of `ready`:
the five items with which the last chain's thread begins hold at the door, and the trees that the
last chain takes over are at hand there. Instances. Statements with their proofs; no definition.

Main names.
  `doorFive_at_the_letters`: **the five items, in the meaning of the last thread's parts, at
    `thread₃`'s own strings**: `door_five_at_run` (DoorFiveAtLastParts.lean of this folder); its
    three premises on the Script, the pile's filler and the readers hold by unfolding.
  `doorTrees_at_the_letters`: **the trees taken over, at `thread₃`**: `door_trees_at_lastThread`
    (DoorTreesAtLastParts.lean); its three equations on the list of taken trees, the tables and the
    counts hold by unfolding at `last h P`; its premise on the first chain's trees is the library's
    `treesFixed_first`.
  `doorFive_at_the_letters_atRun`, `doorTrees_at_the_letters_atRun`: the same two in the form of
    `Socket.doorFive` and `Socket.doorTrees` (TheSocketStatements.lean of this folder).

The premises. made: the maker returns A at the filling. hR: `ready` returns R. O, P: the named holes
of the shared and the last chain in TheLetters.lean, at every value; P holds a proof that the tables
have the declared depths: that a value of P exists is not shown here.

Limits. NOT IN FRONT OF A LAW OVER COINS. Each is an implication from the two earlier threads'
invariants at their chains' ends. The full size, and the hash function `OnBytes.secondHashFunction`, alone.

What is not claimed. None of these is one of the library's goals. Nothing on soundness, completeness
or hiding.
-/
import AtFullSide.Honest.DoorFiveAtLastParts
import AtFullSide.Honest.DoorTreesAtLastParts
import AtFullSide.Honest.TheLetters
import AtFullSide.Honest.TheSocketStatements
import AtFullSide.K1.FirstScriptFixed
import E2E.ThruAtTerm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.Honest
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (matrixInput matrixFilling)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open VerifiableInference.Desc.Last (ItemL startLast)
open AtFullSide.Honest.TheLetters (OpenShared OpenLast thread₁ thread₂ thread₃ said₁ said₂)

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

variable {Z : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (h : HeadAtReturn Z A)

/-- made and hR are premises. **The five items of the last chain's start hold at the door, at the
named letters.** -/
theorem doorFive_at_the_letters
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A) {O : OpenShared A}
    (P : OpenLast h O) (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit) {w₀ : FullSizeMatrix}
    {rc : IndexCommitterCoins} {x : ProofFile.Inst} {k : Coins A.B}
    (hR : ready h.description A.B A.H w₀ rc x k = .ok R) :
    ∀ e₁ m₁ E₁ e₂ m₂ E₂,
      ThrS (thread₁ h R) (said₁ h R) h.description.first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS (thread₂ h R (O := O)) (said₂ h R (O := O)) h.description.shared.blocksInOrder.length k e₂ m₂
        E₂ →
      ∀ s₃ ds, ∀ i ∈ startLast,
        ItemL.holds h.sharedNumbers
          ((lastParts h (TheLetters.first h) (TheLetters.last h P)).meaning R.own) h.lastMeaning i
          (x.pub, e₁) e₂ s₃ ((thread₃ h P R).strs (envThird E₁ E₂))
          (lastWitness h (TheLetters.first h) (TheLetters.reads h) k R.own
            (m₁.st.heard ++ m₂.st.heard ++ ds)) :=
  fun e₁ m₁ E₁ e₂ m₂ E₂ u₁ u₂ s₃ ds =>
    door_five_at_run (I := matrixInput) (S := OnBytes.HonestTrace.Sz.ref) (Op := openHonest) made h
      (TheLetters.first h) (TheLetters.reads h) (TheLetters.shared h O) (TheLetters.last h P) R rfl
      rfl rfl hR e₁ m₁ E₁ e₂ m₂ E₂ u₁ u₂ s₃ ds _

/-- made and hR are premises. **The trees that the last chain takes over are at hand at the door, at
the named letters.** -/
theorem doorTrees_at_the_letters
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A) {O : OpenShared A}
    (P : OpenLast h O) (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit) {w₀ : FullSizeMatrix}
    {rc : IndexCommitterCoins} {x : ProofFile.Inst} {k : Coins A.B}
    (hR : ready h.description A.B A.H w₀ rc x k = .ok R) :
    ∀ e₁ m₁ E₁ e₂ m₂ E₂,
      ThrS (thread₁ h R) (said₁ h R) h.description.first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS (thread₂ h R (O := O)) (said₂ h R (O := O)) h.description.shared.blocksInOrder.length k e₂ m₂
        E₂ →
      (thread₃ h P R).Trees (thread₃ h P R).taken k (R.start₃ A.H m₁ m₂) (envThird E₁ E₂) :=
  door_trees_at_lastThread h (TheLetters.first h) (TheLetters.reads h) (TheLetters.shared h O)
    (lastParts h (TheLetters.first h) (TheLetters.last h P)) R hR
    (ProofFile.Honest.K12.AtFile.ownLast P.ownMany.toRun.toTest () (TheLetters.lastFront h))
    (fun τ => TheLetters.lastFront h +
      ProofFile.Honest.K12.seedRound P.ownMany.toRun.toTest.p.nums.stages τ) rfl rfl rfl
    (ProofFile.Honest.K1.treesFixed_first h.head made)

/-- made and hR are premises. The five items, in the form of `Socket.doorFive`. -/
theorem doorFive_at_the_letters_atRun
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A) {O : OpenShared A}
    (P : OpenLast h O) (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit) {w₀ : FullSizeMatrix}
    {rc : IndexCommitterCoins} {x : ProofFile.Inst} {k : Coins A.B}
    (hR : ready h.description A.B A.H w₀ rc x k = .ok R) :
    Socket.doorFive h (TheLetters.first h) (TheLetters.reads h) (TheLetters.shared h O)
      (lastParts h (TheLetters.first h) (TheLetters.last h P)) R x k :=
  door_five_at_lastParts (I := matrixInput) (S := OnBytes.HonestTrace.Sz.ref) (Op := openHonest)
    made h (TheLetters.first h) (TheLetters.reads h) (TheLetters.shared h O) (TheLetters.last h P) R
    rfl rfl rfl hR

/-- made and hR are premises. The trees taken over, in the form of `Socket.doorTrees`. -/
theorem doorTrees_at_the_letters_atRun
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A) {O : OpenShared A}
    (P : OpenLast h O) (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit) {w₀ : FullSizeMatrix}
    {rc : IndexCommitterCoins} {x : ProofFile.Inst} {k : Coins A.B}
    (hR : ready h.description A.B A.H w₀ rc x k = .ok R) :
    Socket.doorTrees h (TheLetters.first h) (TheLetters.reads h) (TheLetters.shared h O)
      (lastParts h (TheLetters.first h) (TheLetters.last h P)) R k :=
  door_trees_at_lastParts h (TheLetters.first h) (TheLetters.reads h) (TheLetters.shared h O)
    (TheLetters.last h P) R hR
    (ProofFile.Honest.K12.AtFile.ownLast P.ownMany.toRun.toTest () (TheLetters.lastFront h))
    (fun τ => TheLetters.lastFront h +
      ProofFile.Honest.K12.seedRound P.ownMany.toRun.toTest.p.nums.stages τ) rfl rfl rfl
    (ProofFile.Honest.K1.treesFixed_first h.head made)

end AtFullSide.Honest

#print axioms AtFullSide.Honest.doorFive_at_the_letters
#print axioms AtFullSide.Honest.doorTrees_at_the_letters
#print axioms AtFullSide.Honest.doorFive_at_the_letters_atRun
#print axioms AtFullSide.Honest.doorTrees_at_the_letters_atRun
