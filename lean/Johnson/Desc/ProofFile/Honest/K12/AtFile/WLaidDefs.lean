-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WLaidDefs.lean: the terms of the last chain's thread at W, definitions
alone: no law stands here, and this file imports no file of laws on these terms.

  `lastTable`      a source's table at the last chain
  `lastFixed`      after how many challenges a source's table changes no more
  `ownLast`        the last chain's own trees
  `takenLast`      the trees that the last chain takes over
  `lastLettersOf`  the value of `LastLetters` at these terms

Limits. Definitions. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.ScriptLots
import Johnson.Desc.K12.Law.PlacesFull
import Johnson.Desc.ProofFile.Honest.Thread.TheLaterThreads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Third (S₃)
open ProofFile.Honest.K12 (TestJob testTbl seedRound)
open ProofFile.Honest.FirstThread (LastLetters)
open H2K.Member (piWFull)

section
variable {Bk : ProverCoinCounts} {W₃ W₂ : Type}

/-- **A source's table at the last chain.** -/
def lastTable (r₁ : ℕ) (toCommon : W₃ → W₂)
    (tb₁ : Fmt.TreeSource → Coins Bk → W₃ → List Fmt.Drawn → Place × Table)
    (tb₂ : Fmt.TreeSource → Coins Bk → W₂ → List Fmt.Drawn → Place × Table)
    (own : ℕ → Coins Bk → W₃ → List Fmt.Drawn → Place × Table) :
    Fmt.TreeSource → Coins Bk → W₃ → List Fmt.Drawn → Place × Table
  | .own n => own n
  | .taken 0 j => tb₁ (.own j)
  | .taken _ j => fun k w h => tb₂ (.own j) k (toCommon w) (h.drop r₁)

/-- **After how many challenges a source's table at the last chain changes no more.** -/
def lastFixed (r₁ : ℕ) (fx₁ fx₂ : Fmt.TreeSource → ℕ) (own : ℕ → ℕ) : Fmt.TreeSource → ℕ
  | .own n => own n
  | .taken 0 j => fx₁ (.own j)
  | .taken _ j => r₁ + fx₂ (.own j)

/-- The last chain's own trees: its test's tree number τ. n₀: the challenges in front of the test. -/
def ownLast {X : Type} (J : TestJob W₃ X) (own₀ : X) (n₀ : ℕ) :
    ℕ → Coins Bk → W₃ → List Fmt.Drawn → Place × Table :=
  testTbl 2 J own₀ n₀ fun _ _ _ => true

end

/-- The trees that the last chain takes over. -/
def takenLast : List Fmt.TreeSource := piWFull.nums.first.map (·.2)

section
variable {W₀ Rc Tr X₀ X W₂ : Type} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **The value of `LastLetters` at these terms.** -/
def lastLettersOf (r₁ n₀ : ℕ) (toCommon : Local W₀ Rc ProofFile.Inst Tr → W₂)
    (tb₁ : Fmt.TreeSource → Coins A.B → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → Place × Table)
    (tb₂ : Fmt.TreeSource → Coins A.B → W₂ → List Fmt.Drawn → Place × Table)
    (fx₁ fx₂ : Fmt.TreeSource → ℕ) (J : TestJob (Local W₀ Rc ProofFile.Inst Tr) X) (own₀ : X)
    (ends : Coins A.B → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn →
      (ProofFile.InstPub × P5J.TS) × Desc.K14.St)
    (riders : List (RiderCl (Local W₀ Rc ProofFile.Inst Tr) S₃)) (keeps : Place → S₃ → S₃ → Prop)
    (hdep : ∀ d ∈ A.F.second.blocksInOrder.flatMap (·.rounds), ∀ o ∈ d.opens, ∀ k w h,
      (lastTable r₁ toCommon tb₁ tb₂ (ownLast J own₀ n₀) o.2 k w h).2.logLength = o.1.a) :
    LastLetters A where
  taken := takenLast
  ends := ends
  table := lastTable r₁ toCommon tb₁ tb₂ (ownLast J own₀ n₀)
  tableDepths := hdep
  fixed := lastFixed r₁ fx₁ fx₂ fun τ => n₀ + seedRound J.p.nums.stages τ
  riders := riders
  keeps := keeps

end

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.lastTable
#print axioms ProofFile.Honest.K12.AtFile.lastFixed
#print axioms ProofFile.Honest.K12.AtFile.ownLast
#print axioms ProofFile.Honest.K12.AtFile.takenLast
#print axioms ProofFile.Honest.K12.AtFile.lastLettersOf
