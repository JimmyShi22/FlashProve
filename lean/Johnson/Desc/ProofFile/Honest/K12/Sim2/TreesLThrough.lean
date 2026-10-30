-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the two sides of trees_first, read through.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/TreesLThrough.lean: the online filling reads the kinds' sides
through a pair of total maps on the input (OnlineProverParts.through, Honest/ThruK13.lean). So its sides at the
finish of the code switch and at the first chain's last test are Placed.thru of the lots' own. Here:
the finish's half read through is the finish's half at the readers read through; a job read through
(TestJob.through) is jobL at the readers and the door read through; and the test's pair read through
is the pair of the job read through. So trees_first (Sim2/TreesL.lean) speaks of these sides too.
And the closing that the kind K2's own list lays is lotClosingAt, by text. Equations of definitions.
No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.TreesL
import Johnson.Desc.ProofFile.Honest.Thru
import Johnson.Desc.ProofFile.Honest.K2.Exact

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Sim2
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof

/-! ## 1 The finish of the code switch -/

/-- The kind K2's own list lays the closing lotClosingAt. -/
theorem switchLot_halves {W₀ Rc Xi Tr X : Type} (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (Z : Pub) (G : Ground) :
    (K2.switchLot (X := X) D readers).halves Z G =
      K2.switchHalves (K2.coreSender K2.freshTable) D readers
        (K2.lotClosingAt G.first.layout (K2.segmentsOf Z G)) Z G := rfl

/-- **The finish's half read through** is the finish's half at the readers read through. -/
theorem switchHalf_through {W₀ W₀' Rc Rc' Xi Tr Y : Type} (g : W₀' → W₀) (rd : Rc' → Rc)
    (Sd : K2.Sender) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : K2.Closing) (p : K2.SwitchPlace) :
    Placed.thru (Local.thru g rd) (Local.thru g rd)
        (K2.switchHalf (X := Y) Sd D readers closing p) =
      K2.switchHalf Sd D (readers ∘ Local.thru g rd) closing p :=
  congrArg (fun q => (⟨p.place, [q]⟩ : Placed _ _ Y))
    (Part.lift_thru (Local.thru g rd) (Local.thru g rd) (fun _ => ())
      (K2.switchWit D readers closing p) (fun _ => ()) (fun x _ => x)
      (K2.switchPart Sd p.sizes p.others p.foldVars p.carries))

/-! ## 2 The job -/

variable {V V' W W' X C : Type}

/-- **A job read through**: its three functions read the input through wit. -/
def _root_.ProofFile.Honest.K12.TestJob.through (wit : W' → W) (J : TestJob W X) : TestJob W' X :=
  ⟨J.p, J.members, J.fresh, fun w fr => J.rec₀ (wit w) fr, fun w fr mem => J.rows₀ (wit w) fr mem,
    fun w fr mem P => J.trees₀ (wit w) fr mem P⟩

/-- jobL read through is jobL at the door and the readers read through. -/
theorem jobL_through {W₀ W₀' Rc Rc' Xi Tr : Type} (g : W₀' → W₀) (rd : Rc' → Rc)
    (q : VerifiableInference.Desc.K12.P12)
    (door : Local W₀ Rc Xi Tr → Front X → VerifiableInference.Desc.K12.T12) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : K2.Closing) (p : K2.SwitchPlace) :
    (jobL q door D readers closing p).through (Local.thru g rd) =
      jobL q (fun w fr => door (Local.thru g rd w) fr) D (readers ∘ Local.thru g rd) closing p :=
  rfl

/-- A move of the test read through is the move of the job read through. -/
theorem moveAt_through (wit : W' → W) (J : TestJob W X) (rd : C → TestCoins) (i : ℕ) :
    Move.lift wit id (fun _ y => y) (moveAt J rd i) = moveAt (J.through wit) rd i := rfl

theorem movesFrom_through (wit : W' → W) (J : TestJob W X) (rd : C → TestCoins) (a n : ℕ) :
    (movesFrom J rd a n).map (Move.lift wit id fun _ y => y) =
      movesFrom (J.through wit) rd a n := by
  unfold movesFrom
  rw [List.map_map]
  rfl

/-- **The second part read through** is the second part of the job read through. -/
theorem restPart_through (see : V' → V) (wit : W' → W) (J : TestJob W X) :
    Part.thru see wit (restPart J : Part V W X) = restPart (J.through wit) := by
  obtain ⟨p, mem, fr, r, ro, tr⟩ := J
  unfold Part.thru Part.lift restPart
  dsimp only [TestJob.through]
  congr 1
  rw [List.map_append, List.map_flatMap]
  refine congrArg₂ (· ++ ·) ?_ (movesFrom_through wit _ _ _ _)
  refine flatMap_congr_mem _ _ _ fun j _ => ?_
  show List.map _ (_ ++ _) = _
  rw [List.map_append]
  refine congrArg₂ (· ++ ·) ?_ (movesFrom_through wit _ _ _ _)
  split
  · rfl
  · exact movesFrom_through wit _ _ _ _

/-- **The first part read through** is the first part of the job read through. -/
theorem firstPart_through (see : V' → V) (wit : W' → W) (J : TestJob W X) :
    Part.thru see wit (firstPart J : Part V W X) = firstPart (J.through wit) := by
  obtain ⟨p, mem, fr, r, ro, tr⟩ := J
  cases fr with
  | none =>
    unfold Part.thru Part.lift firstPart
    dsimp only [TestJob.through]
    congr 1
    exact movesFrom_through wit _ _ _ _
  | some f =>
    unfold Part.thru Part.lift firstPart
    dsimp only [TestJob.through]
    congr 1
    exact movesFrom_through wit _ _ _ _

/-- **The test's pair read through** is the pair of the job read through. -/
theorem testHalf_through (see : V' → V) (wit : W' → W) (J : TestJob W X) :
    Placed.thru see wit (proverSideOfProximityTest J : Placed V W X) = proverSideOfProximityTest (J.through wit) := by
  unfold Placed.thru proverSideOfProximityTest
  dsimp only [List.map_cons, List.map_nil]
  rw [firstPart_through, restPart_through]
  rfl

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.switchLot_halves
#print axioms ProofFile.Honest.K12.Sim2.switchHalf_through
#print axioms ProofFile.Honest.K12.Sim2.jobL_through
#print axioms ProofFile.Honest.K12.Sim2.moveAt_through
#print axioms ProofFile.Honest.K12.Sim2.restPart_through
#print axioms ProofFile.Honest.K12.Sim2.firstPart_through
#print axioms ProofFile.Honest.K12.Sim2.testHalf_through
