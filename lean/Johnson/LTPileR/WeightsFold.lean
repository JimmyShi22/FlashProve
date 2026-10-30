-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LTPileR/WeightsFold.lean: THE FOLD'S FACT FOR "K13.weightsOk": at every
state that a fold over a front stretch of the request's own chain returns from the chain's own
start, every weight vector of every row on the table passes `Tensor.ok` (`First.weightsB`,
Johnson/Desc/First/Pend/WeightsB.lean).

Main names (namespace `Meaning.K2`).
  `WeightsOk s` := `weightsB s = true`. **`weights_pileLaw`** : `PileLaw WeightsOk`
    (PileSeat.lean): same and zero: the test reads the rows alone · push: `clearWith_cases`
    with `Pend.pending_rows_weights_ok` · batch: `weights_atM3`
    (Johnson/Desc/K13/Law/WeightsKept.lean).
  `weights_start`: the chain's own start `ProofFile.startS Z p` meets it, where Z is the computed public
    part (by `pub_start`, Johnson/IMR/RecRun.lean).
  **`descPure_weights`**: `descPure_rides` at this sentence, from the start: NO PREMISE BUT
    `Block.planOk` AT EVERY SUB-PROTOCOL OF THE CHAIN.

WHO SPENDS IT: the door of the last chain (`doorFirstB`'s third test:
Johnson/Desc/Last/DoorTexts.lean), through FoldFacts.weightsOk (Johnson/Desc/First/FoldFacts.lean).
Limits. As PileSeat.lean's. `Tensor.ok` is a test of form on a weight vector; nothing is said
of what the rows claim. Nothing on soundness or on hiding.

-/
import Johnson.LTPileR.PileSeat
import Johnson.IMR.BookSeat
import Johnson.Desc.K13.Law.WeightsKept
import Johnson.Desc.K13.Law.AtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.Last (weights_atM3 weights_rowsB)
open ProofFile (Pub)
open Johnson.Desc.First.Walk

/-- The sentence: every weight vector of every row on the table passes `Tensor.ok`. -/
def WeightsOk (s : S) : Prop := weightsB s = true

theorem weightsOk_same {s s' : S} (h : s'.rows = s.rows) (hw : WeightsOk s) : WeightsOk s' := by
  unfold WeightsOk
  rw [weightsB_same h]
  exact hw

/-- **The sentence meets what the walk asks.** -/
theorem weights_pileLaw : PileLaw WeightsOk where
  same := fun _ _ q hw => weightsOk_same q.1 hw
  zero := fun _ _ _ _ _ h hw => weightsOk_same (openLayZero_rows h).1 hw
  push := fun X counts left lay lin s t h hw => by
    rcases clearWith_cases h with q | ⟨w, r, os, hr, e, -⟩
    · exact weightsOk_same q.1 hw
    · unfold WeightsOk weightsB at hw ⊢
      rw [e, List.all_append, hw]
      simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.true_and, List.all_eq_true]
      exact Pend.pending_rows_weights_ok hr
  batch := fun _ _ _ _ _ h hw => weights_atM3 h hw

/-- The chain's own start meets it, at every public part of an instance. -/
theorem weights_start {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) (p : ProofFile.InstPub) :
    WeightsOk (ProofFile.startS Z p) := by
  have e : weightsB Z.s₀ = true := by
    have k := pub_start h
    unfold S.startP at k
    split at k
    · rw [← Option.some.inj k]
      rfl
    · cases k
  unfold WeightsOk ProofFile.startS
  dsimp only
  split
  · exact e
  · rfl

/-- **THE FOLD's FACT FOR "K13.weightsOk"**: at the IOP as written in Lean for the proof file: where
every sub-protocol of the request's own chain passes its test on the list of rounds: whatever state
a fold over a front stretch of that chain returns from the chain's own start, every weight vector of
every row on its table passes `Tensor.ok`. -/
theorem descPure_weights {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      ((∀ b ∈ c.blocksInOrder, b.planOk = true) → ∀ (k ft : Nat) (p : ProofFile.InstPub) (rs : List Fmt.RoundView)
        (cols : List VerifiableInference.Desc.OpenedColumn)
        (r : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn),
        foldBlocks ft (c.blocksInOrder.take k) (ProofFile.startS Z p) rs cols = .ok r → weightsB r.1 = true) := by
  obtain ⟨Z, A, B, c, h1, h2, k⟩ := descPure_rides weights_pileLaw h
  exact ⟨Z, A, B, c, h1, h2, fun hp n ft p rs cols r hf =>
    k hp n ft _ rs cols r hf (weights_start h1 p)⟩

#print axioms weightsOk_same
#print axioms weights_pileLaw
#print axioms weights_start
#print axioms descPure_weights

end Meaning.K2
