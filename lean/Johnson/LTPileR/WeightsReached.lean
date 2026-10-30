-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LTPileR/WeightsReached.lean:
THE FOLD'S FACTS OF PileSeat.lean AND WeightsFold.lean AT "REACHED" (`Reach`,
Johnson/Top/H0/Walk/Reach.lean): one call each.

Main names (namespace `Meaning.K2`).
  **`reach_rides`**: under `PileLaw P`, at the IOP as written in Lean for the proof file (F =
    `fileDescBy … c`), where every sub-protocol of `c.blocksInOrder` passes `Block.planOk` and the chain's
    own start meets P at every public part: P holds at every state that is reached along `c.blocksInOrder`
    from that start.
  **`reach_weights`**: so `First.weightsB` holds at every reached state: no premise but
    `Block.planOk`.
  **`weightsOk_field`**: the same in the letters of the structure of fold facts
    (Johnson/Desc/First/FoldFacts.lean: not imported): for every Rch and at_ such that whatever Rch
    holds is reached along the chain at at_'s state (hR): ∀ k a, Rch k a → (at_ a).2.failed = none →
    weightsB (at_ a).2 = true. `fileDescBy_first`: the value's first chain is c and its start
    `ProofFile.startS Z`, by the make: so at `RchAt F` (Walk/ReachAt.lean) hR is that definition unfolded.

Every "there is": Z, A, B, c: as in PileSeat.lean.
Limits. "Reached" binds its rounds and columns inside a "there are": nothing is concluded here about
them. It does not ask that the state bears no mark: the facts hold at a marked state too. Nothing on
soundness or on hiding.

-/
import Johnson.LTPileR.WeightsFold
import Johnson.Top.H0.Walk.Reach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open ProofFile (Pub)
open Johnson.Desc.First.Walk.Tied (Reach)

/-- **A sentence on the pile, at every reached state.** -/
theorem reach_rides {P : S → Prop} (L : PileLaw P) {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {F : FileDescription ProofFile.Inst} (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      ((∀ b ∈ c.blocksInOrder, b.planOk = true) → (∀ p, P (ProofFile.startS Z p)) →
        ∀ (ft k : Nat) (a : ProofFile.InstPub × S), Reach ft c.blocksInOrder (ProofFile.startS Z) k a → P a.2) := by
  obtain ⟨Z, A, B, c, h1, h2, k⟩ := descPure_rides L h
  refine ⟨Z, A, B, c, h1, h2, fun hp h0 ft n a hr => ?_⟩
  obtain ⟨-, rs, cols, hf⟩ := hr.fold
  exact k hp n ft _ rs cols _ hf (h0 a.1)

/-- **THE FIELD FOR "K13.weightsOk", AT "REACHED".** -/
theorem reach_weights {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      ((∀ b ∈ c.blocksInOrder, b.planOk = true) → ∀ (ft k : Nat) (a : ProofFile.InstPub × S),
        Reach ft c.blocksInOrder (ProofFile.startS Z) k a → weightsB a.2 = true) := by
  obtain ⟨Z, A, B, c, h1, h2, k⟩ := reach_rides weights_pileLaw h
  exact ⟨Z, A, B, c, h1, h2, fun hp => k hp (weights_start h1)⟩

/-- The first chain and its start, of the value that `fileDescBy` makes. -/
theorem fileDescBy_first (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : Pub) (A : ProofFile.SharedSeat)
    (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl) :
    (ProofFile.fileDescBy o mk Z A B (fun s => s) (ProofFile.startS Z) c).first = c ∧
      (ProofFile.fileDescBy o mk Z A B (fun s => s) (ProofFile.startS Z) c).start₁ = ProofFile.startS Z :=
  ⟨rfl, rfl⟩

/-- **THE FIELD IN THE LETTERS OF THE TABLES' OWNER's STRUCTURE OF FOLD FACTS** (general in Rch and
at_): hR: whatever Rch holds is reached along the chain from its own start, at at_'s state. -/
theorem weightsOk_field {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      ((∀ b ∈ c.blocksInOrder, b.planOk = true) → ∀ {X Pp : Type} (Rch : Nat → X → Prop)
        (at_ : X → Pp × S),
        (∀ k a, Rch k a → ∃ ft z, Reach ft c.blocksInOrder (ProofFile.startS Z) k (z, (at_ a).2)) →
        ∀ k a, Rch k a → (at_ a).2.failed = none → weightsB (at_ a).2 = true) := by
  obtain ⟨Z, A, B, c, h1, h2, k⟩ := reach_weights h
  refine ⟨Z, A, B, c, h1, h2, fun hp X Pp Rch at_ hR n a ha _ => ?_⟩
  obtain ⟨ft, z, hr⟩ := hR n a ha
  exact k hp ft n _ hr

#print axioms reach_rides
#print axioms reach_weights
#print axioms fileDescBy_first
#print axioms weightsOk_field

end Meaning.K2
