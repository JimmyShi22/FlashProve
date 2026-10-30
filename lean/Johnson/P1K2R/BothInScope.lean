-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/BothInScope.lean (over Johnson/LTPileR/TwoStarts.lean and
  the law files Johnson/Top/H0/K2Hands/BothFrontS.lean and SampleReach.lean): THE TWO INVARIANTS
  ON THE STORED SAMPLE ROWS HOLD AT EVERY REACHED STATE IN FRONT OF THE LAST CODE SWITCH, at the
  first chain of the proof file's IOP as written in Lean. One theorem: a join; it has no premise
  but that `ProofFile.onlineDescription` returns F and F.planOk = true.

Main names (namespace `P1K2`).
  `both_in_scope`: F is `fileDescBy … c`; at every cut k in front of the last code switch, at
    every state that `Reach` has at k over c's own sub-protocols (each beneath `below`) from
    `ProofFile.startS Z`: `K2.SampleGoodS s.st` and `K2.AnsweredStored s.st`. `RchAt F k a`
    (Johnson/Top/H0/Walk/ReachAt.lean) unfolds to that `Reach`. By `keepsBoth_front` (every lot
    keeps both), `both_of_reach` (the walk), `LTPile.rowsInv_startS`, `LTPile.answered_startS`
    (the start holds no oracle message).
Limits. It speaks of the verifier's state's statement; the front that the code switch's text makes
  of the state has another statement (with the same oracle messages and codes): that step is not
  here. Nothing on soundness or on hiding.

-/
import Johnson.LTPileR.TwoStarts
import Johnson.Top.H0.K2Hands.BothFrontS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach)
open Meaning.K2 (frontOf)

/-- **Both invariants at every reached state in front of the last code switch.** -/
theorem both_in_scope {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) (hpl : F.planOk = true) :
    ∃ (Z : ProofFile.Pub) (c : Chain S ProofFile.Cl) (A : ProofFile.SharedSeat) (B' : ProofFile.SecondSeat),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B' (fun s => s) (ProofFile.startS Z) c ∧
      (frontOf c).length = 14 * (ProofFile.subsOf Z).length + 3 ∧
      ∀ k, k ≤ (frontOf c).length → ∀ (z : ProofFile.InstPub) (s : S),
        Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k (z, s) →
        K2.SampleGoodS s.st ∧ K2.AnsweredStored s.st := by
  obtain ⟨Z, c, A, B', hZ, hE, -, hlen, hall⟩ := K2.keepsBoth_front h hpl
  exact ⟨Z, c, A, B', hZ, hE, hlen, fun k hk z s hr =>
    K2.both_of_reach (hall k hk) ((K2.sampleGoodS_iff _).2 (LTPile.rowsInv_startS hZ _ z))
      (LTPile.answered_startS hZ z) hr⟩

#print axioms both_in_scope

end P1K2
