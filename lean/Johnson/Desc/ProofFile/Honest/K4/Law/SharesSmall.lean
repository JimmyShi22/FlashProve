-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K4/Law/SharesSmall.lean: CONDITIONAL.

What is here. K4's two records in the list of falls and marks pass the public test on a stated share, at
each of the twelve members: the two sides of `shareSmall` (E2E/TheFallsSum.lean): 0 < den and
num * 2 ^ 109 ≤ den.

  `k4WideRounds_le_rounds`   the mark's listed rounds are at most the member's rounds
  `k4Rounds_le`              under the head the member has at most 2 ^ 20 rounds: the written cut
  `k4_shares_small`          **`k4Fall`'s and `k4MarkWide`'s shares pass the test**

Limits. A statement on two numbers, under the head: nothing on what the tests say at a run, or on
whether a stated share is the chance of its event. Full size alone, the format's second hash function alone.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.MarkWideCount
import Johnson.Desc.ProofFile.Honest.K4.Law.FrontCount
import Johnson.Desc.ProofFile.Honest.K4.Law.TableFitsMember
import Johnson.Road.K4.K4CutRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes.Desc.First.K4 (Par entries rounds)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Block)
open VerifiableInference.PlanWritten (cutFirstFull cutOf)
open P5J (AtMgA TS)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

/-- The mark's listed rounds are at most the member's rounds. -/
theorem k4WideRounds_le_rounds (Q : K4Pub) :
    (k4WideRounds Q).length ≤ (rounds Q.P Q.hp Q.g).length := by
  have o : ∀ n, k4One n ≤ 1 := fun n => by
    unfold k4One
    split <;> omega
  have a := o Q.P.y.h.lt
  have b := o (Q.P.y.ls + Q.P.y.h.lt)
  have c := o (Q.P.y.lPd - Q.P.y.ls)
  have d := o Q.P.rd.lNI
  have e := o (Q.P.y.h.ll - 1)
  rw [k4WideRounds_length, OnBytes.Road.K4.rounds_len]
  split <;> omega

/-- No member of the written first chain has more than 2 ^ 20 rounds. -/
theorem cutFirst_rounds_small : cutFirstFull.all (fun r => decide (r.2.2.1 ≤ 2 ^ 20)) = true := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL on h and Lh. **K4's member has at most 2 ^ 20 rounds.** -/
theorem k4Rounds_le (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ} {x : Bool × Par}
    {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk) :
    (rounds (k4PubAt cF k x).P (k4PubAt cF k x).hp (k4PubAt cF k x).g).length ≤ 2 ^ 20 := by
  have hr : blk.rounds = (entries (k4PubAt cF k x).P (k4PubAt cF k x).hp (k4PubAt cF k x).g).map
      fun e => ({ entry := e } : Fmt.DeclaredRound) := by
    rw [IM.alone_rounds Lh.laid]
    rfl
  have hl : (rounds (k4PubAt cF k x).P (k4PubAt cF k x).hp (k4PubAt cF k x).g).length =
      blk.rounds.length := by
    rw [hr, List.length_map, OnBytes.Road.K4.entries_len]
  rw [hl]
  have hc := OnBytes.Road.K4.cut_of_head h.toAtMg
  have hm : blk ∈ cF.blocksInOrder := List.mem_of_getElem? Lh.member
  have hw : ∃ w ∈ cutFirstFull, w.2.2.1 = blk.rounds.length := by
    rw [← hc]
    unfold cutOf
    exact ⟨_, List.mem_map.2 ⟨blk, hm, rfl⟩, rfl⟩
  obtain ⟨w, hw, e⟩ := hw
  rw [← e]
  exact of_decide_eq_true (List.all_eq_true.1 cutFirst_rounds_small w hw)

/-- CONDITIONAL on h and Lh. **K4's fall and K4's wider mark at the member pass the test on a stated
share.** A statement on two numbers: nothing on the tests at a run. -/
theorem k4_shares_small (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ} {x : Bool × Par}
    {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk) {S : Type} :
    (0 < (k4Fall (S := S) (k4PubAt cF k x)).share.den ∧
      (k4Fall (S := S) (k4PubAt cF k x)).share.num * 2 ^ 109 ≤
        (k4Fall (S := S) (k4PubAt cF k x)).share.den) ∧
      0 < (k4MarkWide (k4PubAt cF k x)).share.den ∧
      (k4MarkWide (k4PubAt cF k x)).share.num * 2 ^ 109 ≤
        (k4MarkWide (k4PubAt cF k x)).share.den := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · show 0 < k4CoinZeroShare.den
    decide +kernel
  · show k4CoinZeroShare.num * 2 ^ 109 ≤ k4CoinZeroShare.den
    decide +kernel
  · show 0 < Code.pGold ^ 3 * (2 ^ 128) ^ 3
    decide +kernel
  have hL : (k4WideRounds (k4PubAt cF k x)).length ≤ 2 ^ 20 :=
    (k4WideRounds_le_rounds _).trans (k4Rounds_le h Lh)
  show 2 * (k4WideRounds (k4PubAt cF k x)).length * (2 ^ 128 + 1) ^ 3 * 2 ^ 109 ≤
    Code.pGold ^ 3 * (2 ^ 128) ^ 3
  have e1 : 2 * (k4WideRounds (k4PubAt cF k x)).length * (2 ^ 128 + 1) ^ 3 * 2 ^ 109 ≤
      2 * 2 ^ 20 * (2 ^ 128 + 1) ^ 3 * 2 ^ 109 :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hL))
  exact e1.trans (by decide +kernel)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4WideRounds_le_rounds
#print axioms ProofFile.Honest.K4.cutFirst_rounds_small
#print axioms ProofFile.Honest.K4.k4Rounds_le
#print axioms ProofFile.Honest.K4.k4_shares_small
