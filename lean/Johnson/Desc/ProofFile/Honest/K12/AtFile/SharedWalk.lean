-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/SharedWalk.lean: NOT IN FRONT OF A LAW OVER COINS. What a
member of a shared thread pays at the letter that keeps the field, from what the kind states.

  WalkFacts            what the thread's public lists and the prover's halves give once for all members
  said_of_trees        the letter is carried over a member, from its new trees
  paid_of_five         MemberPaid at the letter, from the five and the new trees
  paid_in_eight        MemberPaid at each of K14's eight members, from K14Asks, where no rider is asked

By what. saidNext_field (Honest/Thread/SaidField.lean), k14_asks, k14_behind (Honest/K14/Asks.lean),
made_next (Honest/Thread/MadeLaw.lean).

Limits. Nothing says that the thread stands. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.ThruWalk
import Johnson.Desc.ProofFile.Honest.Thread.SaidField
import Johnson.Desc.ProofFile.Honest.Thread.MadeLaw
import Johnson.Desc.ProofFile.Honest.K14.Asks
import E2E.NoStop

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block)

section
variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-- **What a thread's public lists and its prover's halves give once for all members.** -/
structure WalkFacts (n : Nat) : Prop where
  fits : T.fits n = true
  shaped : ∀ x ∈ T.bs, x.planOk = true ∧ x.shaped = true
  stops : AtPublicFiles.Stops.NoStop T.hs
  opens : ∀ b, b ≤ n → T.opensAvailable b = true
  depths : ∀ b, b ≤ n → ∀ (k : Coins Bk) (m : Mid W X), DepthsAt T b k m

variable {T}

/-- **The letter is carried over a member, from its new trees.** -/
theorem said_of_trees {n b : Nat} (F : WalkFacts T n) (hb : b < n)
    (hT : TreesNext T (SaidField T BaseNil) b) : SaidNext T (SaidField T BaseNil) b :=
  saidNext_field T F.fits (Nat.le_of_lt hb) hT (baseNil_kept T b) (F.opens _ hb) (F.depths _ hb)

/-- **MemberPaid at the letter, from the five.** -/
theorem paid_of_five {n b : Nat} (F : WalkFacts T n) (hb : b < n)
    (hT : TreesNext T (SaidField T BaseNil) b)
    (hP : PlaysS T (SaidField T BaseNil) b)
    (hA : AcceptedS T (SaidField T BaseNil) (fun _ _ _ => none) b)
    (hB : BehindS T (SaidField T BaseNil) b) (hX : ExchangeS T (SaidField T BaseNil) b)
    (hR : RidesPastS T (SaidField T BaseNil) b) : MemberPaid T (SaidField T BaseNil) b :=
  ⟨said_of_trees F hb hT, hP, hA, hB, hX, hR, made_next T F.fits F.shaped b⟩

end

namespace K14
open OnBytes (TableKey)
open Desc.K14 (St P14)

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ P₁ Cl Wt : Type} {ℓ : WitLens Wt}
  {L : SharedThread.Letters Bk St Cl W₀ Rc TableKey X₀ P₁ Wt} {Q : P14}

/-- **MemberPaid at a member of the eight**, where the letter rides says nothing. -/
theorem paid_in_eight {sentU layO c tests last A weights rand}
    (h : K14Asks ℓ L Q sentU layO c tests last A weights rand)
    (hr : ∀ b w s, L.thread.rides b w s ↔ ridersOf ([] : List (RiderCl (Common W₀ Rc TableKey) St)) b w s)
    {n : Nat} (F : WalkFacts L.thread n) {b : Nat} (h1 : 1 ≤ b) (h8 : b ≤ 8) (hb : b < n) :
    MemberPaid L.thread (SaidField L.thread BaseNil) b := by
  obtain ⟨hP, -, hX, hR, hAc⟩ := k14_asks h (fun _ _ _ => none) b h1 h8
  have hB := k14_behind h hr b h1 h8 (fun _ hy => absurd hy List.not_mem_nil)
    (fun _ hy => absurd hy List.not_mem_nil)
  have hPS := playsS_of _ (SaidField L.thread BaseNil) hP
  exact paid_of_five F hb
    (treesNext_of_playsS _ hPS fun blk _ m ds => AtPublicFiles.Stops.chainStopAt_none _ F.stops [blk] _ _)
    hPS (acceptedS_of _ _ hAc) (behindS_of _ _ hB) (exchangeS_of _ _ hX) (ridesPastS_of _ _ hR)

end

end K14

end ProofFile.Honest

#print axioms ProofFile.Honest.WalkFacts
#print axioms ProofFile.Honest.said_of_trees
#print axioms ProofFile.Honest.paid_of_five
#print axioms ProofFile.Honest.K14.paid_in_eight
