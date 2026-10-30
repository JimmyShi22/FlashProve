-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/PaidQuiet.lean: kind K14: Plays (Honest/Thread/Pays.lean) AT THE
KIND's MEMBERS THAT HAVE NO ROUND: "(rec_gamma)" and "joins"; and "SPLIT" where the shape does not
split. By the frame's own law for such members (plays_quiet, Honest/Thread/QuietLaw.lean).

  declares_none   "(rec_gamma)" and "joins" declare no round and state no oracle message; so does
                  "SPLIT" where the shape does not split
  none_Plays      whatever stands at a number of the thread's list and declares no round and no
                  oracle message: Plays there
  six_Play        **Plays at all six of the kind's own members**, from AtEight and, for "LOC", the
                  columns: whether the shape splits or not

The two other members of the eight are the two sendings: not here.

What is not claimed. That AtEight holds at the shared chain's thread of the IOP as written in Lean.
The other sentences that a thread asks at a member. Nothing on soundness or on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.PaidAt
import Johnson.Desc.ProofFile.Honest.Thread.QuietLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block Place)
open Desc.K14 (P14 St blocks)

variable {Bk : ProverCoinCounts} {S Cl W₀ Rc Ky X Pb : Type}

/-- **What "(rec_gamma)" and "joins" declare: nothing**; and "SPLIT" where the shape does not
split. -/
theorem declares_none (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    b3.rounds = [] ∧ b3.oracles = [] ∧ b6.rounds = [] ∧ b6.oracles = [] ∧
      (P.S.sharedSplitNeeded = false → b8.rounds = [] ∧ b8.oracles = []) := by
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hb
  obtain ⟨sentU, hU, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hb
  refine ⟨rfl, rfl, rfl, rfl, fun hS => ⟨?_, ?_⟩⟩
  · unfold Desc.K14.entries Desc.K14.rounds Desc.K14.whys
    simp [hS]
  · simp [hS]

variable {T : Thread Bk S Cl Empty (Common W₀ Rc Ky) X Pb}

/-- Whatever stands at the number b and declares no round and no oracle message: Plays there. -/
theorem none_Plays {b : Nat}
    (h : ∀ blk, T.bs[b]? = some blk → blk.rounds = [] ∧ blk.oracles = []) : Plays T b :=
  fun blk hb => plays_quiet T hb (h blk hb).1 (h blk hb).2 blk hb

variable {b0 : Nat} {P : P14} {A : Data} {weights : W₀ → Weights}

/-- **Plays at all six of the kind's own members**, whether the shape splits or not. -/
theorem six_Play (h : AtEight T b0 P A weights)
    (hcol : ∀ w, T.valid w → ∀ p < 2 ^ (Desc.K14.readsAtLoc P.S.fold P.item).sh.a,
      ∃ u, T.stored w (Desc.K14.readsAtLoc P.S.fold P.item).item p = some u ∧
        u.length = (Desc.K14.readsAtLoc P.S.fold P.item).sh.W) :
    Plays T b0 ∧ Plays T (b0 + 2) ∧ Plays T (b0 + 3) ∧ Plays T (b0 + 5) ∧ Plays T (b0 + 6) ∧
      Plays T (b0 + 7) := by
  obtain ⟨p0, p3, p6⟩ := three_Play h hcol
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, hb, hm⟩ := h.eight
  obtain ⟨r3, o3, r6, o6, h8⟩ := declares_none P b1 b2 b3 b4 b5 b6 b7 b8 hb
  refine ⟨p0, none_Plays fun blk hblk => ?_, p3, none_Plays fun blk hblk => ?_, p6, ?_⟩
  · obtain ⟨hr, ho, -⟩ := hm 2 b3 rfl blk hblk
    exact ⟨hr.trans r3, ho.trans o3⟩
  · obtain ⟨hr, ho, -⟩ := hm 5 b6 rfl blk hblk
    exact ⟨hr.trans r6, ho.trans o6⟩
  · cases hS : P.S.sharedSplitNeeded with
    | true => exact split_Plays (atSplit_of h hS)
    | false =>
      refine none_Plays fun blk hblk => ?_
      obtain ⟨hr, ho, -⟩ := hm 7 b8 rfl blk hblk
      exact ⟨hr.trans (h8 hS).1, ho.trans (h8 hS).2⟩

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.declares_none
#print axioms ProofFile.Honest.K14.none_Plays
#print axioms ProofFile.Honest.K14.six_Play
