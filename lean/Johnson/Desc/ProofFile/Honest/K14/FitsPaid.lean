-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/FitsPaid.lean: kind K14: WHAT WAS PLAYED AND READ PASSES THE
STEP's OWN TESTS ON ROUNDS AND COLUMNS (FitsAt, Honest/Thread/Shape.lean), at the kind's own six
members, general in the thread. By the frame's own law where a half stands (fitsAt_half,
Honest/Thread/ShapeRow.lean); at a member without a round by unfolding.

  fitsAt_found    FitsAt where a half with the member's number of rounds is found at whatever stands
                  at the number b, and that sub-protocol states a list of oracle messages a round
  fitsAt_none     FitsAt where whatever stands at the number b declares no round
  quiet_Fits, split_Fits   so from AtQuiet | AtSplit (Honest/K14/Paid.lean)
  six_Fits        **FitsAt at all six of the kind's own members**, from AtEight alone: whether the
                  shape splits or not

What is not claimed. That AtEight holds at the shared chain's thread of the IOP as written in Lean.
That a member's decide function returns. Nothing on soundness or on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.PaidQuiet
import Johnson.Desc.ProofFile.Honest.Thread.ShapeRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block Place OpenedColumn)
open Desc.K14 (P14 St blocks)

variable {Bk : ProverCoinCounts} {S Cl V W X Pb W₀ Rc Ky : Type}

/-- FitsAt where a half with the member's number of rounds is found. General in the thread. -/
theorem fitsAt_found {T : Thread Bk S Cl V W X Pb} {b : Nat}
    (h : ∀ blk, T.bs[b]? = some blk → ∃ g, (T.hs.find? fun g => g.place == blk.place) = some g ∧
      g.rounds = blk.rounds.length ∧ blk.oracles.length = blk.rounds.length) : FitsAt T b :=
  fun blk hblk => by
    obtain ⟨g, hf, hr, ho⟩ := h blk hblk
    exact fitsAt_half T hblk hf hr ho blk hblk

/-- FitsAt where whatever stands at the number b declares no round. General in the thread. -/
theorem fitsAt_none {T : Thread Bk S Cl V W X Pb} {b : Nat}
    (h : ∀ blk, T.bs[b]? = some blk → blk.rounds = []) : FitsAt T b := by
  intro blk hblk k m E ds y cols hd hMv
  have hr := h blk hblk
  unfold Thread.Moved at hMv
  obtain ⟨⟨l, hl, hy⟩, hc⟩ := hMv
  have hl0 : l = [] := by
    have e := steps_decl hl
    rw [List.flatMap_cons, List.flatMap_nil, List.append_nil, hr] at e
    exact List.map_eq_nil_iff.1 e
  have hd0 : ds = [] := by
    have e := drawsFit_length _ _ hd
    rw [hr] at e
    exact List.eq_nil_of_length_eq_zero e
  subst hl0
  subst hd0
  have ey : (([], m) : List Played × Mid W X) = y := Except.ok.inj hy
  subst ey
  rw [hr] at hc
  have ec : ([] : List OpenedColumn) = cols := Except.ok.inj hc
  subst ec
  unfold Block.Fits Block.want
  rw [hr]
  exact ⟨rfl, rfl⟩

variable {T : Thread Bk S Cl Empty (Common W₀ Rc Ky) X Pb} {b : Nat} {A : Data}
  {weights : W₀ → Weights}

/-- FitsAt at a member with a quiet half. -/
theorem quiet_Fits (h : AtQuiet T b A weights) : FitsAt T b :=
  fitsAt_found fun blk hblk => by
    obtain ⟨d, hr, ho, -⟩ := h.member blk hblk
    exact ⟨_, h.half blk hblk, by rw [hr]; rfl, by rw [hr, ho]; rfl⟩

/-- FitsAt at "SPLIT". -/
theorem split_Fits (h : AtSplit T b A weights) : FitsAt T b :=
  fitsAt_found fun blk hblk => by
    obtain ⟨d, hr, ho, -⟩ := h.member blk hblk
    exact ⟨_, h.half blk hblk, by rw [hr]; rfl, by rw [hr, ho]; rfl⟩

variable {b0 : Nat} {P : P14}

/-- **FitsAt at all six of the kind's own members**, whether the shape splits or not. -/
theorem six_Fits (h : AtEight T b0 P A weights) :
    FitsAt T b0 ∧ FitsAt T (b0 + 2) ∧ FitsAt T (b0 + 3) ∧ FitsAt T (b0 + 5) ∧ FitsAt T (b0 + 6) ∧
      FitsAt T (b0 + 7) := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, hb, hm⟩ := h.eight
  obtain ⟨r3, -, r6, -, h8⟩ := declares_none P b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨-, -, -, -, -, r4, o4, -⟩ := declares3 P b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨-, p4, -⟩ := places4 P b1 b2 b3 b4 b5 b6 b7 b8 hb
  refine ⟨quiet_Fits (atPoint_of h), fitsAt_none fun blk hblk => (hm 2 b3 rfl blk hblk).1.trans r3,
    fitsAt_found fun blk hblk => ?_, fitsAt_none fun blk hblk => (hm 5 b6 rfl blk hblk).1.trans r6,
    quiet_Fits (atZeta_of h), ?_⟩
  · obtain ⟨hr, ho, hp⟩ := hm 3 b4 rfl blk hblk
    refine ⟨{ place := place 4, parts := [liftK14 A weights quietPart] }, ?_, ?_, ?_⟩
    · rw [hp, p4]
      exact h.found { place := place 4, parts := [liftK14 A weights quietPart] }
        (by rw [halves_eq]; simp)
    · rw [hr, r4]
      rfl
    · rw [hr, ho, r4, o4]
      rfl
  · cases hS : P.S.sharedSplitNeeded with
    | true => exact split_Fits (atSplit_of h hS)
    | false => exact fitsAt_none fun blk hblk => (hm 7 b8 rfl blk hblk).1.trans (h8 hS).1

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.six_Fits
#print axioms ProofFile.Honest.K14.fitsAt_found
#print axioms ProofFile.Honest.K14.fitsAt_none
#print axioms ProofFile.Honest.K14.quiet_Fits
#print axioms ProofFile.Honest.K14.split_Fits
