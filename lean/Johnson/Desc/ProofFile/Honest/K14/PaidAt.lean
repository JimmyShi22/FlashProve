-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/PaidAt.lean: kind K14: THE PREMISES OF Honest/K14/Paid.lean FOLLOW
FROM FACTS THAT CAN BE READ OFF A THREAD's TWO LISTS.

  AtEight T b0 P A weights   whatever stands at the numbers b0 to b0 + 7 of the thread's list has
                  the rounds, the oracle messages and the place of the like one of the eight
                  sub-protocols that the library makes at the parameters P; the thread's halves
                  stand at different places; the kind's halves are among them; A has P's shape
  places4         the places of the four of the eight that have a round of the kind's own
  AtEight.found   a half of the kind's is found at its place
  atPoint_of, atLoc_of, atZeta_of   so AtQuiet | AtLoc | AtQuiet hold at b0, b0 + 3, b0 + 6: whether
                  the shape splits or not
  atSplit_of      and AtSplit at b0 + 7, where the shape splits
  three_Play, four_Play   **Plays at these members**, from AtEight and, for "LOC", the columns

A member may be wrapped (another type of claims, a guard): AtEight asks its rounds, oracle messages
and place alone. A list that is too short meets AtEight's clause on members for nothing, and Plays
with it. OF A's THREE FIELDS AtEight TIES THE SHAPE ALONE: the two numbers A.atPoint and A.atZeta
are free: Plays says nothing of the value that is sent. Whoever goes on to what a thread asks of
that value needs them to be the numbers of the rounds in front of "LIN point" and "LIN zeta" in the
thread's own list (roundsInFront, Honest/ForKinds.lean).

What is not claimed. That AtEight holds at the shared chain's thread of the IOP as written in Lean
(its clause on members: Honest/K14/PaidFlat.lean). Where the shape does not split, nothing on the
member number b0 + 7. Nothing on soundness or on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.Paid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block Place)
open Desc.K14 (P14 St blocks)
open Desc.K14.Law (entryAt)

variable {Bk : ProverCoinCounts} {S Cl W₀ Rc Ky X Pb : Type}

variable (T : Thread Bk S Cl Empty (Common W₀ Rc Ky) X Pb)

/-- **The kind's eight sub-protocols and its halves stand in the thread's two lists.** -/
structure AtEight (b0 : Nat) (P : P14) (A : Data) (weights : W₀ → Weights) : Prop where
  shape : A.S = P.S
  eight : ∃ b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit,
    blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8] ∧
    ∀ i (c : Block St Unit), [b1, b2, b3, b4, b5, b6, b7, b8][i]? = some c →
      ∀ blk, T.bs[b0 + i]? = some blk →
        blk.rounds = c.rounds ∧ blk.oracles = c.oracles ∧ blk.place = c.place
  apart : (T.hs.map (·.place)).Nodup
  among : ∀ h ∈ (proverSidesOfSharedRounds A weights : List (Placed Empty (Common W₀ Rc Ky) X)), h ∈ T.hs

/-- The places of the four. -/
theorem places4 (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    b1.place = place 1 ∧ b4.place = place 4 ∧ b7.place = place 7 ∧ b8.place = place 8 := by
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hb
  obtain ⟨sentU, hU, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hb
  exact ⟨rfl, rfl, rfl, rfl⟩

variable {T} {b0 : Nat} {P : P14} {A : Data} {weights : W₀ → Weights}

/-- A half of the kind's is found at its place. -/
theorem AtEight.found (h : AtEight T b0 P A weights) (g : Placed Empty (Common W₀ Rc Ky) X)
    (hg : g ∈ (proverSidesOfSharedRounds A weights : List (Placed Empty (Common W₀ Rc Ky) X))) :
    (T.hs.find? fun x => x.place == g.place) = some g :=
  find_of_mem T.hs g h.apart (h.among g hg)

/-- "LIN point" stands at b0. -/
theorem atPoint_of (h : AtEight T b0 P A weights) : AtQuiet T b0 A weights := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, hb, hm⟩ := h.eight
  obtain ⟨h0, -, -, r1, o1, -⟩ := declares3 P b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨p1, -⟩ := places4 P b1 b2 b3 b4 b5 b6 b7 b8 hb
  refine ⟨fun blk hblk => ?_, fun blk hblk => ?_⟩
  · obtain ⟨hr, ho, -⟩ := hm 0 b1 rfl blk hblk
    exact ⟨{ entry := entryAt P 0 }, hr.trans r1, ho.trans o1, h0, rfl, rfl⟩
  · obtain ⟨-, -, hp⟩ := hm 0 b1 rfl blk hblk
    rw [hp, p1]
    exact h.found { place := place 1, parts := [liftK14 A weights quietPart] }
      (by rw [halves_eq]; simp)

/-- "LIN zeta" stands at b0 + 6. -/
theorem atZeta_of (h : AtEight T b0 P A weights) : AtQuiet T (b0 + 6) A weights := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, hb, hm⟩ := h.eight
  obtain ⟨-, -, h2, -, -, -, -, r7, o7⟩ := declares3 P b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨-, -, p7, -⟩ := places4 P b1 b2 b3 b4 b5 b6 b7 b8 hb
  refine ⟨fun blk hblk => ?_, fun blk hblk => ?_⟩
  · obtain ⟨hr, ho, -⟩ := hm 6 b7 rfl blk hblk
    exact ⟨{ entry := entryAt P 2 }, hr.trans r7, ho.trans o7, h2, rfl, rfl⟩
  · obtain ⟨-, -, hp⟩ := hm 6 b7 rfl blk hblk
    rw [hp, p7]
    exact h.found { place := place 7, parts := [liftK14 A weights quietPart] }
      (by rw [halves_eq]; simp)

/-- "SPLIT" stands at b0 + 7, where the shape splits. -/
theorem atSplit_of (h : AtEight T b0 P A weights) (hS : P.S.sharedSplitNeeded = true) :
    AtSplit T (b0 + 7) A weights := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, hb, hm⟩ := h.eight
  obtain ⟨h3, r8, o8⟩ := declares_split P b1 b2 b3 b4 b5 b6 b7 b8 hb hS
  obtain ⟨-, -, -, p8⟩ := places4 P b1 b2 b3 b4 b5 b6 b7 b8 hb
  refine ⟨fun blk hblk => ?_, fun blk hblk => ?_⟩
  · obtain ⟨hr, ho, -⟩ := hm 7 b8 rfl blk hblk
    exact ⟨{ entry := entryAt P 3 }, hr.trans r8, ho.trans o8, h3, rfl, rfl⟩
  · obtain ⟨-, -, hp⟩ := hm 7 b8 rfl blk hblk
    rw [hp, p8]
    exact h.found { place := place 8, parts := [liftK14 A weights (splitPart A)] }
      (by rw [halves_eq, h.shape, hS]; simp)

/-- "LOC" stands at b0 + 3. hcol: at every valid input the thread's committed table of the item that
"LOC" reads has a column of the declared width at every position below its length. -/
theorem atLoc_of (h : AtEight T b0 P A weights)
    (hcol : ∀ w, T.valid w → ∀ p < 2 ^ (Desc.K14.readsAtLoc P.S.fold P.item).sh.a,
      ∃ u, T.stored w (Desc.K14.readsAtLoc P.S.fold P.item).item p = some u ∧
        u.length = (Desc.K14.readsAtLoc P.S.fold P.item).sh.W) :
    AtLoc T (b0 + 3) A weights := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, hb, hm⟩ := h.eight
  obtain ⟨-, h1, -, -, -, r4, o4, -⟩ := declares3 P b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨-, p4, -⟩ := places4 P b1 b2 b3 b4 b5 b6 b7 b8 hb
  refine ⟨fun blk hblk => ?_, fun blk hblk => ?_⟩
  · obtain ⟨hr, ho, -⟩ := hm 3 b4 rfl blk hblk
    refine ⟨{ entry := entryAt P 1, stored := [Desc.K14.readsAtLoc P.S.fold P.item] },
      hr.trans r4, ho.trans o4, h1, rfl, fun w hw s hs p hp => ?_⟩
    obtain rfl : s = Desc.K14.readsAtLoc P.S.fold P.item := by simpa using hs
    exact hcol w hw p hp
  · obtain ⟨-, -, hp⟩ := hm 3 b4 rfl blk hblk
    rw [hp, p4]
    exact h.found { place := place 4, parts := [liftK14 A weights quietPart] }
      (by rw [halves_eq]; simp)

/-- **Plays at "LIN point", "LOC" and "LIN zeta"**, whether the shape splits or not. -/
theorem three_Play (h : AtEight T b0 P A weights)
    (hcol : ∀ w, T.valid w → ∀ p < 2 ^ (Desc.K14.readsAtLoc P.S.fold P.item).sh.a,
      ∃ u, T.stored w (Desc.K14.readsAtLoc P.S.fold P.item).item p = some u ∧
        u.length = (Desc.K14.readsAtLoc P.S.fold P.item).sh.W) :
    Plays T b0 ∧ Plays T (b0 + 3) ∧ Plays T (b0 + 6) :=
  ⟨quiet_Plays (atPoint_of h), loc_Plays (atLoc_of h hcol), quiet_Plays (atZeta_of h)⟩

/-- **Plays at the kind's own four members that have a round**, where the shape splits. -/
theorem four_Play (h : AtEight T b0 P A weights) (hS : P.S.sharedSplitNeeded = true)
    (hcol : ∀ w, T.valid w → ∀ p < 2 ^ (Desc.K14.readsAtLoc P.S.fold P.item).sh.a,
      ∃ u, T.stored w (Desc.K14.readsAtLoc P.S.fold P.item).item p = some u ∧
        u.length = (Desc.K14.readsAtLoc P.S.fold P.item).sh.W) :
    Plays T b0 ∧ Plays T (b0 + 3) ∧ Plays T (b0 + 6) ∧ Plays T (b0 + 7) :=
  ⟨quiet_Plays (atPoint_of h), loc_Plays (atLoc_of h hcol), quiet_Plays (atZeta_of h),
    split_Plays (atSplit_of h hS)⟩

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.places4
#print axioms ProofFile.Honest.K14.AtEight.found
#print axioms ProofFile.Honest.K14.atPoint_of
#print axioms ProofFile.Honest.K14.atZeta_of
#print axioms ProofFile.Honest.K14.atSplit_of
#print axioms ProofFile.Honest.K14.atLoc_of
#print axioms ProofFile.Honest.K14.three_Play
#print axioms ProofFile.Honest.K14.four_Play
