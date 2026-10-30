-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K9R/WantsBlocks.lean: A LAW OF THE PLANNERS' TEXT, general in the numbers: the two
computations of the number of blocks of ZZ's rows agree at what HTailF2.piecesF returns: the
second computation (HTailF2.wants, OnBytes/Model/Tail.lean) returns, and its number of blocks is
the number that piecesF has laid (zzBlocks). Typed for K9's files: it is the sentence of the field
StaticOk.blocks (Johnson/Desc/First/Link/Law/OkJoin.lean) and of its test with code blocksB
(OkClauseTests.lean, same folder), off the routine's return. NO BLOCK IMPORTS THIS FILE.
  t2BL_one_or_two    t2BL R = .ok bz, and bz has one or two blocks ⟹ nothing is left behind the
                     largest power of two below R, and bz has one · or what is left is a power of
                     two, and bz has two
  wants_of_t2BL      so tl.wants.map (·.1) = some bz.size, where bz is t2BL's value at tl.tau
  wants_of_piecesF   tl0.piecesF = .ok tl ⟹ tl.wants.map (·.1) = some tl.zzBlocks
  wants_seven        A NEGATIVE FACT, BY THE KERNEL: at tau = 7 (three blocks: 4 · 2 · 1) the
                     second computation returns nothing: so the sentence is no idle one
HOW. The loop's first step by its text; the rest of the loop by
piecesF_tail_cnt_t2BLLoop (OnBytes/Tie/Pv/Lookup/Ends/PiecesFTailCnt.lean): its blocks' lengths
sum to what is left and are powers of two. piecesF is cut as piecesF_cut cuts it
(FoZRec.lean: bindX · jpX).
LIMITS. At piecesF's return alone: the carrying to the public parameters and the built segments is
K9's files' to show. No soundness is claimed.
-/
import OnBytes.Tie.Pv.Lookup.Ends.PiecesFTailCnt
import OnBytes.Tie.Pv.Lookup.Ends.FoZRec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K9
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open Fo.ZPlan (bindX jpX)
open Fo.PiecesF (piecesF_tail_cnt_t2BLLoop)

theorem t2BL_one_or_two {R : Nat} {bz : Array (Nat × Nat)} (h : t2BL R = .ok bz)
    (h1 : ¬ (bz.isEmpty || decide (bz.size > 2)) = true) :
    (R - 2 ^ Nat.log2 R = 0 ∧ bz.size = 1) ∨ (∃ k, R - 2 ^ Nat.log2 R = 2 ^ k ∧ bz.size = 2) := by
  unfold t2BL at h
  dsimp only at h
  split_ifs at h
  have e := (Except.ok.inj h).symm
  subst e
  rw [t2BLLoop] at h1 ⊢
  by_cases hR : 0 < R
  · rw [if_pos hR] at h1 ⊢
    have hlt : R < 2 ^ (Nat.log2 R + 1) := Nat.lt_log2_self
    rw [pow_succ] at hlt
    have hle : 2 ^ Nat.log2 R ≤ R := Nat.log2_self_le (by omega)
    obtain ⟨i1, i2⟩ := piecesF_tail_cnt_t2BLLoop R (Nat.log2 R) (0 + 2 ^ Nat.log2 (R - 0))
      (by rw [Nat.sub_zero]; omega)
    simp only [Nat.sub_zero, Nat.zero_add] at i1 i2 h1 ⊢
    generalize t2BLLoop R (Nat.log2 R) (2 ^ Nat.log2 R) = rest at i1 i2 h1 ⊢
    match rest, i1, i2, h1 with
    | [], i1, _, _ =>
      left
      exact ⟨i1.symm, rfl⟩
    | [x], i1, i2, _ =>
      right
      obtain ⟨a, ha⟩ := i2 x (List.mem_singleton.2 rfl)
      refine ⟨a, ?_, rfl⟩
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at i1
      rw [← i1, ha]
    | _ :: _ :: _, _, _, h1 =>
      exfalso
      apply h1
      simp
  · rw [if_neg hR] at h1
    exfalso
    apply h1
    simp

theorem wants_of_t2BL (tl : HTailF2) {bz : Array (Nat × Nat)} (h : t2BL tl.tau = .ok bz)
    (h1 : ¬ (bz.isEmpty || decide (bz.size > 2)) = true) :
    tl.wants.map (·.1) = some bz.size := by
  unfold wants
  dsimp only
  rcases t2BL_one_or_two h h1 with ⟨e, s⟩ | ⟨k, e, s⟩
  · rw [e, s]
    simp
  · have hp : isPow2 (2 ^ k) = true := by
      unfold isPow2
      rw [Nat.log2_two_pow]
      simp
    rw [e, s, hp]
    simp

theorem wants_of_piecesF {tl0 tl : HTailF2} (h : tl0.piecesF = .ok tl) :
    tl.wants.map (·.1) = some tl.zzBlocks := by
  unfold piecesF at h
  obtain ⟨bz, hbz, h⟩ := bindX h
  obtain ⟨hsz, h⟩ := jpX h
  obtain ⟨_, h⟩ := jpX h
  obtain ⟨f9, _, h⟩ := bindX h
  obtain ⟨pub, _, h⟩ := bindX h
  obtain ⟨_, _, h⟩ := bindX h
  have e := (Except.ok.inj h).symm
  subst e
  exact wants_of_t2BL _ hbz hsz

theorem wants_seven : (({ tau := 7 } : HTailF2).wants.map (·.1)) = none := by decide +kernel

end P1K9

#print axioms P1K9.t2BL_one_or_two
#print axioms P1K9.wants_of_t2BL
#print axioms P1K9.wants_of_piecesF
#print axioms P1K9.wants_seven
