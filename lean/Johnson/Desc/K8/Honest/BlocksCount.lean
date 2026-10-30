-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/BlocksCount.lean: THE SMALLNESS TEST: THE VERIFIER's TWO COMPUTATIONS OF THE
NUMBER OF BLOCKS OF THE DIGITS' ROWS AGREE: the first lays the blocks by a loop (`t2BL`,
OnBytes/Model/Tail.lean), the second reads the number off the top bit of the number of combinations
(`HTailF2.wants`, the same file). For the test by a second computation behind the adding, which
compares numbers of virtual rows at the second number while the plan lays them at the first. Lemmas
on the verifier's own text; none of the library's goals.

  `loop_done`   the loop lays nothing from a first row at or behind the end
  **`blocks_count`**   t2BL R = .ok bz → bz is not empty → bz.size ≤ 2 → bz.size = (if R - 2 ^
                   Nat.log2 R != 0 then 2 else 1)
  **`wants_blocks`**   so, where the data's blocks are the loop's at its number of combinations, one
                   or two of them: tl.wants = some (nbW, W) → nbW = tl.zzBlocks
THE LIBRARY HAS THAT EQUATION FROM THE TEST's SUCCESS (`blocks_eq`,
OnBytes/Tie/Pv/Tail/EndRaw.lean): here it comes from the plan, for whoever is to show that the test
succeeds.
Limits. THAT THE DATA's BLOCKS ARE THE LOOP's (t2BL tl.tau = .ok tl.blocks), AND ONE OR TWO, ARE
PREMISES: facts on the plan: the routine that makes the two lookup calls lays them so and refuses
otherwise (`piecesF`); that a state's data come of that routine is not shown here.
Nothing is claimed on completeness, soundness or hiding.

-/
import OnBytes.Model.Tail

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model

/-- The loop lays nothing from a first row at or behind the end. -/
theorem loop_done (R r0 : Nat) (h : ¬ r0 < R) : ∀ fuel, t2BLLoop R fuel r0 = []
  | 0 => rfl
  | fuel + 1 => by simp only [t2BLLoop, if_neg h]

/-- **The loop's number of blocks is the one that the top bit gives.** -/
theorem blocks_count {R : Nat} {bz : Array (Nat × Nat)} (h : t2BL R = .ok bz)
    (h1 : bz.size ≠ 0) (h2 : bz.size ≤ 2) :
    bz.size = if R - 2 ^ Nat.log2 R != 0 then 2 else 1 := by
  unfold t2BL at h
  simp only at h
  split at h
  · cases h
  · obtain rfl := Except.ok.inj h
    simp only [List.size_toArray] at h1 h2 ⊢
    have hR : 0 < R := by
      rcases Nat.eq_zero_or_pos R with e | e
      · subst e
        exact absurd (by rw [loop_done 0 0 (Nat.lt_irrefl 0)]; rfl) h1
      · exact e
    have e1 : t2BLLoop R (Nat.log2 R + 1) 0 =
        (0, 2 ^ Nat.log2 R) :: t2BLLoop R (Nat.log2 R) (2 ^ Nat.log2 R) := by
      simp only [t2BLLoop, if_pos hR, Nat.sub_zero, Nat.zero_add]
    rw [e1] at h2 ⊢
    simp only [List.length_cons] at h2 ⊢
    have hle : 2 ^ Nat.log2 R ≤ R := Nat.log2_self_le (Nat.pos_iff_ne_zero.1 hR)
    by_cases hc : 2 ^ Nat.log2 R < R
    · have hl : Nat.log2 R ≠ 0 := by
        intro e
        have h3 : R < 2 ^ (Nat.log2 R + 1) := Nat.lt_log2_self
        rw [e] at h3 hc
        omega
      obtain ⟨f, hf⟩ := Nat.exists_eq_succ_of_ne_zero hl
      have e2 : ∃ x l, t2BLLoop R (Nat.log2 R) (2 ^ Nat.log2 R) = x :: l := by
        generalize 2 ^ Nat.log2 R = r0 at hc
        rw [hf]
        simp only [t2BLLoop, if_pos hc]
        exact ⟨_, _, rfl⟩
      obtain ⟨x, l, e3⟩ := e2
      rw [e3] at h2 ⊢
      simp only [List.length_cons] at h2 ⊢
      have hne : (R - 2 ^ Nat.log2 R != 0) = true := by
        simp only [bne_iff_ne, ne_eq]
        omega
      rw [if_pos hne]
      omega
    · rw [loop_done R _ hc]
      have hz : (R - 2 ^ Nat.log2 R != 0) = false := by
        have : R - 2 ^ Nat.log2 R = 0 := by omega
        rw [this]
        rfl
      rw [hz]
      rfl

/-- **The second computation's number of blocks is the plan's.** -/
theorem wants_blocks (tl : HTailF2) (hb : t2BL tl.tau = .ok tl.blocks)
    (h1 : tl.blocks.size ≠ 0) (h2 : tl.blocks.size ≤ 2) :
    ∀ nbW W, tl.wants = some (nbW, W) → nbW = tl.zzBlocks := by
  intro nbW W hw
  unfold HTailF2.wants at hw
  simp only at hw
  split at hw
  · cases hw
  · have e := (Prod.mk.inj (Option.some.inj hw)).1
    rw [← e]
    exact (blocks_count hb h1 h2).symm

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.loop_done
#print axioms VerifiableInference.Desc.First.K8.Honest.blocks_count
#print axioms VerifiableInference.Desc.First.K8.Honest.wants_blocks
