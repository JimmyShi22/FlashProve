-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1L20R/FtAtSwitch.lean: ROW F28: the number
"first tree" of the place of every code switch, as the sentence on the carried word reads it
(ProofFile.pAtK2 Z m, Johnson/Desc/ProofFile/CarryAt.lean), is 0: the number at which the first chain's
fold runs.

Why. CarryFence (Johnson/Top/H0/Walk/FrameCarryBack.lean) subtracts that number from a tree's number
in the natural numbers before it looks the tree up; "the book is in order" along the run is had at
the fold's own first tree. Were the two different, the key would be wrong without any test noticing.

  par9_firstTree    K2.par9 p keeps p's first tree
  pAt_firstTree     at a public part that the maker returns: (ProofFile.pAtK2 Z m).firstTree = 0, at
                    every m
  ft_at_switch      so (K2.par9 (ProofFile.pAtK2 Z m)).firstTree = 0: the binder hFt of fence9_of
                    (FrameKn.lean), at ft := 0, at every m

Called: P1K2.firstTree_of_pub (Johnson/Top/H0/K2Hears/FtAtPub.lean) and spot_is
(Johnson/Top/H0/K2Caller/PAtSeated.lean).

No soundness statement.

-/
import Johnson.Top.H0.K2Hears.FtAtPub
import Johnson.Top.H0.K2Caller.PAtSeated

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1L20

open VerifiableInference.Desc.First.K2 (P2 par9)
open VerifiableInference.Desc.First.K2Caller (spot_is)

/-- K2.par9 keeps the place's first tree. -/
theorem par9_firstTree (p : P2) : (par9 p).firstTree = p.firstTree := by
  unfold par9
  split <;> rfl

/-- **The place's first tree is 0.** -/
theorem pAt_firstTree {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pubPlain o pol lay KL = .ok Z) (m : ℕ) : (ProofFile.pAtK2 Z m).firstTree = 0 := by
  unfold ProofFile.pAtK2 ProofFile.pAtK2?
  cases hf : (ProofFile.k2SpotsAt Z).find? fun x => x.2.grp == m + 1 with
  | none => rfl
  | some y =>
    have hy : y ∈ ProofFile.k2SpotsAt Z := List.mem_of_find?_eq_some hf
    unfold ProofFile.k2SpotsAt at hy
    cases hb : ProofFile.blankBy ProofFile.pureRoad.links Z with
    | none =>
      rw [hb] at hy
      cases hy
    | some G =>
      rw [hb] at hy
      obtain ⟨P, n, -, -, e⟩ := spot_is (G := G) hy
      show y.2.firstTree = 0
      rw [e]
      exact P1K2.firstTree_of_pub h

/-- **fence9_of's binder hFt, at ft := 0.** -/
theorem ft_at_switch {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pubPlain o pol lay KL = .ok Z) (m : ℕ) : (par9 (ProofFile.pAtK2 Z m)).firstTree = 0 := by
  rw [par9_firstTree]
  exact pAt_firstTree h m

end P1L20

#print axioms P1L20.par9_firstTree
#print axioms P1L20.pAt_firstTree
#print axioms P1L20.ft_at_switch
