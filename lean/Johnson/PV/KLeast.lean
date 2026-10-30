-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/KLeast.lean: **K IS NO CHOICE: IT IS THE LEAST NUMBER THAT SERVES.** General in the
  field's mark, the three files' data and the seed's need.
WHAT IS ASKED OF K, AND BY WHOM: (a) of every round d of the key file's, the entry's and the proof
  file's data: (bsRound f d.entry d.kind).b ≤ K: the very shape of kThree_key |
  kThree_entry | kThree_proof (OnBytes/Flat/WireBlocks.lean:59-77): what a round's challenge reads
  of an
answer's K blocks · (b) of the seed: sb ≤ K + 1: the very premise of recSeedK … (K + 1) h
  (OnBytes/Flat/RecordSeed.lean:30), sb := (seedBS lg s).b. Serves f DK ds DP sb K := these four.
  foldl_max_le · blocksT_le · kThree_le: kThree is at most every K that serves the rounds
    (the three laws named above say that it serves them)
  kLeast f DK ds DP sb := max (kThree f DK ds DP) (sb - 1) · **kLeast_serves** · **kLeast_least :
    Serves … K → kLeast … ≤ K**
NOT SAID: that the theorem's hypothesis on the wires (CompilerSoundnessConditionStatements.wires) asks no more of K than (a) and
  (b): I have not walked it. Nothing on soundness.


-/
import OnBytes.Flat.WireBlocks

set_option autoImplicit false

namespace W4N
open OnBytes.Flat OnBytes.Maker _root_.Run _root_.Run.PQ

/-- A fold by the greater stays below what bounds its start and every member's value. -/
theorem foldl_max_le {α : Type} (g : α → ℕ) (K : ℕ) : ∀ (l : List α) (n : ℕ), n ≤ K → (∀ d ∈ l, g d
    ≤ K) →
    l.foldl (fun a d => max a (g d)) n ≤ K
  | [], _, hn, _ => hn
  | x :: l, n, hn, h =>
    foldl_max_le g K l (max n (g x)) (Nat.max_le.2 ⟨hn, h x (List.mem_cons_self ..)⟩)
      fun d hd => h d (List.mem_cons_of_mem _ hd)

variable (f : Fmt.Fld) (DK : WholeD) (ds : List RD) (DP : WholeD) (sb : ℕ)

/-- K serves: every round of the three files' data, and the seed. -/
structure Serves (K : ℕ) : Prop where
  key : ∀ d ∈ DK.ds₁ ++ (DK.ds₂ ++ DK.ds₃), (bsRound f d.entry d.kind).b ≤ K
  entry : ∀ d ∈ ds, (bsRound f d.entry d.kind).b ≤ K
  proof : ∀ d ∈ DP.ds₁ ++ (DP.ds₂ ++ DP.ds₃), (bsRound f d.entry d.kind).b ≤ K
  seed : sb ≤ K + 1

/-- `kThree` (OnBytes/Flat/WireBlocks.lean) is at most every K that serves the rounds. -/
theorem kThree_le {K : ℕ} (h : Serves f DK ds DP sb K) : kThree f DK ds DP ≤ K :=
  Nat.max_le.2 ⟨foldl_max_le _ K _ 0 (Nat.zero_le _) h.key,
    Nat.max_le.2 ⟨foldl_max_le _ K _ 0 (Nat.zero_le _) h.entry, foldl_max_le _ K _ 0 (Nat.zero_le _)
        h.proof⟩⟩

/-- The least number that serves. -/
def kLeast : ℕ := max (kThree f DK ds DP) (sb - 1)

/-- **It serves.** -/
theorem kLeast_serves : Serves f DK ds DP sb (kLeast f DK ds DP sb) where
  key := fun d hd => Nat.le_trans (kThree_key f DK ds DP d hd) (Nat.le_max_left _ _)
  entry := fun d hd => Nat.le_trans (kThree_entry f DK ds DP d hd) (Nat.le_max_left _ _)
  proof := fun d hd => Nat.le_trans (kThree_proof f DK ds DP d hd) (Nat.le_max_left _ _)
  seed := by
    have : sb - 1 ≤ kLeast f DK ds DP sb := Nat.le_max_right _ _
    omega

/-- **No lesser number serves.** -/
theorem kLeast_least {K : ℕ} (h : Serves f DK ds DP sb K) : kLeast f DK ds DP sb ≤ K :=
  Nat.max_le.2 ⟨kThree_le f DK ds DP sb h, by have := h.seed; omega⟩

end W4N

#print axioms W4N.kLeast_serves
#print axioms W4N.kLeast_least
