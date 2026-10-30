-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/HBaseWritten.lean: the binder hbase of the law on the sub-protocol K13, `N.index.1
< nTrees (ds₁.take n)`: the tree of the index masks' oracle message is sent in front of K13's place.
As it is stated it sums over some 48,270 rounds, which Lean's kernel does not bear. Here it is had
from the first round alone: that round sends two trees, and a longer stretch sends no fewer.

Row or tool. One general law, one closed fact on the written data, and the binder from these. They
are an example and a payer for a premise of another law. No law on a sub-protocol is named.

The binder's arguments, their written terms and their ties.
  `(dataOf a R₁ R₂ R₃).ds₁`, the data of the first chain's rounds: `writtenPFull.ds₁`
    (Johnson/Flat/Dec/FitAtWritten.lean). Tie: `laidPOf_written`
    (Johnson/Desc/Laid/ProofFullScope.lean): through Lean.
  `N.index.1`: 1, by a program. No closed term for N lies yet: here a premise, `N.index.1 ≤
    1`.
  `inFront355 c`, the number of rounds that the first 355 sub-protocols declare: it reads the chain
    c. Here a letter n with the premise `1 ≤ n`. No tie.

What is here.
  `nTrees_take_mono`: for 1 ≤ n, the first n rounds send at least as many trees as the first round.
  `trees_of`, `trees_written`: each round of the written data sends as many trees as the written
    round beneath it has items "root". By `rdsFromL_map` (OnBytes/Maker/ReadData.lean); nothing is
    evaluated. `nTrees_take_of`: the trees of a stretch in front, off that list of numbers.
    `first_round_written`: the first round of the written data sends two trees.
  `hbase_of`: so `N.index.1 < nTrees (writtenPFull.ds₁.take n)` wherever `N.index.1 ≤ 1` and `1 ≤
    n`.
  `hbase_rejects`: the negative test: at n = 0 the inequality fails at every N; and at a tree's
    number 2 the first round alone does not give it.
By an evaluation in Lean's kernel (`decide +kernel`): inside `first_round_written`, on the written
list of rounds, not on the data made of it. What the kernel does not bear, by two runs: any question
put to `writtenPFull.ds₁` itself, even the length of its first round alone: at the usual depth of
recursion Lean refuses, and at a depth of 1000000 it ends with a stack overflow.

Limits. No form in scope is stated: two of the three arguments are tied by nothing yet. Nothing on
soundness.


-/
import Johnson.Desc.Sound.Cuts
import Johnson.Desc.First.Borders
import Johnson.Flat.Dec.FitAtWritten
import OnBytes.Maker.ReadData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes.Maker Johnson.G
open VerifiableInference.Desc.Sound (nTrees nTrees_cons)
open VerifiableInference.Desc.First (Numbers)

/-- For 1 ≤ n the first n rounds send at least as many trees as the first round. -/
theorem nTrees_take_mono (ds : List RDT) {n : ℕ} (hn : 1 ≤ n) :
    nTrees (ds.take 1) ≤ nTrees (ds.take n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  cases ds with
  | nil => simp
  | cons d l =>
    rw [List.take_succ_cons, List.take_succ_cons, List.take_zero, nTrees_cons, nTrees_cons]
    exact Nat.add_le_add_left (Nat.zero_le _) _

/-- How many trees each round of a file's first list of data sends: as many as the written round has
items "root"; without the last round, the seal. -/
theorem trees_of (a : ℕ) (R₁ R₂ R₃ : OnBytes.Params.Rounds) :
    (WholeD.of a (OnBytes.Three.Whole.of R₁ R₂ R₃)).ds₁.map (·.trees.length) =
      (R₁.map fun r => r.1.items.countP (· == .root)).dropLast := by
  show (((OnBytes.Three.Whole.of R₁ R₂ R₃).ds₁.dropLast.map rdtOf).map (·.trees.length)) = _
  rw [List.map_map, List.map_dropLast]
  exact congrArg List.dropLast (rdsFromL_map _ _ _ _ _ _ _ _ (fun r n => by
    show ((List.range (r.1.items.countP (· == .root))).map _).length = _
    rw [List.length_map, List.length_range]) R₁)

/-- The same at the written data. -/
theorem trees_written :
    writtenPFull.ds₁.map (·.trees.length) =
      (dryProofFull.1.map fun r => r.1.items.countP (· == .root)).dropLast :=
  trees_of 32 dryProofFull.1 dryProofFull.2.1 dryProofFull.2.2

/-- The trees of a stretch in front, off the list of the rounds' numbers of trees. -/
theorem nTrees_take_of {ds : List RDT} {l : List ℕ} (h : ds.map (·.trees.length) = l) (n : ℕ) :
    nTrees (ds.take n) = (l.take n).sum := by
  unfold nTrees
  rw [List.map_take, h]

/-- **The first round of the written data sends two trees.** -/
theorem first_round_written : nTrees (writtenPFull.ds₁.take 1) = 2 :=
  (nTrees_take_of trees_written 1).trans (by decide +kernel)

/-- **The binder**, from the first round alone. -/
theorem hbase_of {N : Numbers} {n : ℕ} (hi : N.index.1 ≤ 1) (hn : 1 ≤ n) :
    N.index.1 < nTrees (writtenPFull.ds₁.take n) := by
  have h := nTrees_take_mono writtenPFull.ds₁ hn
  rw [first_round_written] at h
  omega

/-- **The negative test**: at no round in front it fails; and the first round gives no third tree.
-/
theorem hbase_rejects (N : Numbers) :
    ¬ N.index.1 < nTrees (writtenPFull.ds₁.take 0) ∧ ¬ 2 < nTrees (writtenPFull.ds₁.take 1) := by
  refine ⟨?_, ?_⟩
  · rw [List.take_zero]
    exact Nat.not_lt_zero _
  · rw [first_round_written]
    exact Nat.lt_irrefl 2

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.nTrees_take_mono
#print axioms VerifiableInference.Desc.K13.Law.trees_of
#print axioms VerifiableInference.Desc.K13.Law.trees_written
#print axioms VerifiableInference.Desc.K13.Law.nTrees_take_of
#print axioms VerifiableInference.Desc.K13.Law.first_round_written
#print axioms VerifiableInference.Desc.K13.Law.hbase_of
#print axioms VerifiableInference.Desc.K13.Law.hbase_rejects
