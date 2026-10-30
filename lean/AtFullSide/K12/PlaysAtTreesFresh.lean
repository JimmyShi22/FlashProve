-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
AtFullSide/K12/PlaysAtTreesFresh.lean

It states no goal. No property of the protocol is claimed.

WHICH MEMBERS OF THE PROOF FILE's LAST CHAIN CAN HAVE A NEW TREE: NUMBER 2, THE CHAIN's OWN PROXIMITY TEST, ALONE. Four
theorems; no definition.

  `fresh_nil_of_same_count`      at any thread: where the count of declared trees does not grow over member b,
                                 `Thread.fresh b` is empty
  `treesTo_succ_of_no_tree`      a block that declares no tree leaves the count as it was
  `fresh_nil_of_no_tree`         so at a member whose block declares no tree `Thread.fresh b` is empty
  `fresh_nil_off_the_test`       at a thread over the description's last chain: at every member but number 2

By what. The text of `Thread.fresh` (Honest/Thread/Pays.lean), `Thread.hand`, `treesTo` (Honest/Thread/Thr.lean);
`second_flat` (K12/AtFile/WLetter.lean): the last chain is four blocks: K14's second part, the taken trees' sources,
the test, the chain's end; the first two and the last declare no oracle message, by their text.

Hypotheses of the last. hbs: the thread's list is the description's last chain. hb: b is a member. hne: b is not 2. No
head, at every function for the format's second hash function.

Limits.
- A fact on the description's text: counts of declared trees. No run, no coin, no input is named.
- That number 2 has a new tree is not said here.
- The last fact stands also at one thread as a value (`last_fresh`, AtFullSide/Honest/TheLettersFit.lean, not beneath this
  file); here the thread is a letter. `treesTo_behind_quiet` there is the same law as `treesTo_succ_of_no_tree` here.
- Nothing on completeness, soundness or hiding.

These four bear no label under the rule of use at the head of Johnson/Bind/ForProver/FiveFieldsAt.lean: none names a
coin, a run's input or a Script.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WLetter
import Johnson.Desc.ProofFile.Honest.Thread.Pays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K12
open ProofFile.Honest
open VerifiableInference.Desc (Block Chain)
open ProofFile.Honest.K12.AtFile (second_flat)
open P5J (F0T TS)

section
variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-- **Where the count of declared trees does not grow over a member, the member has no new tree.** -/
theorem fresh_nil_of_same_count {b : ℕ} (e : treesTo T.bs (b + 1) = treesTo T.bs b) :
    T.fresh b = [] := by
  unfold Thread.fresh Thread.hand
  rw [e]
  exact List.filter_eq_nil_iff.2 fun σ hσ => by simp [hσ]

/-- A block that declares no tree leaves the count as it was. -/
theorem treesTo_succ_of_no_tree {bs : List (Block S Cl)} {b : ℕ} {blk : Block S Cl}
    (hb : bs[b]? = some blk) (h0 : blk.oracles.flatMap id = []) :
    treesTo bs (b + 1) = treesTo bs b := by
  unfold treesTo
  rw [List.take_add_one, hb, List.flatMap_append, List.length_append, Option.toList_some]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, h0, List.length_nil, Nat.add_zero]

/-- **At a member whose block declares no tree there is no new tree.** -/
theorem fresh_nil_of_no_tree {b : ℕ} {blk : Block S Cl} (hb : T.bs[b]? = some blk)
    (h0 : blk.oracles.flatMap id = []) : T.fresh b = [] :=
  fresh_nil_of_same_count T (treesTo_succ_of_no_tree hb h0)

end

section
variable {V W X Pb : Type} {Bk : ProverCoinCounts} (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4)
  (cF : Chain TS ProofFile.Cl)

/-- **At the last chain every member but number 2 has no new tree.** -/
theorem fresh_nil_off_the_test
    (T : Thread Bk (F0T o Zp Np cF).S₃ (F0T o Zp Np cF).Cl V W X Pb)
    (hbs : T.bs = (F0T o Zp Np cF).second.blocksInOrder) {b : ℕ} (hb : b < T.bs.length) (hne : b ≠ 2) :
    T.fresh b = [] := by
  have hl : T.bs.length = 4 := by
    rw [hbs, second_flat]
    rfl
  rw [hl] at hb
  apply fresh_nil_of_same_count
  rw [hbs, second_flat]
  rcases (by omega : b = 0 ∨ b = 1 ∨ b = 3) with rfl | rfl | rfl <;> rfl

end

end AtFullSide.K12

#print axioms AtFullSide.K12.fresh_nil_of_same_count
#print axioms AtFullSide.K12.treesTo_succ_of_no_tree
#print axioms AtFullSide.K12.fresh_nil_of_no_tree
#print axioms AtFullSide.K12.fresh_nil_off_the_test
