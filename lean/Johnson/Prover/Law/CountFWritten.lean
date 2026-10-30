-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Law/CountFWritten.lean: THE THREE CLOSED SUMS OF Johnson/Prover/Law/CountFAt.lean AS
NUMERALS, AT THE WRITTEN LISTS OF THE FULL-SIZE EXAMPLE, by evaluations in Lean's kernel: at the
data of dKeyFull and dProofFull (Johnson/Flat/Dec/FitAtWritten.lean) and the copy's file's written
rounds dsFull (OnBytes/Flat/LinkSibAt.lean), with K := 24086 blocks for a round's verifier message
(an answer has 24088 hash blocks), caps of 2^(work + 6) tries, and paths of the lengths 0, 0 and 6.

Main names.
  key1, key2, key3, proof1, proof2, proof3, copy0   the seven stretches' sums.
  chainF_keyFull    = 5223661230411.
  chainF_copyFull   = 1649307525166.
  chainF_proofFull  = 177887278538.
  three_le          their sum, 7050856034115, is at most 2^43.

chainF_keyFull and chainF_proofFull take the data as a LETTER D with the three sums as premises;
chainF_at_dKeyFull and chainF_at_dProofFull are their calls at the written data themselves (bare
applications, under a raised recursion depth: three other forms of the call, by rw and by congrArg,
were refused by Lean: "(kernel) deep recursion detected", twice; "maximum recursion depth", once).

Limits. THE THEOREMS SPEAK OF THE WRITTEN LISTS, which were made at one made-up request: that these
are the plan's rounds at the release's public files is no theorem at the full size (the head of
FitAtWritten.lean). THREE CHAINS ALONE: the outer trees, which a prover of a whole request builds
beside, the seeds' queries and whatever commit, parser and readMore ask are not in these numbers.
THE CAPS ARE OF OUR CHOOSING. K AND THE THREE LENGTHS OF PATHS ARE NUMERALS HERE: 24086, and the
depths of request trees at which FitAtWritten.lean evaluates the frame's test (0 for the key file's
calls, 6 for the proof file's) and the 0 that the frame's wiring lays for the copy's file; that a
coin's path has its tree's depth is a clause of Coins.Fit (OnBytes/Prover/Inv.lean): not called
here. An upper bound on every path, with chainF's looseness. No goal's form is named: nothing here
says that a budget is met.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Law.CountFAt
import Johnson.Flat.Dec.FitAtWritten
import OnBytes.Flat.LinkSibAt

set_option autoImplicit false

namespace OnBytes.Prover
open Johnson.G OnBytes.Flat OnBytes.Maker _root_.Run _root_.Run.PQ

set_option maxRecDepth 1000000 in
theorem key1 : sumE 0 (dKeyFull.ds₁.map fun d =>
    roundF 24088 0 (d.trees.map (·.a)) d.entry.work) = 1100439984544 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem key2 : sumE 0 (dKeyFull.ds₂.map fun d =>
    roundF 24088 0 (d.trees.map (·.a)) d.entry.work) = 2748829449534 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem key3 : sumE 0 (dKeyFull.ds₃.map fun d =>
    roundF 24088 0 (d.trees.map (·.a)) d.entry.work) = 1374391651799 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem proof1 : sumE 0 (dProofFull.ds₁.map fun d =>
    roundF 24088 6 (d.trees.map (·.a)) d.entry.work) = 5700400065 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem proof2 : sumE 0 (dProofFull.ds₂.map fun d =>
    roundF 24088 6 (d.trees.map (·.a)) d.entry.work) = 171849072342 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem proof3 : sumE 0 (dProofFull.ds₃.map fun d =>
    roundF 24088 6 (d.trees.map (·.a)) d.entry.work) = 337661579 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem copy0 : sumE 0 (dsFull.map fun d =>
    roundF 24088 0 (d.trees.map (·.a)) d.entry.work) = 1649307476988 := by decide +kernel

theorem sum_of_sumE {l : List ℕ} {n : ℕ} (h : sumE 0 l = n) : l.sum = n := by
  rw [← h, sumE_eq, Nat.zero_add]

section
variable (C : CK) (chal : ∀ e k, (Fin 24086 → _root_.Iop.Dig 256) → C.Ch e k)
  {TF TJ T3 Xi : Type} (tF : TF) (tJ : TJ) (t3 : T3) (silent : Xi → TF → TJ → T3 → Bool)
  (run : Xi → View → View → View → Bool)

/-- **The key file's chain**, at data with the written lists' three sums. -/
theorem chainF_keyFull (D : WholeD)
    (h₁ : sumE 0 (D.ds₁.map fun d => roundF 24088 0 (d.trees.map (·.a)) d.entry.work) =
      1100439984544)
    (h₂ : sumE 0 (D.ds₂.map fun d => roundF 24088 0 (d.trees.map (·.a)) d.entry.work) =
      2748829449534)
    (h₃ : sumE 0 (D.ds₃.map fun d => roundF 24088 0 (d.trees.map (·.a)) d.entry.work) =
      1374391651799) :
    chainF (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann
      (wqWhole C 24086 chal D tF tJ t3 silent run).sh (capAt (Page.workAt D)) 0 0 =
      5223661230411 :=
  (chainF_of_sums C 24086 chal 0 D tF tJ t3 silent run 24088 rfl _ _ _ (sum_of_sumE h₁)
    (sum_of_sumE h₂) (sum_of_sumE h₃)).trans (by norm_num)

/-- **The proof file's chain**, at data with the written lists' three sums. -/
theorem chainF_proofFull (D : WholeD)
    (h₁ : sumE 0 (D.ds₁.map fun d => roundF 24088 6 (d.trees.map (·.a)) d.entry.work) =
      5700400065)
    (h₂ : sumE 0 (D.ds₂.map fun d => roundF 24088 6 (d.trees.map (·.a)) d.entry.work) =
      171849072342)
    (h₃ : sumE 0 (D.ds₃.map fun d => roundF 24088 6 (d.trees.map (·.a)) d.entry.work) =
      337661579) :
    chainF (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann
      (wqWhole C 24086 chal D tF tJ t3 silent run).sh (capAt (Page.workAt D)) 0 6 =
      177887278538 :=
  (chainF_of_sums C 24086 chal 6 D tF tJ t3 silent run 24088 rfl _ _ _ (sum_of_sumE h₁)
    (sum_of_sumE h₂) (sum_of_sumE h₃)).trans (by norm_num)

/-- **The copy's file's chain.** -/
theorem chainF_copyFull (a : ℕ) (xs : List XO) {Y : Type} (dec : Y → View → Bool) :
    chainF (linkSkeletonOfRoundData C dsFull a xs dec).up.loc.shape (linkSkeletonOfRoundData C dsFull a xs dec).up.ann
      (Johnson.RunOne.StrictW.wqW C dsFull a xs dec 24086 chal).sh (capAt (workL dsFull)) 0 0 =
      1649307525166 := by
  rw [chainF_wqW, sum_of_sumE copy0]

end

section
variable (C : CK) (chal : ∀ e k, (Fin 24086 → _root_.Iop.Dig 256) → C.Ch e k)
  {TF TJ T3 Xi : Type} (tF : TF) (tJ : TJ) (t3 : T3) (silent : Xi → TF → TJ → T3 → Bool)
  (run : Xi → View → View → View → Bool)

set_option maxRecDepth 1000000 in
/-- **The key file's chain at the written data.** -/
theorem chainF_at_dKeyFull :
    chainF (chainsOf C dKeyFull tF tJ t3).sh (chainsOf C dKeyFull tF tJ t3).ann
      (wqWhole C 24086 chal dKeyFull tF tJ t3 silent run).sh (capAt (Page.workAt dKeyFull)) 0 0 =
      5223661230411 :=
  chainF_keyFull C chal tF tJ t3 silent run dKeyFull key1 key2 key3

set_option maxRecDepth 1000000 in
/-- **The proof file's chain at the written data.** -/
theorem chainF_at_dProofFull :
    chainF (chainsOf C dProofFull tF tJ t3).sh (chainsOf C dProofFull tF tJ t3).ann
      (wqWhole C 24086 chal dProofFull tF tJ t3 silent run).sh (capAt (Page.workAt dProofFull)) 0
      6 = 177887278538 :=
  chainF_proofFull C chal tF tJ t3 silent run dProofFull proof1 proof2 proof3

end

/-- The three together. -/
theorem three_le : 5223661230411 + 1649307525166 + 177887278538 ≤ 2 ^ 43 := by norm_num

end OnBytes.Prover

#print axioms OnBytes.Prover.key1
#print axioms OnBytes.Prover.key2
#print axioms OnBytes.Prover.key3
#print axioms OnBytes.Prover.proof1
#print axioms OnBytes.Prover.proof2
#print axioms OnBytes.Prover.proof3
#print axioms OnBytes.Prover.copy0
#print axioms OnBytes.Prover.sum_of_sumE
#print axioms OnBytes.Prover.chainF_keyFull
#print axioms OnBytes.Prover.chainF_proofFull
#print axioms OnBytes.Prover.chainF_copyFull
#print axioms OnBytes.Prover.chainF_at_dKeyFull
#print axioms OnBytes.Prover.chainF_at_dProofFull
#print axioms OnBytes.Prover.three_le
