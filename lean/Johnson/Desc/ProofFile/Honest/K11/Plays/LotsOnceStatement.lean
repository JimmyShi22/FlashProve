-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/LotsOnceStatement.lean: THE ELEMENTS THAT THE KIND's TWO
LOTS NAME LIE IN NO OTHER PART's SPENDING ENTRY, AT A BOOK THAT FAILS NONE OF ITS OWN TESTS AND
PASSES THE LOCKS' OWN TEST. STATEMENTS ALONE: two definitions of propositions; no definition of
another kind. NOTHING IS PROVED IN THIS FILE, and neither is one of the library's goals: they are
lemmas' statements. PUBLIC DATA ALONE: a description, a book, numbers.

  `MaskLotOnce`   the book fails none of its tests (`ProverCoinCounts.word` is none) · the test `entryRunIs`
                  (Honest/Small/EntryRunIs.lean) at ⟨pl, 1⟩, entry 0, start base + ν₀ and count 2 lk
                  + 2: IT IS, SIGN FOR SIGN, THE TEST OF `MaskLotMeets` (MaskLotOwnerStatement.lean
                  of this folder): one yes pays both. Then, of every spending entry e' of every
                  OTHER part that has the same owner: none of the numbers base + ν₀ + i, i below 2
                  lk + 2, lies in its block of the extension field
  `IndexLotOnce`  the like at entry 1, start el and count 1: the test is that of `IndexLotMeets`
                  (IndexLotOwnerStatement.lean of this folder)

WHAT IT IS NOT. SILENT AT THE KIND's OWN PART: NOTHING ON ITS TWO ENTRIES AGAINST EACH OTHER. Under
two premises on the book: that any book meets them is not said here. Spending entries alone, but all
of them; nothing on carrying entries. ENTRIES ARE HELD AGAINST ENTRIES: what the owner itself does
with these elements is not seen. No address of another kind is written: the other part is a letter:
so each statement covers every pair with the kind's part. No lot is laid.

NEAR. `entryRunIs_once` (Honest/Small/EntryOnce.lean): the same at any part and entry: both are
calls of it.

Limits. Instances of one lemma. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Small.EntryRunIs
import Johnson.Desc.First.Fork.MergeKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open VerifiableInference.Desc (FileDescription Place)
open Johnson.Desc.First.ForkMerge (HeadMergeP)

/-- **The statement at the first lot's entry.** Not proved here; a lemma's statement, none of the
library's goals. -/
def MaskLotOnce : Prop :=
  ∀ (Xi : Type) (F : FileDescription Xi) (B : ProverCoinCounts) (pl : Place) (P : HeadMergeP) (o : Addr)
    (sf base ν₀ : Nat),
    B.word F = none →
    entryRunIs (spentE B ⟨pl, 1⟩) 0 o ⟨sf, base + ν₀⟩ ⟨0, 2 * P.lay.lk + 2⟩ = true →
    ∀ a', a' ≠ ⟨pl, 1⟩ → ∀ e' ∈ spentE B a', e'.owner = o → ∀ i, i < 2 * P.lay.lk + 2 →
      ¬ (e'.start.e ≤ base + ν₀ + i ∧ base + ν₀ + i < e'.start.e + e'.count.e)

/-- **The statement at the second lot's entry.** Not proved here; a lemma's statement, none of the
library's goals. -/
def IndexLotOnce : Prop :=
  ∀ (Xi : Type) (F : FileDescription Xi) (B : ProverCoinCounts) (pl : Place) (o : Addr) (sf el : Nat),
    B.word F = none → entryRunIs (spentE B ⟨pl, 1⟩) 1 o ⟨sf, el⟩ ⟨0, 1⟩ = true →
    ∀ a', a' ≠ ⟨pl, 1⟩ → ∀ e' ∈ spentE B a', e'.owner = o →
      ¬ (e'.start.e ≤ el ∧ el < e'.start.e + e'.count.e)

end ProofFile.Honest.K11
