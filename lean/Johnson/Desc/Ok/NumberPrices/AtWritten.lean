-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ok/NumberPrices/AtWritten.lean: towards the row number_prices with the plan as data.
Every round of the data of the library's written lists of the full size (`writtenKFull`,
`writtenPFull`, Johnson/Flat/Dec/FitAtWritten.lean) has a priced round at its place with `PricedAt`
(Johnson/Desc/Ok/NumberPrices/AtData.lean), where a file's three written priced plans pass one test
with code. The written priced plans are a letter here.

`pricedRounds_of_lists` is a tool, for all lists and plans. `PricedOfThree` speaks of the six
written lists, for all written priced plans: a tool at the written lists. No row is to be laid on
either. No planner runs in them, and no public file is named.

Definitions.
  `Three`: a file's three written priced plans (`Lit`, Johnson/Desc/Ok/NumberPrices/ByRuns.lean).
  `keyLitOk k T`, `proofLitOk k T`: `litOk` at each of the three, against its written list, with the
    bounds on work of `Desc.madeOk`: 32, 32, 32 at the key file's; 20, 28, 20 at the proof file's.
  `KeyPricedAt T`, `ProofPricedAt T`: `PricedRounds` of `writtenKFull` (`writtenPFull`) and the
    three plans.
  `PricedOfThree`: the closed statement: a yes of each test gives its clause.
Statements and proofs: `pricedRounds_of_lists`, `pricedOfThree`; `keyOk_of_lit`, `proofOk_of_lit`: a
yes gives the file's own test of `Desc.madeOk` at every record of the planner's type whose three
plans are these (for the proof file: and whose line on slots says 64). No evaluation is made here.

What holds a written error. From above, the test: the price is at most 2 ^ (work - 128)
(`roundHolds`). From below, nobody yet: whoever spends `PricedAt d r` has to show its own count
against r.error times the number of typed values, and no file does so today. Until then an error
here is a number that passes a bound, and no more. It is argued, one round at a time, that with both
proofs a wrong number makes one of the two fail, so that no tie to the planner is needed. The head
of Johnson/Desc/MadeOk.lean, written for a record that the planner makes, says that the level hangs
on that tie; the two heads differ, and which is kept is open. The argument does not cover a
condition between rounds: that all rounds of one stage are priced at one distance is read off the
field `group`, a written word. The test `rideB` (ByRuns.lean) is for saying truly whence the numbers
came.

What of OnBytes/Model/ is used: no statement here names anything of it. The file imports
Johnson/Desc/Ok/NumberPrices/AtData.lean, whose other theorems do: see its head.

Limits. The tests' yes is not shown here. They hold idly of errors 0: then `PricedAt` serves no
count but 0. `PricedRounds` carries the price alone: the bound on work, where work is counted, and
the tests on pairs and on words are in `Desc.chainAll`, which `litOk_parts` gives beside it. In a
written plan `why`, `group`, `rests`, `scope` and `wordFault` are the written record's own words.
That the written lists are what the planner makes of the public files, and that a description's data
are `writtenKFull`, `writtenPFull`, is not said here. The first list's last round and an entry under
the name "RECORD" are passed over, as in `PricedRounds`. The entry file's plan is in none of the six
lists. The small example is not covered. The limits of AtData.lean hold here.
-/
import Johnson.Desc.Ok.NumberPrices.AtData
import Johnson.Desc.Ok.NumberPrices.ByRuns
import Johnson.Flat.Dec.FitAtWritten
import OnBytes.Flat.WholeEntries

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Number.ByRuns
open VerifiableInference VerifiableInference.Number
open OnBytes OnBytes.Params OnBytes.Flat OnBytes.Flat.Held OnBytes.Maker
open Johnson.G Johnson.G.OfPlan

/-- **From three lists of written rounds and three plans that pass the test**, for all lists: the
data of the lists are priced place by place. -/
theorem pricedRounds_of_lists {a : ℕ} {R : Rounds × Rounds × Rounds} {P₁ P₂ P₃ : Planned}
    {w₁ w₂ w₃ : ℕ} (h₁ : Desc.chainOk w₁ P₁ = true) (h₂ : Desc.chainOk w₂ P₂ = true)
    (h₃ : Desc.chainOk w₃ P₃ = true)
    (a₁ : R.1.map (·.1.entry) = (chainRounds P₁).map (·.entry))
    (a₂ : R.2.1.map (·.1.entry) = (chainRounds P₂).map (·.entry))
    (a₃ : R.2.2.map (·.1.entry) = (chainRounds P₃).map (·.entry)) :
    PricedRounds (WholeD.of a (wholeAt (some R))) P₁ P₂ P₃ := by
  refine ⟨pricedAt_cut h₁ _ ?_, pricedAt_aligned h₂ _ ?_, pricedAt_aligned h₃ _ ?_⟩
  · unfold AlignedCut
    rw [List.map_map, List.map_dropLast, ← a₁]
    exact Flat.of_entry₁ a R.1 R.2.1 R.2.2
  · unfold Aligned
    rw [List.map_map, ← a₂]
    exact Flat.of_entry₂ a R.1 R.2.1 R.2.2
  · unfold Aligned
    rw [List.map_map, ← a₃]
    exact Flat.of_entry₃ a R.1 R.2.1 R.2.2

/-- A file's three written priced plans. -/
structure Three where
  A : Lit
  B : Lit
  C : Lit

/-- **The test on the key file's three written priced plans**, against the written lists. -/
def keyLitOk (k : ℕ) (T : Three) : Bool :=
  litOk 32 k dryKeyRecsFull dryKeyRunsFull0 T.A && litOk 32 k dryKeyRecsFull dryKeyRunsFull1 T.B &&
    litOk 32 k dryKeyRecsFull dryKeyRunsFull2 T.C

/-- **The test on the proof file's three written priced plans**, against the written lists. -/
def proofLitOk (k : ℕ) (T : Three) : Bool :=
  litOk 20 k dryProofRecsFull dryProofRunsFull0 T.A &&
    litOk 28 k dryProofRecsFull dryProofRunsFull1 T.B &&
    litOk 20 k dryProofRecsFull dryProofRunsFull2 T.C

/-- Every round of the key file's data at the written lists has a priced round at its place. -/
def KeyPricedAt (T : Three) : Prop := PricedRounds writtenKFull T.A.plan T.B.plan T.C.plan

/-- Every round of the proof file's data at the written lists has a priced round at its place. -/
def ProofPricedAt (T : Three) : Prop := PricedRounds writtenPFull T.A.plan T.B.plan T.C.plan

/-- A yes of each test gives its clause, at all written priced plans. -/
def PricedOfThree : Prop :=
  ∀ (k : ℕ) (T : Three), (keyLitOk k T = true → KeyPricedAt T) ∧
    (proofLitOk k T = true → ProofPricedAt T)

/-- **It holds.** -/
theorem pricedOfThree : PricedOfThree := by
  intro k T
  constructor
  · intro h
    simp only [keyLitOk, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    exact pricedRounds_of_lists (litOk_chainOk h1) (litOk_chainOk h2) (litOk_chainOk h3)
      (litOk_parts h1).2 (litOk_parts h2).2 (litOk_parts h3).2
  · intro h
    simp only [proofLitOk, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    exact pricedRounds_of_lists (litOk_chainOk h1) (litOk_chainOk h2) (litOk_chainOk h3)
      (litOk_parts h1).2 (litOk_parts h2).2 (litOk_parts h3).2

/-- A yes gives the key file's own test of `Desc.madeOk`, wherever the three plans are these. -/
theorem keyOk_of_lit {k : ℕ} {T : Three} (h : keyLitOk k T = true) (c : Configured)
    (hc : c.key = [T.A.plan, T.B.plan, T.C.plan]) : Desc.keyOk c = true := by
  simp only [keyLitOk, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  unfold Desc.keyOk
  rw [hc]
  exact Bool.and_eq_true_iff.2 ⟨Bool.and_eq_true_iff.2 ⟨(litOk_parts h1).1, (litOk_parts h2).1⟩,
    (litOk_parts h3).1⟩

/-- The like for the proof file, where the line on slots says `Desc.slots`. -/
theorem proofOk_of_lit {k : ℕ} {T : Three} (h : proofLitOk k T = true) (c : Configured)
    (hc : c.proof = [T.A.plan, T.B.plan, T.C.plan]) (hs : c.sized.lines.slots = Desc.slots) :
    Desc.proofOk c = true := by
  simp only [proofLitOk, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  unfold Desc.proofOk
  rw [hc]
  exact Bool.and_eq_true_iff.2 ⟨Bool.and_eq_true_iff.2 ⟨Bool.and_eq_true_iff.2
    ⟨(litOk_parts h1).1, (litOk_parts h2).1⟩, (litOk_parts h3).1⟩, decide_eq_true hs⟩

end VerifiableInference.Number.ByRuns

#print axioms VerifiableInference.Number.ByRuns.pricedRounds_of_lists
#print axioms VerifiableInference.Number.ByRuns.pricedOfThree
#print axioms VerifiableInference.Number.ByRuns.keyOk_of_lit
#print axioms VerifiableInference.Number.ByRuns.proofOk_of_lit
