-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/FactsOfFold.lean: WHAT OUR BRIDGE ASKS OF THE CONDITION Rch (`FactsK13`,
Johnson/Desc/K13/Law/BridgeK13.lean) OUT OF THE ONE STRUCTURE OF FACTS ON THE VERIFIER's STATE
(`FoldFacts`, Johnson/Desc/First/FoldFacts.lean: statements alone). One statement
with its proof. `factsK13_of_fold`: at every statement that Rch admits whose state bears no mark.
  TWELVE FIELDS ARE SPENT: tidy, codes, shape, layout (our conjunct of "in order"); pileMasks,
    pileWithin, oneRow; weightsOk; bookInOrder, seatsCarried, msgShapes, bookFits. WHERE our
    layer's data has the structure's codes, shape and layout, the proximity test's data its first
    tree, seats and shapes; and `pubP` says nothing beside the test at the eight names.
What is not claimed. A member of `FoldFacts`. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.BridgeK13
import Johnson.Desc.First.FoldFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Slice
open VerifiableInference.Desc.First (S ModelPart Pub Meaning FoldData FoldFacts)
open VerifiableInference.Desc.K12.Door (K12Data)

/-- **`FactsK13` out of `FoldFacts`.** -/
theorem factsK13_of_fold {X Pp W : Type} {nR : ℕ} {Rch : ℕ → X → Prop} {at_ : X → Pp × S}
    {f : FoldData} {reqW : Pp → Array UInt32} {links : List ModelPart} {ps : List Place}
    (H : FoldFacts Rch at_ f reqW links ps) (D : DataK13 Pp W nR) (d : K12Data)
    (Mg : Meaning Pp W) (hc : D.codes = f.sent.codes) (hsh : D.shape = f.sent.shape)
    (hly : D.layout = f.sent.layout) (hft : d.ft = f.ft) (hL : d.L = f.L) (hM : d.M = f.M)
    (hq : ∀ q, cA13 q = true → ∀ x, Mg.pubP q x) (k : ℕ) (a : X) (hr : Rch k a)
    (hm : (at_ a).2.failed = none) : FactsK13 D d Mg (at_ a) where
  order := by
    unfold inOrderK13
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨H.tidy k a hr hm, by rw [hc]; exact H.codes k a hr hm⟩,
      by rw [hsh]; exact H.shape k a hr hm⟩, by rw [hly]; exact H.layout k a hr hm⟩
  masks := H.pileMasks k a hr hm
  within := H.pileWithin k a hr hm
  oneRow := H.oneRow k a hr hm
  weights := H.weightsOk k a hr hm
  book := by rw [hft]; exact H.bookInOrder k a hr hm
  seats := by rw [hL]; exact H.seatsCarried k a hr hm
  shapes := by rw [hM]; exact H.msgShapes k a hr hm
  fits := H.bookFits k a hr hm
  quiet := fun q h => hq q h _

end VerifiableInference.Desc.K13.Law
