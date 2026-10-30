-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/Road/K4/K4NamedFirst.lean: TWO OF THE NINE NAMED TESTS OF K4's ROW (the structure
K4NamedW, Johnson/Road/K4/K4RowAtWide.lean) AS THEOREMS AT THE COMPOSED MEANING's CLOSED CONSTANT
(Johnson/P5J/MgAtAll.lean): toldFit and book. Two statements with their proofs: CALLS of other
files' theorems: no new argument.

  `toldFit_const`: k4ToldFit accepts at the written lists and at what the first chain's own
    sub-protocols tell. Premises: hA, the one head (it pays the scope, readFiles and, by its field
    laid.planOk, "the sub-protocols are shaped") · O, an opening (the head's field laid.opened has
    one). By `k04_toldFit` (Johnson/Road/K4/ToldAtK4.lean).
  `book_const`: bookFit accepts at the constant's own numbers. Premise: hA, for the constant's
    name alone. By `bookFit_withTold` (Johnson/Desc/First/BookFitTold.lean) and
    `ProofFile.Law.flatPlaces_nodup`. BY THE MAKE OF THE NUMBERS: the test compares a thing with itself
    there: its accept carries no content (that file's own limit (2)).
At which meaning: none: both are tests on public data.
Limits. A MEMBER OF THE HEAD IS PROVED AT `storedPublicFiles` AND `zGap` ALONE (AT secondHashFunction; SIDE LIBRARY
AtFullSide/Top/). The full size alone. K04_law, the law of K4's
sub-protocol itself, IS NOT PROVED. Nothing on soundness.


-/
import Johnson.Road.K4.ToldAtK4
import Johnson.Desc.First.BookFitTold
import Johnson.Desc.ProofFile.Law.KindPlaces
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S flatPlacesOf bookFit bookFit_withTold)
open VerifiableInference.Desc.First.FillK4 (k4ToldFit)
open VerifiableInference.Desc.Sound (linksFull planOk_parts)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **toldFit at the constant's letters: at every place of K4's the sub-protocol tells no tree.** -/
theorem toldFit_const (hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (Desc.K14.Law.seatZ Zp Np) (Desc.K14.Law.secondAt Zp Np)) :
    k4ToldFit linksFull (flatPlacesOf linksFull true)
      (cF.blocksInOrder.map fun b => b.oracles.flatMap id) = true :=
  k04_toldFit hA.scope hA.reads O (planOk_parts _ hA.laid.planOk).1

/-- **book at the constant's own numbers**: by their make. -/
theorem book_const (hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) :
    bookFit hA.𝔇.N (flatPlacesOf linksFull true)
      (cF.blocksInOrder.map fun b => b.oracles.flatMap id) = true := by
  have e : linksFull = P5J.fullLinks := rfl
  rw [e]
  show bookFit (P5J.At.N Zp cF) (flatPlacesOf P5J.fullLinks true)
    (cF.blocksInOrder.map fun b => b.oracles.flatMap id) = true
  unfold P5J.At.N P5J.At.ps P5J.At.told VerifiableInference.Desc.Sound.toldOf
  exact bookFit_withTold _ _ _ (ProofFile.Law.flatPlaces_nodup P5J.fullLinks true)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.toldFit_const
#print axioms OnBytes.Road.K4.book_const
