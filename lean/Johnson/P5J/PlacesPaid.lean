-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/PlacesPaid.lean: FROM THE ONE HEAD, AT THE FORMAT's SECOND HASH: THE FIRST CHAIN's SUB-PROTOCOLS' PLACES ARE THE WRITTEN LIST; SO THE NAMED TEST "poss" IS A THEOREM, AND THE TABLE's NUMBERS ARE "THE NUMBERS CLOSED OVER THE SUB-PROTOCOLS". Four theorems. A joint build of files of several kinds.
  places_paid: in scope, from LaidAt at OnBytes.secondHashFunction: blockPlaces cF.blocksInOrder = At.ps: another file's theorem (LPFK9.blockPlaces_full, Johnson/LPFK9R/SubsFull.lean, over places_any | subs_all, Johnson/IMR/PlacesScope.lean) at what LaidAt's field "opened" hands over.
  poss_at · N_at: "poss" holds · At.N Zp cF = (numbersOf pseats).atBlocks shape links cF.blocksInOrder.
  At.PlanOk.of_five: SO PlanOk FOLLOWS, IN SCOPE, FROM LaidAt AND FIVE TESTS: laid · named · fit · groups · radii.
Limits. At OnBytes.secondHashFunction (there the counted laws are owed). It shows none of the five to accept. The full size alone. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.PlanOkPaid
import Johnson.P5J.PossPaid
import Johnson.P5J.LaidOpens
import Johnson.LPFK9R.SubsFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J.At
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (blockPlaces possThereB)
open OnBytes.Maker (WholeD)

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **The sub-protocols' places are the written list.** -/
theorem places_paid (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) : blockPlaces cF.blocksInOrder = ps := by
  obtain ⟨Bs, base, O⟩ := L.opened
  exact LPFK9.blockPlaces_full hZ hR O

theorem poss_at (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    possThereB cF.blocksInOrder links.length = true := poss_paid cF (places_paid hZ hR L)

theorem N_at (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    N Zp cF = (P5T.numbersOf (pseats Zp)).atBlocks (shape Zp) links cF.blocksInOrder :=
  N_atBlocks Zp cF (places_paid hZ hR L)

/-- **PlanOk from LaidAt and five tests, in scope.** -/
theorem PlanOk.of_five (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (laid : Meaning.laidThere (X Zp) (Meaning.sizesOf (X Zp)) (layout Zp) = true)
    (named : seatsNamedC (X Zp) (Meaning.sizesOf (X Zp)) (layout Zp) (num Zp) (arr Zp) (N Zp cF) = true)
    (fit : P5T.seatsFitP (F0T OnBytes.secondHashFunction Zp Np cF) (cs Zp) (pseats Zp) = true)
    (groups : P5T.groupsP (N Zp cF) (nG Zp) (pseats Zp) = true)
    (radii : P5T.radIsB ((P5T.rowsAt? Zp.pol Z.lay Zp.KL).getD []) Zp.made.proof.1.sends.length
      (rad Zp Z.lay) (pseats Zp) = true) :
    PlanOk OnBytes.secondHashFunction Zp Np cF Z.lay :=
  PlanOk.of_six hZ L.pub Np cF laid named fit groups radii (poss_at hZ hR L)

end P5J.At

#print axioms P5J.At.places_paid
#print axioms P5J.At.poss_at
#print axioms P5J.At.N_at
#print axioms P5J.At.PlanOk.of_five
