-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/NoStrayLight.lean: kind K13, the members' batching: UNDER THE
LIBRARY's HEAD h NO HALF OF K13's LOT AT Zp STANDS AT A PLACE THAT THE FIRST CHAIN OF THE TERM
`P5J.F0T` DOES NOT HAVE, whatever the reader of the weights, the pile's filler and the letter G. Two
statements with their proofs; no definition. THE FULL SIZE AND THE FORMAT's EARLIER HASH ALONE.

Main names: `k13_place_in_ps`: **by the kernel**: the kind's place, ⟨1, none, 3, K13⟩, stands in the
library's written list of places (`P5J.At.ps`). `k13Lot_no_strays_light`: **the line.**

Why. It imports LotKind.lean of this folder
(over Part.lean, where the
lot `k13Lot` is defined)
and three files of the library.
It is for a caller whose imports do not
hold the kind's whole chain of laws.

How. The lot lays one half (`k13Lot_halves`), whose place is ⟨1, none, 3, K13⟩ (`k13Place_whereOf`;
both in LotKind.lean); under h the places of the first chain's sub-protocols are the written list
(the library's `P5J.At.places_paid`); the closed fact, for which the depth of recursion is raised
over that one theorem (maxRecDepth).

Related. THE GENERAL LAW: `ProofFile.Honest.K5.strays_of_ps` (Honest/K5/Law/NoStrayThree.lean): under h a
list of halves whose places all stand in the written list has no stray in the first chain: this line
is that law at the list of one half with `k13_place_in_ps`, and its proof is written anew here at
that one half. It is not imported: this file is to stand over the kind's own files and the library
alone. Like closed facts of other kinds stand in Honest/K5/Law/NoStrayLots.lean.

Limits. CONDITIONAL ON h: that h can be met is not shown here. An implication on places and lists:
nothing is said of what a half does. One closed fact by evaluation in Lean's kernel, which no
independent checker has replayed. This file's imports reach Johnson/Goal/: each of the library's
three files does; the hypothesis h (`P5J.AtMgA`) is stated over the goals' description. No
definition stands here.

What is not claimed. It is none of the library's goals. Nothing on soundness, completeness or
hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.LotKind
import Johnson.P5J.PlacesPaid
import Johnson.P5J.MgAtAll
import Johnson.P5J.AtTerm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open VerifiableInference.Desc (Chain Place)
open VerifiableInference.Desc.K13 (whereOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

set_option maxRecDepth 1000000 in
/-- **By the kernel**: the kind's place stands in the library's written list of places. -/
theorem k13_place_in_ps : (⟨1, none, 3, .K13⟩ : Place) ∈ P5J.At.ps := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {W₀ Rc Tr X : Type}

include h in
/-- **Under h no half of K13's lot at Zp stands at no place of the first chain of the term
`P5J.F0T`**, whatever the reader of the weights, the pile's filler and the letter G. -/
theorem k13Lot_no_strays_light (weights : W₀ → Weights)
    (pile : ProofFile.Pub → ProofFile.Ground → PileOf ProofFile.Inst) (G : ProofFile.Ground) :
    strays (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder
      ((k13Lot (Rc := Rc) (Tr := Tr) (X := X) weights pile).halves Zp G) = [] := by
  have hm : (⟨1, none, 3, .K13⟩ : Place) ∈ cF.blocksInOrder.map (·.place) := by
    have e : cF.blocksInOrder.map (·.place) = P5J.At.ps := P5J.At.places_paid h.scope h.reads h.laid
    rw [e]
    exact k13_place_in_ps
  obtain ⟨blk, hb, he⟩ := List.mem_map.1 hm
  have ha : (cF.blocksInOrder.any fun b => b.place ==
      (proverSideOfClaimCombination (Rc := Rc) (Tr := Tr) (X := X) weights (pile Zp G) (whereOf Zp)).place) = true :=
    List.any_eq_true.2 ⟨blk, hb, by
      rw [he, show (proverSideOfClaimCombination (Rc := Rc) (Tr := Tr) (X := X) weights (pile Zp G) (whereOf Zp)).place =
        k13Place (whereOf Zp) from rfl, k13Place_whereOf]
      rfl⟩
  rw [k13Lot_halves]
  show strays cF.blocksInOrder [proverSideOfClaimCombination (Rc := Rc) (Tr := Tr) (X := X) weights (pile Zp G) (whereOf Zp)] = []
  unfold strays
  rw [List.filter_cons_of_neg (by rw [ha]; decide)]
  rfl

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13_place_in_ps
#print axioms ProofFile.Honest.K13.k13Lot_no_strays_light
