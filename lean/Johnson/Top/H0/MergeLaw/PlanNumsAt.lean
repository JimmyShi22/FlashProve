-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/PlanNumsAt.lean: FOUR EQUATIONS ON THE PLANNER's NUMBERS that the theorem
`mergeFill_at` (Johnson/Desc/Sound/MgAt/K11.lean) takes as premises (hns, hlay, hnR, hkC), at the
terms that are meant for the composed meaning's parameters at the proof file's public part Z:
built := Z.p.built.links, d1 := `FillP1.d1At Z` (Johnson/Top/H0/Fill/D1At.lean), P13 :=
`K13.whereOf Z` (Johnson/Desc/ProofFile/Lot/K13.lean), Pm := `K11.parOf Z G₀`
(Johnson/Desc/ProofFile/Lot/K11.lean), G₀ the ground for a request of zeros. One of the four is a
theorem at every Z. Three follow from tests with code. Definitions, statements and proofs.

Main names.
  `hlay_at`: hlay: the layout in `d1At Z` is the merge's. AT EVERY Z: no file is read, no number
    evaluated: the ground that is made of Z has Z's own public data (`ProofFile.Law.blankBy_W`,
    Johnson/Desc/ProofFile/Law/MakerPublic.lean).
  `parOf_nMsg`: the merge's number of slots is the public data's.
  `nsB Z m`: a test: the planner's link number m has as many slots as the public data's head.
  `nRB Z nR`: a test: nR is the number of rows of the committed table's layout.
  `kColB lin lay`: a test: the row's shape has as many column bits as the layout.
  `numsB Z m nR`: the three.
  `nums_of_test`: hns, hnR, hkC, in `mergeFill_at`'s own letters, from `numsB Z m nR = true`.
  `lay_room_at`, `lay_room_pub`: beside the row: `mergeFill_at`'s h and hn at Pm: where Z's public
    data are a return of the planner's text (`publicO_merge`,
    Johnson/Top/H0/MergeLaw/PlanNums.lean);
    so wherever Z is made of three public files by the road that the IOP as written in Lean takes
    (`ProofFile.Law.pub_public`).
Limits. THE THREE TESTS ARE SHOWN TRUE AT NO Z HERE: an evaluation at the stored full-size public
files stands in ZzK11Nums.lean (a file that is not in this library), and an evaluation is no proof.
THE TERMS ARE THE MEANT ONES. The closed value of the composed meaning's parameters (`P5J.At.𝔇At`,
P5J/LettersRec.lean) lays built as here, by its text and by report. It does not lay
d1, P13 and the index nR: that these terms are meant for it is by report. nR IS AN INDEX
OF THE PARAMETERS' TYPE: hnR holds of the closed value only if that index is the layout's number of
rows, which at the stored full-size files is 3,076,096 and no power of two. `nRB` compares a letter
with that number: whoever lays nR as that very number passes it by definition; as an example it
shows the number's value and nothing else. THAT THE CONCLUSIONS ARE `mergeFill_at`'s PREMISES TO THE
LETTER IS BY READING: that file (Johnson/Desc/Sound/MgAt/K11.lean) is not among this file's
imports.
Nothing on a verifier's state. Nothing on soundness or hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.H0.Fill.D1At
import Johnson.Top.H0.MergeLaw.PlanNums
import Johnson.Desc.ProofFile.Law.MakerPublic
import Johnson.Desc.ProofFile.Lot.K11
import Johnson.Desc.ProofFile.Lot.K13

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes OnBytes.Model

variable {mk : ProofFile.LinksBy} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground}

/-- **hlay, at every Z**: the layout in `d1At Z` is the merge's. -/
theorem hlay_at (h : ProofFile.blankBy mk Z = some G₀) :
    (FillP1.d1At Z).lay = (K11.parOf Z G₀).lay := by
  show Z.p.X.layers.wsLay = G₀.W.layers.wsLay
  rw [ProofFile.Law.blankBy_W h]

/-- The merge's number of slots is the public data's. -/
theorem parOf_nMsg (h : ProofFile.blankBy mk Z = some G₀) : (K11.parOf Z G₀).nMsg = Z.p.X.H.nMsg := by
  show G₀.W.H.nMsg = Z.p.X.H.nMsg
  rw [ProofFile.Law.blankBy_W h]

/-- A test: the planner's link number m has as many slots as the public data's head. -/
def nsB (Z : ProofFile.Pub) (m : ℕ) : Bool :=
  decide ((Z.p.built.links[m]?).map (·.ns) = some Z.p.X.H.nMsg)

/-- A test: nR is the number of rows of the committed table's layout. -/
def nRB (Z : ProofFile.Pub) (nR : ℕ) : Bool := decide (nR = Z.p.X.layers.wsLay.m0)

/-- A test: the row's shape has as many column bits as the layout. -/
def kColB (lin : Params.LinShape) (lay : WsLay) : Bool := decide (lin.kCol = lay.lk)

/-- The three. -/
def numsB (Z : ProofFile.Pub) (m nR : ℕ) : Bool :=
  nsB Z m && nRB Z nR && kColB (VerifiableInference.Desc.K13.whereOf Z).lin Z.p.X.layers.wsLay

/-- **hns, hnR, hkC, in `mergeFill_at`'s own letters at the meant terms, from the three tests.** -/
theorem nums_of_test {m nR : ℕ} (h : ProofFile.blankBy mk Z = some G₀) (ht : numsB Z m nR = true) :
    (Z.p.built.links[m]?).map (·.ns) = some (K11.parOf Z G₀).nMsg ∧
      nR = (FillP1.d1At Z).lay.m0 ∧
      (VerifiableInference.Desc.K13.whereOf Z).lin.kCol = (FillP1.d1At Z).lay.lk := by
  unfold numsB nsB nRB kColB at ht
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
  exact ⟨by rw [parOf_nMsg h]; exact ht.1.1, ht.1.2, ht.2⟩

/-- **Beside the row: `mergeFill_at`'s h and hn at Pm**, where Z's public data are a return of the
planner's text with the second hash function as an argument. -/
theorem lay_room_at (o : Nat → ByteArray → ByteArray) {pol KL : ByteArray}
    {layout : Option ByteArray} (h : ProofFile.blankBy mk Z = some G₀)
    (hX : VerifiableInference.PlanWritten.publicOfO o pol KL layout = .ok Z.p.X) :
    (∃ s p3 lkW, wsLayOf s p3 lkW = .ok (K11.parOf Z G₀).lay) ∧
      2 * (K11.parOf Z G₀).lay.lk + 3 ≤ (K11.parOf Z G₀).nMsg := by
  rw [← hlay_at h, parOf_nMsg h]
  exact publicO_merge o hX

/-- So wherever Z is made of three public files by the road that the IOP as written in Lean
takes. -/
theorem lay_room_pub {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray}
    (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z) (h : ProofFile.blankBy mk Z = some G₀) :
    (∃ s p3 lkW, wsLayOf s p3 lkW = .ok (K11.parOf Z G₀).lay) ∧
      2 * (K11.parOf Z G₀).lay.lk + 3 ≤ (K11.parOf Z G₀).nMsg :=
  lay_room_at o h (ProofFile.Law.pub_public hZ)

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.hlay_at
#print axioms VerifiableInference.Desc.First.MergeLaw.parOf_nMsg
#print axioms VerifiableInference.Desc.First.MergeLaw.nums_of_test
#print axioms VerifiableInference.Desc.First.MergeLaw.lay_room_at
#print axioms VerifiableInference.Desc.First.MergeLaw.lay_room_pub
