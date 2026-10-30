-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/SeamArrInScope.lean: THE TEST seamArrB (Johnson/Road/K4/SeamOfLayout.lean) AT THE
SEAM BETWEEN GROUP g - 1 AND GROUP g, RESTATED UNDER THE PUBLIC CORE AS A TEST THAT READS THE
LAYOUT FILE's ITEM AND THE SEATS ALONE: nothing of the public parameters X.

  `seamLayB layout num arr N y g`: the test with the owner 2 (g - 1), the name of the entry "the
    stream that goes out" and the two sizes read off the layers' layout y.
  **`seamArr_iff_lay`**: for 0 < g < 12: seamArrB at X, the library's own sizes, segments 2 g and
    2 (g - 1) and the entry "the stream that comes in" IS seamLayB at X.y: an equation of the two
    Bools. `seamArr_of_lay`: its one direction.
  `seamClosedB layout num arr N g`: the same with the name "M7" and the sizes 65536 and 400
    written out: neither X nor y is read.
  **`seamLay_iff_closed`**: seamLayB at X.y IS seamClosedB. `seamArr_of_closed`: so an accept of the
    closed test gives seamArrB's.
PREMISES of each theorem: h: X is what publicOf returns · C: Hd.PublicCore X.P (in the goals' scope:
Hd.core_of_scope).
No new argument: entryG (Johnson/Goal/Meaning/HidPlanFit.lean), follows_of_core
(Johnson/Goal/Meaning/HidPlanNM.lean), owner_label (Johnson/Goal/Meaning/HidSeatsOf.lean),
ix_of_core (Johnson/Goal/Meaning/HidOwner.lean), xoNum_of_core (Johnson/Goal/Meaning/HidHead.lean).
Limits. The tests have been evaluated here at no layout. The reference sizes alone. K04_law, the law
of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.


-/
import Johnson.Road.K4.SeamOfLayout
import Johnson.Goal.Meaning.HidHead
import Johnson.Goal.Meaning.HidPlanNM
import Johnson.Goal.Meaning.HidSeatsOf
import Johnson.Goal.Meaning.HidPlanFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes
open OnBytes.Params (ReqLayout)
open OnBytes.Model.Verify (publicOf)
open OnBytes.Model.Layer (Lay matIx)
open VerifiableInference.Desc (arrayOf)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Sound (namedOnce)
open Meaning (labAt ownerK ownerA nameOf matsAt)

/-- The test at the seam, off the layers' layout. -/
def seamLayB (layout : ReqLayout) (num arr : ℕ → ℕ → ℕ) (N : Numbers) (y : Lay) (g : ℕ) : Bool :=
  match arrayOf layout (2 * (g - 1)) (nameOf (matIx y).iXO) with
  | none => false
  | some A => A.sizeI == Alg.symRows y.mxb && A.sizeC == y.kxb &&
      namedOnce arr N (2 * g) (num (2 * (g - 1)) A.message) &&
      namedOnce arr N (2 * (g - 1)) (num (2 * (g - 1)) A.message)

/-- The test at the seam, with the name and the two sizes written out. -/
def seamClosedB (layout : ReqLayout) (num arr : ℕ → ℕ → ℕ) (N : Numbers) (g : ℕ) : Bool :=
  match arrayOf layout (2 * (g - 1)) (nameOf 7) with
  | none => false
  | some A => A.sizeI == Alg.symRows 65536 && A.sizeC == 400 &&
      namedOnce arr N (2 * g) (num (2 * (g - 1)) A.message) &&
      namedOnce arr N (2 * (g - 1)) (num (2 * (g - 1)) A.message)

variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}
  {layout : ReqLayout} {num arr : ℕ → ℕ → ℕ} {N : Numbers} {g : ℕ}

/-- **Under the public core seamArrB at the seam is seamLayB.** -/
theorem seamArr_iff_lay (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) (h0 : 0 < g)
    (hg : g < 12) :
    seamArrB X (_root_.Meaning.sizesOf X) layout num arr N (2 * g) (2 * (g - 1))
      (matIx X.y).iXI = seamLayB layout num arr N X.y g := by
  have hk : 2 * g < 25 := by omega
  obtain ⟨M, hM, em, ek, _⟩ := Meaning.entryG h C hg (mat := 4) (by decide) (by decide)
  have hM' : (matsAt X (2 * g))[(matIx X.y).iXI]? = some M := hM
  have ha : (matIx X.y).iXI < (matsAt X (2 * g)).size := (Array.getElem?_eq_some_iff.1 hM').1
  have F := Meaning.follows_of_core h C
  have sm : (_root_.Meaning.sizesOf X (2 * g)).m (matIx X.y).iXI = X.y.mxb := by
    rw [F.m _ hk _ ha, Meaning.getD_of hM']
    exact em
  have sk : (_root_.Meaning.sizesOf X (2 * g)).k (matIx X.y).iXI = X.y.kxb := by
    rw [F.k _ hk _ ha, Meaning.getD_of hM']
    exact ek
  have ol := Meaning.owner_label h C hk ha
  have oo : Meaning.ownerOf X (2 * g) (matIx X.y).iXI = (2 * (g - 1), (matIx X.y).iXO) := by
    unfold Meaning.ownerOf
    rw [if_neg (by omega), if_neg (by omega), if_pos ⟨rfl, by omega⟩,
      show 2 * g - 2 = 2 * (g - 1) by omega]
  rw [oo] at ol
  have eK : ownerK (labAt X (2 * g) (matIx X.y).iXI) = 2 * (g - 1) := congrArg Prod.fst ol
  have eA : ownerA (labAt X (2 * g) (matIx X.y).iXI) = (matIx X.y).iXO := congrArg Prod.snd ol
  unfold seamArrB seamLayB
  rw [eK, eA, sm, sk]
  cases arrayOf layout (2 * (g - 1)) (nameOf (matIx X.y).iXO) <;> rfl

/-- Its one direction. -/
theorem seamArr_of_lay (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) (h0 : 0 < g)
    (hg : g < 12) (hB : seamLayB layout num arr N X.y g = true) :
    seamArrB X (_root_.Meaning.sizesOf X) layout num arr N (2 * g) (2 * (g - 1))
      (matIx X.y).iXI = true := by
  rw [seamArr_iff_lay h C h0 hg]
  exact hB

/-- **Under the public core seamLayB at X's layout is the closed test.** -/
theorem seamLay_iff_closed (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) :
    seamLayB layout num arr N X.y g = seamClosedB layout num arr N g := by
  obtain ⟨_, i7, _⟩ := Meaning.ix_of_core h C
  have Nn := Meaning.xoNum_of_core h C
  unfold seamLayB seamClosedB
  rw [i7, Nn.mxb, Nn.kxb]

/-- An accept of the closed test gives seamArrB's. -/
theorem seamArr_of_closed (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) (h0 : 0 < g)
    (hg : g < 12) (hB : seamClosedB layout num arr N g = true) :
    seamArrB X (_root_.Meaning.sizesOf X) layout num arr N (2 * g) (2 * (g - 1))
      (matIx X.y).iXI = true :=
  seamArr_of_lay h C h0 hg ((seamLay_iff_closed h C).trans hB)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.seamArr_iff_lay
#print axioms OnBytes.Road.K4.seamArr_of_lay
#print axioms OnBytes.Road.K4.seamLay_iff_closed
#print axioms OnBytes.Road.K4.seamArr_of_closed
