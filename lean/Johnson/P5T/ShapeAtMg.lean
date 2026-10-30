-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5T/ShapeAtMg.lean: AT THE HEAD `AtMg`: THREE FACTS ON THE REQUEST's SHAPE THAT LAWS ON
THE KIND K9 TAKE AS PREMISES, EACH IN ITS CALLER's OWN FORM; AND SO THE CLOSED TEST `linkPlanB`
COMES DOWN TO ITS TWO CLAUSES ON THE BUILT SEGMENT. Four theorems. A joining: the evaluation is
Johnson/P5T/ShapeFacts.lean's; that the shape is the written one is
`AtMg.shape_full` (Johnson/P5J/ShapeFullAtMg.lean).
  `AtMg.shape_moments`: **every oracle message of segment m has a moment below 3**: the one
  premise hmom of `hall_of_moments` (Johnson/LPFK9R/HallOfMoments.lean), to the letter, at
  `Zp.first.shape`; at every m.
  `AtMg.shape_three`, `AtMg.shape_mask`: the fields three and mask of `LinkPlanFits`
  (Johnson/Desc/First/Link/Law/HtinPaid.lean), to the letter; the second at m below 25.
  `AtMg.linkPlan_of_two`: `linkPlanB Zp m X = true` from its two clauses on the built segment X: the
  arrays' sorts; every array has a name.
Limits. The two clauses on X are premises here: they follow from no pin. It stands over the
verifier's list of entry tests of thirteen rows alone (GLOSSARY.md, "entry tests"). The full size
alone. No probability: no soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5T.ShapeFacts
import Johnson.P5J.ShapeFullAtMg
import Johnson.Desc.First.Link.Law.HtinPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open OnBytes OnBytes.Model
open VerifiableInference
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.ReqLit (shapeFull)
open VerifiableInference.Desc.LinkJoin (linkPlanB sortsB look)
open OnBytes.Maker (WholeD)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **Every oracle message of a segment has a moment below 3.** -/
theorem AtMg.shape_moments (h : AtMg o Z D r Zp Np cF) (m : ℕ) :
    ∀ ms, (Zp.first.shape.link[m]?).map (·.messages) = some ms → ∀ x ∈ ms, x.moment < 3 := by
  intro ms hms x hx
  rw [h.shape_full] at hms
  cases e : shapeFull.link[m]? with
  | none =>
    rw [e] at hms
    cases hms
  | some L =>
    rw [e] at hms
    have e2 : L.messages = ms := Option.some.inj hms
    have k := P5T.shape_mem e
    unfold P5T.segShapeB at k
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at k
    exact k.1.2 x (e2 ▸ hx)

/-- A segment has at most three moments. -/
theorem AtMg.shape_three (h : AtMg o Z D r Zp Np cF) (m : ℕ) :
    ∀ L, Zp.first.shape.link[m]? = some L → reqMoments L ≤ 3 := by
  intro L hL
  rw [h.shape_full] at hL
  have k := P5T.shape_mem hL
  unfold P5T.segShapeB at k
  simp only [Bool.and_eq_true, decide_eq_true_eq] at k
  exact k.1.1

/-- One of a segment's messages has mask rows. -/
theorem AtMg.shape_mask (h : AtMg o Z D r Zp Np cF) (m : ℕ) (hm : m < 25) :
    ∃ L, Zp.first.shape.link[m]? = some L ∧
      (L.messages.any fun x => x.shape.maskRows != 0) = true := by
  have e25 : shapeFull.link.length = 25 := congrArg Prod.fst P5T.shape_ok
  have hl : m < shapeFull.link.length := by
    rw [e25]
    exact hm
  have e : shapeFull.link[m]? = some shapeFull.link[m] := List.getElem?_eq_getElem hl
  have k := P5T.shape_mem e
  unfold P5T.segShapeB at k
  rw [Bool.and_eq_true] at k
  exact ⟨_, by rw [h.shape_full]; exact e, k.2⟩

/-- **The closed test comes down to its two clauses on the built segment.** -/
theorem AtMg.linkPlan_of_two (h : AtMg o Z D r Zp Np cF) (m : ℕ) (hm : m < 25)
    (X : Stages.LinkH) (hs : sortsB (X.Fp.trees.toList.map look) X.tl = true)
    (hn : X.Fp.trees.size ≤ X.arrayOf.size) : linkPlanB Zp m X = true := by
  obtain ⟨L, hL, hk⟩ := h.shape_mask m hm
  unfold linkPlanB
  rw [hs, hL]
  simp only [Bool.true_and, Option.any_some, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hn, h.shape_three m L hL, hk⟩

end P5J

#print axioms P5J.AtMg.shape_moments
#print axioms P5J.AtMg.shape_three
#print axioms P5J.AtMg.shape_mask
#print axioms P5J.AtMg.linkPlan_of_two
