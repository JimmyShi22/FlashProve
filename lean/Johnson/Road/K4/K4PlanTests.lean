-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PlanTests.lean: WHAT THE LINES OF K4's ROW AT THE TABLE OF JOINTS THAT GO THROUGH
THE PINS ASK OF THE PUBLIC PARAMETERS, IN A GROUP THAT IS NOT THE FIRST (the Lean structure
`K4PlanFit`, Johnson/Road/K4/K4PinsEnd.lean), FROM ELEVEN TESTS WITH CODE THAT WALK NO SYMBOL.
`K4PlanFit` is one premise of `k4_own_end` among many: the row is not paid by it. One definition
with code; one Lean structure, whose fields are all of the form "a test says true"; three theorems.
Glue: calls; no draw, no count.

  `seatsAsShapesB`: every entry of L has as many seats as shapes.
  `groupsSeated_of_lengths`: `GroupsSeated (msOf L) N` from it, `groupsAreMembers` and hEnd.
  `K4PlanTests`: eleven tests. Of the programs: `Codes.lengthsOk`, `reqShapeOk`, `reqLayoutOk`.
    In the library: `nmFit`, `pairFit`. From other files: `groupsAreMembers`, `shapesTiedB`.
    This file's, or of K4PinsBools.lean | SymsOfLayout.lean | SeamOfLayout.lean: `sitsInB`, `symTieB` at every matrix, `seamArrB`, `seatsAsShapesB`.
  `three_of_tests`: `SitsIn`, `SymsOne`, `SeamFit` at ms := msOf L, s := Meaning.sizesOf X,
    seat := seatBy (fLay D.layout num) X (Meaning.sizesOf X).
  `k4PlanFit_of_tests`: `K4PlanFit` there, by `planFit_of_tests`
    (Johnson/Road/K4/K4PinsPlanOf.lean), which has the other six fields as theorems or lines on
    numbers.

BESIDE THE TESTS. hEnd: the groups beyond segment n are empty: a sentence over all numbers: no test
can say it; it is a lemma on whatever makes N. 0 < p.g < 12. And what `planFit_of_tests` takes:
`PublicSteps`, `RefPub`, the two lines on p, `PlaceIs x p 0` (a theorem at the place that is made:
`ties_of_plan`, Johnson/Road/K4/K4PinsScope.lean: not called here), three lines on numbers.

ELDER: `groupsSeated_of_B` (GroupsSeatedB.lean)
has the same conclusion under `seatsFitB G cs L`, a test that reads the whole IOP as written in
Lean; its proof spends that test's first clause alone: as many seats as shapes. Here that clause is
the premise, and the elder's twelve lines are walked anew: so no letter G is wanted.

NO RUN IS A PART OF THIS FILE, AND AN EVALUATOR's YES IS NO PROOF BY THE KERNEL. Which of the tests
have run, where, and with which negative tests, stands in notes not in this repository, not here.

Limits. K04_law IS NOT PROVED BY THIS. The letters num, arr, N, L, seatT, D and the numbers n, hd
are free here: their makers off the public parameters stand in no library file; "m is not hd"
says something only at hd := the head's link. ONE LETTER, THREE ROLES: 2 p.g is the sub-proof, the
segment of N.group and, through a label's owner, a link of the layout: nothing ties these. The first
group: Johnson/Road/K4/K4PlanTestsFirst.lean.
-/
import Johnson.Road.K4.K4PinsPlanOf
import Johnson.Road.K4.K4PinsBools
import Johnson.Road.K4.SeamOfLayout
import Johnson.Road.K4.SymsOfLayout
import Johnson.Road.K4.LayoutTies
import Johnson.Desc.First.BordersPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes
open OnBytes.Model.Layer (matIx)
open OnBytes.Model.Verify (Public)
open VerifiableInference.PlanWritten (PublicSteps)
open OnBytes.Desc.First.K4 (Par)
open VerifiableInference.Desc (MemberLists allSeats)
open VerifiableInference.Desc.First (Numbers groupsAreMembers)
open VerifiableInference.Desc.First.Look (Sent sigListCalls szOf pubAt stepOf)
open VerifiableInference.Desc.Sound (msOf seatOf GroupsSeated Sending)
open Johnson.Road.K4.LayoutTies (shapesTiedB shapesTied_of_B)
open Meaning (nmFit pairFit seatBy fLay follows_sizesOf)
open Inst.Model.Layout (kRef hRef)

/-- Every entry has as many seats as shapes. -/
def seatsAsShapesB (L : MemberLists) : Bool := L.all fun e => e.1.length == e.2.length

/-- **Every tenant of every segment's group is the seat of a member**, from two tests on lists and
"the groups beyond segment n are empty". -/
theorem groupsSeated_of_lengths (L : MemberLists) (h : seatsAsShapesB L = true) (N : Numbers)
    (n : ℕ) (hG : groupsAreMembers N n L = true) (hEnd : ∀ k, n < k → N.group k = []) :
    GroupsSeated (msOf L) N := by
  intro k x hx
  by_cases hk : n < k
  · rw [hEnd k hk] at hx
    cases hx
  · have h1 := List.all_eq_true.1 hG x (List.mem_append_left _
      (List.mem_flatMap.2 ⟨k, List.mem_range.2 (by omega), hx⟩))
    obtain ⟨e, he, hxe⟩ := List.mem_flatMap.1 (List.contains_iff_mem.1 h1 : x ∈ allSeats L)
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hxe
    have hi' : i < e.1.length := (beq_iff_eq.1 (List.all_eq_true.1 h e he)) ▸ hi
    refine ⟨⟨Sending.ofLists e.1 e.2, ⟨i, hi'⟩⟩, ?_, ?_⟩
    · exact List.mem_flatMap.2 ⟨Sending.ofLists e.1 e.2, List.mem_map.2 ⟨e, he, rfl⟩,
        List.mem_map.2 ⟨⟨i, hi'⟩, List.mem_finRange _, rfl⟩⟩
    · show e.2.getD i (0, 0) = e.2[i]
      exact List.getD_eq_getElem _ _ hi

variable {X : Public} {p : Par} {rows cols : ℕ}
  (x : VerifiableInference.Desc.First.Look.Place) (D : Sent)
  (rad : OnBytes.OracleShape → ℕ) (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ)
  (posI : ℕ → Bool × ℕ × ℕ) (oW : Cb.OMsg Cb.Gl.E)
  (enc : (Fin rows → Fin cols → Cb.Gl.E) → oW.Msg) (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E)
  (num arr : ℕ → ℕ → ℕ) (L : MemberLists) (N : Numbers) (m n : ℕ)

/-- **The tests.** Every field: a test with code says true. None walks a symbol. -/
structure K4PlanTests : Prop where
  sits : sitsInB (sigListCalls D rad x.link) seatT (msOf L) N m = true
  syms : ((List.range (Meaning.sizesOf X (2 * p.g)).NM).all fun μ =>
    symTieB (planAt x D rad seatT (cutW enc wOf hRef (2 ^ kRef)) posI) num arr N (2 * p.g) p.hp.tl
      X (Meaning.sizesOf X) μ) = true
  lens : D.codes.lengthsOk = true
  shape : reqShapeOk D.shape = true
  layout : reqLayoutOk D.codes D.shape D.layout = true
  nm : nmFit X = true
  tied : shapesTiedB D.codes D.shape D.layout num arr L (fun k => N.group k) = true
  lengths : seatsAsShapesB L = true
  groups : groupsAreMembers N n L = true
  pair : pairFit X (2 * p.g) (matIx X.y).iXI (2 * (p.g - 1)) (matIx X.y).iXO = true
  seamArr : seamArrB X (Meaning.sizesOf X) D.layout num arr N (2 * p.g) (2 * (p.g - 1))
    (matIx X.y).iXI = true

variable {x D rad seatT posI oW enc wOf num arr L N m n}

/-- **The tests give the three conditions that are no theorems**, at ms := msOf L, the sizes off the
public parameters and the seats off the layout; beside them: hEnd and 0 < p.g < 12. -/
theorem three_of_tests
    (T : K4PlanTests (X := X) (p := p) x D rad seatT posI oW enc wOf num arr L N m n)
    (hEnd : ∀ k, n < k → N.group k = []) (hg : p.g < 12) (hg0 : 0 < p.g) :
    SitsIn (sigListCalls D rad x.link) seatT (msOf L) N m ∧
    SymsOne (planAt x D rad seatT (cutW enc wOf hRef (2 ^ kRef)) posI) p.hp.tl arr N (2 * p.g)
      (Meaning.sizesOf X (2 * p.g)) (seatBy (fLay D.layout num) X (Meaning.sizesOf X) (2 * p.g)) ∧
    SeamFit arr (msOf L) N (Meaning.sizesOf X) (seatBy (fLay D.layout num) X (Meaning.sizesOf X))
      D.codes X.y p.g :=
  ⟨sitsIn_of_B T.sits,
    symsOne_of_layout _ num arr N (2 * p.g) p.hp.tl rfl fun μ hμ =>
      List.all_eq_true.1 T.syms μ (List.mem_range.2 hμ),
    seamFit_of_layout T.lens T.shape T.layout (follows_sizesOf T.nm) (shapesTied_of_B T.tied)
      (groupsSeated_of_lengths L T.lengths N n T.groups hEnd) hg0 hg T.pair T.seamArr⟩

/-- **`K4PlanFit` from the eleven tests**, hEnd, 0 < p.g, and what `planFit_of_tests` takes. -/
theorem k4PlanFit_of_tests {pol KL : ByteArray} {tk : Array Nat} (hd : ℕ)
    (T : K4PlanTests (X := X) (p := p) x D rad seatT posI oW enc wOf num arr L N m n)
    (hEnd : ∀ k, n < k → N.group k = []) (hg0 : 0 < p.g) (St : PublicSteps pol KL X)
    (B : RefPub X p.g) (hP : p.P = { X.layers with tokv := tk }) (hG : X.G[p.g]? = some p.hp)
    (hg : p.g < 12) (P0 : PlaceIs x p 0) (hgr : m / stepOf X = p.g) (hm : m = 2 * p.g)
    (hhd : m ≠ hd) :
    K4PlanFit (X := X) (p := p) x (pubAt X (m / stepOf X)) D rad seatT posI oW enc wOf arr (msOf L)
      N m (szOf p.hp.tl).NM ((Finset.range (szOf p.hp.tl).NM).sup (szOf p.hp.tl).m)
      ((Finset.range (szOf p.hp.tl).NM).sup (szOf p.hp.tl).k) 0 (Meaning.sizesOf X)
      (seatBy (fLay D.layout num) X (Meaning.sizesOf X)) hd :=
  planFit_of_tests x D rad seatT posI oW enc wOf arr (msOf L) N m _ hd St B hP hG hg P0 hgr hm hhd
    (three_of_tests T hEnd hg hg0).1 (three_of_tests T hEnd hg hg0).2.1
    (three_of_tests T hEnd hg hg0).2.2

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.groupsSeated_of_lengths
#print axioms OnBytes.Road.K4.three_of_tests
#print axioms OnBytes.Road.K4.k4PlanFit_of_tests
