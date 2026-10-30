-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/K6CallsText.lean: the last of the seven conditions in front of the law on the
sub-protocol K6 at the head (`K6LeftSeven`): `callsC`: the matrices that the lookup
on the head's calls reads sit as planned. At the head it comes down to one small closed test on one
list: eight names in the built segment 24's list of arrays.

Row or tool. Closed facts on written values with negative tests, and a law at the head by rewriting
through named ties. A payer for a premise of another law, under one named premise.

The test's text. The condition is `AtFold.callsSeatedC` (Johnson/Desc/Kinds/Law/K6CallsTest.lean).
Its owners have shown that it is `callsSeatedV`, the same test at plain values (`callsSeatedC_view`,
Johnson/Desc/Kinds/Law/K6CallsView.lean). Neither file is imported by name. Here
`memberText`, `insideText`, `callText` and `callsText` spell out `memberOf`, `insideB`, `callV` and
`callsSeatedV`; `sitsText` is that of K6MaskText.lean. The file K6CallsAtHead.lean beside this one
says the condition at its own name.

The premise that is left. `callNamesB arrs = true` at `arrs`, the built segment 24's list of arrays:
at the number of each of the head's eight matrices' symbol arrays the list names the array that the
matrix's label names. The numbers and the labels are the written view's. By the text of the list's
maker (`declareLinks`, OnBytes/Model/StagesLinks.lean) the list is made of fields of the public data
that no test on written values holds and the view does not show. No law on that maker gives these
eight names yet.

What else the test reads, and the ties: as in K6MaskText.lean; beside: the layout: `layoutFull`, by
`layout_in_scope`; the labels and the numbers of the symbol arrays: the written view, by
`xShape_in_scope` with `viewTail_at` and `viewEntry_at` (TailAtView.lean); the number NHf: it is 4,
since the head has NHf + 4 matrices (`k6_NM`) and the view has eight.

What is here.
  `memberText`, `insideText`, `callText`, `callsText`, `callsText_mems`.
  `ownW a`: the owner and the name that the written label of matrix a gives. `callNamesB`.
  `names_example`: the test `callNamesB` accepts at a list of eleven names that is written here;
    `names_rejects`: with two of them exchanged it rejects. The example is made up after the maker's
    text: nothing says that it is the built list.
  `view_24`: the written view has eight matrices at segment 24.
  `calls_written`: the test accepts at the written values, all eight names given. `calls_walks`:
    each of the eight labels names an array of the written layout: so no matrix is passed over.
    `calls_rejects`: negative tests: with one name not given; and at the seats with the first own
    oracle message's tenant moved.
  `gt_of`: the number of a matrix's symbol array stands in the view.
  `callsText_at_head`.
By evaluations in Lean's kernel (`decide +kernel`): `names_example`, `names_rejects`, `view_24`,
`calls_written`, `calls_walks`, `calls_rejects`.

Limits. The premise is not shown.
(Where this and lean/THEOREM.md differ, the page holds.) Nothing on soundness.


-/
import Johnson.HB.LLHARD.K6MaskText
import Johnson.HB.LLHARD.K6NamedText
import Johnson.HB.LLHARD.TailAtView
import Johnson.Desc.Kinds.Law.LaidOffPad
import Johnson.G.LayoutLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open OnBytes OnBytes.Params OnBytes.Model Johnson.G
open VerifiableInference.Desc (Chain arrayOf)
open VerifiableInference.Desc.First.Look (Sent Place keptAt bornAt sigListCalls)
open VerifiableInference.Desc.Kinds.Head.Law.OffPad (lastRowOf lastPlaceOf)
open VerifiableInference.PlanWritten (proofSizedFull tailView xShapeOf)
open VerifiableInference.PlanWritten.Joined (first_written_in_scope xShape_in_scope layout_in_scope)
open Meaning (ownerK ownerA nameOf labAt sizesOf tlAt viewTail viewEntry viewTail_at viewEntry_at
  all_range_same)
open P5T (PSeat psFull seatsAllFull N0Full seats_in_scope arrOf numOfPlan)

/-- The text of `memberOf`. -/
def memberText (D : Sent) (i born msg : ℕ) : Option ℕ :=
  if born == i then some ((keptAt D i).length + msg) else (bornAt D i).idxOf? (born, msg)

/-- The text of `insideB`. -/
def insideText (cs : Codes) (s : OracleShape) (A : ReqArray) : Bool :=
  A.blocks.all fun b =>
    decide (lastRowOf b < s.mainRows) && decide (lastPlaceOf b < (Johnson.Pack.pMain cs s).ell)

/-- The text of `callV`. -/
def callText (arr : ℕ → ℕ → ℕ) (group : List (ℕ × ℕ)) (lay : ReqLayout) (num : ℕ → ℕ → ℕ)
    (D : Sent) (i : ℕ) (seatN : ℕ → ℕ × ℕ) (mems : List (OracleShape × (ℕ × ℕ)))
    (ow : ℕ × String) (nm : Bool) : Bool :=
  match arrayOf lay ow.1 ow.2 with
  | none => true
  | some A =>
    nm && (memberText D i ow.1 A.message).any fun k =>
      sitsText arr group ((sigListCalls D (fun _ => 0) i).map (·.1)) seatN mems k
        (num ow.1 A.message) fun s => insideText D.codes s A

/-- The text of `callsSeatedV`. -/
def callsText (arr : ℕ → ℕ → ℕ) (group : List (ℕ × ℕ)) (lay : ReqLayout) (num : ℕ → ℕ → ℕ)
    (D : Sent) (i : ℕ) (seatN : ℕ → ℕ × ℕ) (mems : List (OracleShape × (ℕ × ℕ))) (NM NHf : ℕ)
    (ows : ℕ → ℕ × String) (nms : ℕ → Bool) : Bool :=
  (List.range NM).all fun a =>
    decide (NHf + 3 < a) || callText arr group lay num D i seatN mems (ows a) (nms a)

/-- The test reads of the members no more than who sits where. -/
theorem callsText_mems (arr : ℕ → ℕ → ℕ) (group : List (ℕ × ℕ)) (lay : ReqLayout)
    (num : ℕ → ℕ → ℕ) (D : Sent) (i : ℕ) (seatN : ℕ → ℕ × ℕ)
    {l l' : List (OracleShape × (ℕ × ℕ))} (hm : ∀ y, y ∈ l ↔ y ∈ l')
    (hu : ∀ y ∈ l', ∀ y' ∈ l', y.2 = y'.2 → y = y') (NM NHf : ℕ) (ows : ℕ → ℕ × String)
    (nms : ℕ → Bool) :
    callsText arr group lay num D i seatN l NM NHf ows nms =
      callsText arr group lay num D i seatN l' NM NHf ows nms := by
  unfold callsText callText sitsText
  simp only [find_any_same hm hu]

/-- The owner and the name that the written label of matrix a gives. -/
def ownW (a : ℕ) : ℕ × String :=
  (ownerK (viewEntry xShapeFull 24 a).1, nameOf (ownerA (viewEntry xShapeFull 24 a).1))

/-- **The test that is left**: eight names in one list of arrays. -/
def callNamesB (arrs : Array (ℕ × String)) : Bool :=
  (List.range 8).all fun a => arrs[(viewTail xShapeFull 24).2.2.getD a 0]? == some (ownW a)

set_option maxRecDepth 1000000 in
/-- It accepts at a list that is made up after the maker's text. -/
theorem names_example :
    callNamesB #[(24, "U3"), (24, "M0"), (24, "M1"), (24, "M2"), (24, "M3"), (24, "M4"),
      (24, "M5"), (24, "M6"), (24, "ZZ"), (24, "BZ"), (22, "M7")] = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The negative test: two names exchanged. -/
theorem names_rejects :
    callNamesB #[(24, "U3"), (24, "M1"), (24, "M0"), (24, "M2"), (24, "M3"), (24, "M4"),
      (24, "M5"), (24, "M6"), (24, "ZZ"), (24, "BZ"), (22, "M7")] = false := by decide +kernel

set_option maxRecDepth 1000000 in
theorem view_24 : (viewTail xShapeFull 24).1 = 8 := by decide +kernel

/-- The test at the written values; a layout and lists of arrays ride in what the caller reads. -/
def callsW (ps : List PSeat) (lay : ReqLayout) (arrs : Array (Array (ℕ × String)))
    (nms : ℕ → Bool) : Bool :=
  callsText (arrOf seatsAllFull) (N0Full.group 24) layoutFull (numOfPlan seatsAllFull)
    (sentW lay arrs) 24 (P6T.seatCallsT ps (sentW lay arrs) 24) memsW 8 4 ownW nms

/-- Of what the caller reads, neither the layout nor the lists of arrays is read here. -/
theorem callsW_blind (ps : List PSeat) (lay : ReqLayout) (arrs : Array (Array (ℕ × String)))
    (nms : ℕ → Bool) : callsW ps lay arrs nms = callsW ps ⟨[]⟩ #[] nms := rfl

set_option maxRecDepth 1000000 in
/-- **The test accepts at the written values, all eight names given.** -/
theorem calls_written : callsW psFull ⟨[]⟩ #[] (fun _ => true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Each of the eight labels names an array of the written layout. -/
theorem calls_walks :
    ((List.range 8).all fun a => (arrayOf layoutFull (ownW a).1 (ownW a).2).isSome) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **Negative tests.** -/
theorem calls_rejects :
    callsW psFull ⟨[]⟩ #[] (fun a => a != 7) = false ∧
      callsW (P6T.bumped psFull 24) ⟨[]⟩ #[] (fun _ => true) = false := by decide +kernel

/-- The number of a matrix's symbol array stands in the view. -/
theorem gt_of (t : HTailF2) (a : ℕ) : (tailView t).2.2.getD a 0 = t.gtTree.getD a 0 := by
  show t.gtTree.toList.getD a 0 = _
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getD_eq_getD_getElem?]

/-- **The condition, at the head's own terms, from the eight names.** -/
theorem callsText_at_head {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hNm : callNamesB (h.𝔇.sent.arrayOf.getD 24 #[]) = true) :
    callsText h.𝔇.arr (h.𝔇.N.group 24) (At.layout Zp) (At.num Zp) h.𝔇.sent x.link
      (h.𝔇.l3.seat x.link false)
      (h.𝔇.ms.map fun y => ((y.1.l.get y.2).1, VerifiableInference.Desc.Sound.seatOf y))
      (sizesOf (At.X Zp) 24).NM (At.X Zp).hS.NHf
      (fun a => (ownerK (labAt (At.X Zp) 24 a), nameOf (ownerA (labAt (At.X Zp) 24 a))))
      (fun a => (h.𝔇.sent.arrayOf.getD x.link #[])[(tlAt (At.X Zp) 24).gtTree.getD a 0]? ==
        some (ownerK (labAt (At.X Zp) 24 a), nameOf (ownerA (labAt (At.X Zp) 24 a)))) = true := by
  have hZ := h.scope
  have L := h.laid
  have hy := (pins_of_laid hZ L).1
  have hl := LPFD.Full.laidPOf_of L.value L.planOk L.data L.asks
  obtain ⟨hps, hAll, hN0⟩ := seats_in_scope hZ L.pub hy hl
  have hF := H2K.Sizes.publicO_at_scope hZ L.publicO
  have h4 : (At.X Zp).p4 = true := hF.p4
  have hG : (At.X Zp).NGr = 12 := hF.groups
  have hx : x.link = 24 := by
    rw [headAt_link h.headAt, h4, hG]
    rfl
  have FW := first_written_in_scope hZ L.pub hy
  have hV : xShapeOf (At.X Zp) = xShapeFull := xShape_in_scope hZ L.pub hy
  have hLy : At.layout Zp = layoutFull := layout_in_scope hZ L.pub hy
  have hT : viewTail xShapeFull 24 = tailView (tlAt (At.X Zp) 24) := by
    rw [← hV]
    exact viewTail_at h4 hG (by omega)
  have hNM : (sizesOf (At.X Zp) 24).NM = 8 := by
    rw [← view_24, hT]
    rfl
  have hH : (At.X Zp).hS.NHf = 4 := by
    have e := VerifiableInference.Desc.Kinds.Head.Law.k6_NM h.pubOne
    rw [← nm_24, hNM] at e
    omega
  have hlab : ∀ a, (ownerK (labAt (At.X Zp) 24 a), nameOf (ownerA (labAt (At.X Zp) 24 a))) =
      ownW a := by
    intro a
    unfold ownW
    rw [← hV, viewEntry_at h4 hG (by omega) a]
  have hs : (At.N Zp cF).sent = N0Full.sent := by
    rw [← hN0]
    rfl
  have hm : ∀ y, y ∈ (P5T.msAtR Zp (At.rad Zp Z.lay)).map
      (fun y => ((y.1.l.get y.2).1, VerifiableInference.Desc.Sound.seatOf y)) ↔ y ∈ memsW := by
    intro y
    rw [P5T.memsSame_atR, hps]
    rfl
  have hD : At.sentAt Zp = sentW (At.layout Zp) (Zp.made.p.built.links.map (·.arrayOf)) := by
    unfold At.sentAt sentW
    rw [show At.cs Zp = proofSizedFull.codes from FW.1,
      show At.shape Zp = proofSizedFull.request from FW.2.2.1]
  have hnm : ∀ a, a < 8 →
      ((h.𝔇.sent.arrayOf.getD 24 #[])[(tlAt (At.X Zp) 24).gtTree.getD a 0]? ==
        some (ownW a)) = true := by
    intro a ha
    have c := List.all_eq_true.1 hNm a (List.mem_range.2 ha)
    rw [hT, gt_of] at c
    exact c
  rw [hx, hNM, hH]
  simp only [hlab]
  have step : ∀ (arr : ℕ → ℕ → ℕ) (g : List (ℕ × ℕ)) (ly : ReqLayout) (num : ℕ → ℕ → ℕ)
      (S : Sent) (sn : ℕ → ℕ × ℕ) (ms : List (OracleShape × (ℕ × ℕ))) (nms : ℕ → Bool),
      (∀ a, a < 8 → nms a = true) →
      callsText arr g ly num S 24 sn ms 8 4 ownW nms =
        callsText arr g ly num S 24 sn ms 8 4 ownW fun _ => true := by
    intro arr g ly num S sn ms nms hn
    unfold callsText
    exact all_range_same fun a ha => by rw [hn a ha]
  rw [step _ _ _ _ _ _ _ _ hnm]
  show callsText (arrOf (P5T.planSeatsAll Zp Zp.D)) ((At.N Zp cF).group 24) (At.layout Zp)
    (numOfPlan (P5T.planSeatsAll Zp Zp.D)) (At.sentAt Zp) 24
    (P6T.seatCallsT (P5T.planSeats Zp Zp.D.1) (At.sentAt Zp) 24)
    ((P5T.msAtR Zp (At.rad Zp Z.lay)).map
      fun y => ((y.1.l.get y.2).1, VerifiableInference.Desc.Sound.seatOf y))
    8 4 ownW (fun _ => true) = true
  rw [callsText_mems _ _ _ _ _ _ _ hm (List.inj_on_of_nodup_map seats_one), hAll, hps, hD,
    group_same hs 24, hLy]
  exact (callsW_blind _ _ _ _).trans calls_written

end P5J

#print axioms P5J.callsText_mems
#print axioms P5J.names_example
#print axioms P5J.names_rejects
#print axioms P5J.view_24
#print axioms P5J.callsW_blind
#print axioms P5J.calls_written
#print axioms P5J.calls_walks
#print axioms P5J.calls_rejects
#print axioms P5J.gt_of
#print axioms P5J.callsText_at_head
