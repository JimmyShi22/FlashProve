-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Cells/SeatsInside.lean: THE OUTPUT HEAD's OWN SUB-PROTOCOL (K6):
WHERE THE SEATS OF THE HEAD's SIX OWN MATRICES OFF THE PLANE LIE: in message 0 of link 24, where the
layout's rule lays the element, below the main rows and the main code's length of message 2 of the
code switch's sending, IN THE SWITCH's PLACE's OWN LETTERS. Under the hypothesis h (`P5J.AtMgA`,
Johnson/P5J/MgAtAll.lean). On public data alone. No definition; five theorems.

  `arrays24W`         a closed fact: in the written layout the arrays "M0" to "M5" of link 24 are
                      there and lie in message 0
  `arrays24W_other`   a control: the test on the message can say no
  `message24W`        a closed fact: the written request has message 0 of link 24, in two spellings
  `k6_owner_own`      under h: the label of the head's matrix number a < 6 names segment 24 and a
  `k6_seats_inside`   the sentence above

THE LIBRARY HAS ALMOST ALL OF IT, AT THE PLAN's OWN LETTERS; IT IS CALLED: `seat_of_laidThere`,
`owner_label` (Johnson/Goal/Meaning/HidSeatsOf.lean); `laidAt_inside`
(Johnson/Goal/Meaning/LaidInside.lean); `three_at_pure` (Johnson/P5J/InsideAtPure.lean); the plan's
test `laidThere` is a field of h's. New here: the message's number (a closed fact) and the turn from
the plan's letters to the switch's place's (`atLink24Main`, Honest/K6/Cells/Link24Main.lean).

What it is not.
  * WHERE a seat lies, not what stands there.
  * The plane (number 6) and the borrowed stream (number 7) are out.
  * The pads of the message's sample are not spoken of.
  * The three closed facts: written values, by evaluation in Lean's kernel; replayed by no
    independent checker.
  * h: the full size and the format's second hash function alone.
  * Modules under lean/Johnson/Goal/ lie in its import closure.
  * Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K6.Cells.Link24Main
import Johnson.Desc.ProofFile.Honest.K6.Cells.SizesAtHead
import Johnson.Desc.Kinds.Law.PlanK6At
import Johnson.Desc.First.Att.Door.Law.K5CondOfHead
import Johnson.Goal.Meaning.LaidInside
import Johnson.Goal.Meaning.HidSeatsOf
import Johnson.Goal.Meaning.HidPlanNM
import Johnson.P5J.InsideAtPure
import Johnson.G.LayoutLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- The library's default table of scales is no instance in this file: no statement here can take it
in silence. An instance is taken away, none is added. -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open VerifiableInference.Desc (Chain arrayOf)
open VerifiableInference.PlanWritten (proofSizedFull)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS At.layout At.num At.X)
open ProofFile.Honest (K2.SwitchPlace K2.switchSent)
open ProofFile.Honest.K6 (atLink24MainW atLink24Main_gives)

set_option maxRecDepth 1000000 in
/-- A CLOSED FACT: in the written layout the arrays "M0" to "M5" of link 24 are there and lie in
message 0. By evaluation in Lean's kernel. -/
theorem arrays24W : ((List.range 6).all fun a =>
    ((arrayOf Johnson.G.layoutFull 24 (Meaning.nameOf a)).map (·.message)) == some 0) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control, in three limbs: THE TEST ON THE MESSAGE CAN SAY NO: the array "U3" of link 24 is
there and does not lie in message 0; and no array "M7" stands in link 24's list. -/
theorem arrays24W_other :
    (((arrayOf Johnson.G.layoutFull 24 "U3").map (·.message)) == some 0) = false ∧
      (arrayOf Johnson.G.layoutFull 24 "U3").isSome = true ∧
      (arrayOf Johnson.G.layoutFull 24 (Meaning.nameOf 7)).isSome = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A CLOSED FACT: the written request has message 0 of link 24: the library's reader of a request's
shape and the two readers with a default give one message. By evaluation in Lean's kernel. -/
theorem message24W : Meaning.messageAt proofSizedFull.request 24 0 =
    some ((proofSizedFull.request.link.getD 24 default).messages.getD 0 default) := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : First.Look.Place}

/-- CONDITIONAL: the hypothesis h. The label of the head's matrix number a < 6 names segment 24 and
the number a. -/
theorem k6_owner_own (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {a : ℕ} (ha : a < 6) :
    Meaning.ownerK (Meaning.labAt (At.X Zp) 24 a) = 24 ∧
      Meaning.ownerA (Meaning.labAt (At.X Zp) 24 a) = a := by
  have hP := h.pubOne
  have C := OnBytes.Road.Hd.core_of_scope h.scope h.reads hP
  obtain ⟨hNM, hN4, -, -, -⟩ := k6_sizes_own h
  have F := Meaning.follows_of_core hP C
  have e := Meaning.owner_label hP C (k := 24) (a := a) (by norm_num)
    (by rw [← F.NM 24 (by norm_num), hNM]; omega)
  unfold Meaning.ownerOf at e
  rw [if_pos rfl, if_neg (by rw [hN4]; omega)] at e
  exact ⟨(Prod.mk.inj e).1, (Prod.mk.inj e).2⟩

/-- CONDITIONAL: h; hp; hlk. ON PUBLIC DATA ALONE. **EVERY SEAT OF THE HEAD's SIX OWN MATRICES OFF
THE PLANE**: the array, its message, its two sizes, where the layout's rule lays the element, the
message's number in the witness, and the two fences in the switch's place's own letters. -/
theorem k6_seats_inside (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {p : K2.SwitchPlace}
    (hp : p ∈ ProofFile.Honest.K2.Law.placesW) (hlk : p.link = 24) {a : ℕ} (ha : a < 6)
    (ha' : a < (Meaning.sizesOf (At.X Zp) 24).NM) {i c : ℕ}
    (hi : i < Alg.symRows ((Meaning.sizesOf (At.X Zp) 24).m a))
    (hc : c < (Meaning.sizesOf (At.X Zp) 24).k a) :
    ∃ A, arrayOf (At.layout Zp) 24 (Meaning.nameOf a) = some A ∧ A.message = 0 ∧
      A.sizeI = Alg.symRows ((Meaning.sizesOf (At.X Zp) 24).m a) ∧
      A.sizeC = (Meaning.sizesOf (At.X Zp) 24).k a ∧
      VerifiableInference.Desc.laidAt A i c =
        some ((seatLay (At.X Zp) (At.layout Zp) (At.num Zp) 24 ⟨a, ha'⟩ i c).2.1,
          (seatLay (At.X Zp) (At.layout Zp) (At.num Zp) 24 ⟨a, ha'⟩ i c).2.2) ∧
      (seatLay (At.X Zp) (At.layout Zp) (At.num Zp) 24 ⟨a, ha'⟩ i c).1 = At.num Zp 24 0 ∧
      (seatLay (At.X Zp) (At.layout Zp) (At.num Zp) 24 ⟨a, ha'⟩ i c).2.1 <
        ((K2.switchSent p.sizes p.others).getD 2 default).shape.mainRows ∧
      (seatLay (At.X Zp) (At.layout Zp) (At.num Zp) 24 ⟨a, ha'⟩ i c).2.2 <
        (p.sizes.codes.base.getD ((K2.switchSent p.sizes p.others).getD 2 default).shape.code
          default).ell := by
  obtain ⟨o1, o2⟩ := k6_owner_own h ha
  obtain ⟨A, y, hA, z1, z2, hat, hseat⟩ :=
    Meaning.seat_of_laidThere h.plan.laid (At.num Zp) (k := 24) (by norm_num) ⟨a, ha'⟩ hi hc
  -- the same two sentences, with the number of the written pair read off
  have hA' : arrayOf (At.layout Zp) (Meaning.ownerK (Meaning.labAt (At.X Zp) 24 a))
      (Meaning.nameOf (Meaning.ownerA (Meaning.labAt (At.X Zp) 24 a))) = some A := hA
  have hseat' : (seatLay (At.X Zp) (At.layout Zp) (At.num Zp) 24 ⟨a, ha'⟩ i c) =
      (At.num Zp (Meaning.ownerK (Meaning.labAt (At.X Zp) 24 a)) A.message, y.1, y.2) := hseat
  rw [o1, o2] at hA'
  rw [o1] at hseat'
  obtain ⟨f1, -, f3, -, -, f6⟩ :=
    (H2K5.Door.made_row_gives (H2K5.Door.pins_at_head h.toAtMg).1).1
  have el : At.layout Zp = Johnson.G.layoutFull := f6
  have hm0 : A.message = 0 := by
    have H := arrays24W
    rw [List.all_eq_true] at H
    have h1 : (((arrayOf Johnson.G.layoutFull 24 (Meaning.nameOf a)).map (·.message)) == some 0) =
        true := H a (List.mem_range.2 ha)
    rw [← el, hA'] at h1
    simpa using h1
  obtain ⟨Z', hZ', c1, c2, c3⟩ := P5J.three_at_pure h.laid.value
  have eZ : Z' = Zp := Except.ok.inj (hZ'.symm.trans h.laid.pub)
  rw [eZ] at c1 c2 c3
  obtain ⟨as, hl, hf⟩ := Option.bind_eq_some_iff.1 hA'
  obtain ⟨m, hm, r1, r2, -⟩ := Meaning.laidAt_inside c1 c2 c3 hl (List.mem_of_find?_eq_some hf)
    (i := i) (c := c) (r := y.1) (p := y.2) hat
  rw [hm0, f3] at hm
  obtain rfl : (proofSizedFull.request.link.getD 24 default).messages.getD 0 default = m :=
    Option.some.inj (message24W.symm.trans hm)
  rw [f1] at r2
  obtain ⟨-, g2, g3, -, -⟩ := atLink24Main_gives (List.all_eq_true.1 atLink24MainW p hp) hlk
  refine ⟨A, hA', hm0, z1, z2, ?_, ?_, ?_, ?_⟩
  · rw [hseat']
    exact hat
  · rw [hseat', hm0]
  · rw [hseat', g2]
    exact r1
  · rw [hseat', g3]
    exact r2

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.arrays24W
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.arrays24W_other
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.message24W
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_owner_own
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_seats_inside
