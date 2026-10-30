-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/SeatNumberK4.lean: CONDITIONAL: on h, Lh and hx. On
public data alone.

What is here. AT THE SEAT OF A SYMBOL OF THE LIST OF MATRICES OF THE FEED-FORWARD LAYERS' OWN ROUNDS
(sub-protocol K4): WHICH ARRAY OF THE LAYOUT, WHICH PLACE BY THE LAYOUT's RULE, AND WHICH NUMBER IN
THE WITNESS. It is the like, at a layers' link 2 g, of another house's `seat_number_head`
(Honest/K5/Law/SeatNumber.lean), which stands at an attention link 2 g + 1 over a closed test at the
odd links. Here nothing new is decided by evaluation: the library's own road for K4 has what is
needed at the even links, and proofs of ours draw it under h already: `SymsOne`
(Johnson/Road/K4/K4PinsSym.lean), a field of `fitF_wide`: each symbol's seat, its row and place, and
the tenant with its number; the names' tie (`namesTied_of_scope`, Johnson/Road/K4/K4PlanNames.lean):
the array at the tree of matrix μ is the one that the label names; `XNine`
(Johnson/Road/K4/K4PlanNine.lean, by `xNine_of_laid`): nine matrices, and the label's owner is
`ownerW g μ`: the group's own link and μ, but the stream that comes in at a later group: the group
before, entry 7. A helper and two statements with their proofs. The first proof has the first lines
of `matsAre_head` (Law/W/MatsAreHead.lean); the second goes as `seat_number_head` does where it
reads `seatCalls`' own text, and as the library's `symsOne_of_layout`
(Johnson/Road/K4/SymsOfLayout.lean) where it unfolds the model's owner's seats.

  `seatBy_at`   a helper: the model's owner's seat of a symbol, where the array that the label names
      is there and the rule lays the symbol. It has the lines of a step of `symsOne_of_layout`.
  `symsOne_head`   under h: the plan's sizes are the segment's; `SymsOne`; the place's link is 2 g;
      what the lookups read as sent is the plan's.
  `k4_seat_number`   **the array, the place and the number at a symbol's seat.**

Not shown here. Of what a message holds nothing is said. All nine entries of the list, the planes'
too. h: the library's hypothesis `P5J.AtMgA` on the public files; Lh (`LaidK4`, Law/SeatedHead.lean)
and hx follow from it at each of the twelve groups, as Law/W/MatsAreHead.lean's head says. Beneath
it stand closed facts that Lean's kernel decided by evaluation at the library's written values
(beneath `first_paid`, `xNine_of_laid` and what Law/W/MatsAreHead.lean's head names); no independent
checker that its writers know of has replayed them. THE STATEMENTS REST ON DEFINITIONS AND LAWS OF
FILES UNDER Johnson/Goal/, CALLED BY NAME: `Meaning.seatBy`, `Meaning.fLay`, `Meaning.labAt`,
`Meaning.ownerK`, `Meaning.ownerA`, `Meaning.nameOf`, `Meaning.sizesOf`, `Meaning.tlAt`,
`Meaning.laidPlace_eq_laidAt`, and those that Law/W/MatsAreHead.lean's head names. THE FULL SIZE
ALONE, and the format's second hash function alone (`OnBytes.secondHashFunction`). A LAW, NOT A PART: no file that
defines a part of the proof file's description may import this one. Nothing on soundness, on
completeness or on any other property.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MatsAreHead
import Johnson.Desc.ProofFile.Honest.K5.Law.CellsQRaw
import Johnson.Desc.ProofFile.Honest.K5.Law.PackedVals
import Johnson.Road.K4.SymsOfLayout
import Johnson.Road.K4.K4PlanClosed
import Johnson.Road.K4.K4PlanIsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.HonestTrace (arrayLabel)
open OnBytes.Road.K4 (eAll parOf written_of_head fitF_wide pinsFill_const group_at layAt_plan cutW
  posFree refPub_in_scope xNine_of_laid namesTied_of_scope XNine ownerW SymsOne planAt tlAt_even)
open OnBytes.Maker (WholeD)
open OnBytes.Params (ReqLayout ReqArray)
open Cb.Pv.Tail (Size)
open Inst.Model.Layout (kRef hRef)
open VerifiableInference.PlanWritten (publicSteps_of)
open VerifiableInference.Desc (Chain Block arrayOf laidAt seatIn)
open VerifiableInference.Desc.First.Look (layAt Stored.entries Seat sigListCalls seatCalls szOf)
open VerifiableInference.Desc.Sound (mgBase)
open ProofFile.Honest.K5 (msgNo5)
open P5J (AtMgA TS)
open ProofFile.Honest.K4.SeatedHead (LaidK4 k4Here_head)

/-- The model's owner's seat of symbol (r, c) of matrix μ of sub-proof k, where the array that the
label names is there and the layout's rule lays the symbol at rp. -/
theorem seatBy_at {X : Verify.Public} {s : ℕ → Size} {layout : ReqLayout} {num : ℕ → ℕ → ℕ}
    {k : ℕ} (μ : Fin (s k).NM) {r c : ℕ} {a : ReqArray} {rp : ℕ × ℕ}
    (ha : arrayOf layout (_root_.Meaning.ownerK (_root_.Meaning.labAt X k μ.val))
      (_root_.Meaning.nameOf (_root_.Meaning.ownerA (_root_.Meaning.labAt X k μ.val))) = some a)
    (hx : laidAt a r c = some rp) :
    _root_.Meaning.seatBy (_root_.Meaning.fLay layout num) X s k μ r c =
      (num (_root_.Meaning.ownerK (_root_.Meaning.labAt X k μ.val)) a.message, rp.1, rp.2) := by
  unfold _root_.Meaning.seatBy _root_.Meaning.fLay seatIn
  rw [ha]
  simp [hx]

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL: on h, Lh and hx. **Four facts on public letters at the lookup's place of the
segment.** xl: that place. -/
theorem symsOne_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ} {x : Bool × Par}
    {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    {xl : VerifiableInference.Desc.First.Look.Place} (hx : layAt (P5J.At.X Zp) m = some xl) :
    szOf x.2.hp.tl = _root_.Meaning.sizesOf Zp.p.X (2 * g) ∧
      SymsOne (planAt xl h.𝔇.sent h.𝔇.l3.rad (fun j => h.𝔇.l3.seat xl.link false j.1)
          (cutW Stored.entries h.𝔇.l3.wOf hRef (2 ^ kRef)) (posFree 0)) x.2.hp.tl h.𝔇.l3.arr
        h.𝔇.N (2 * g) (_root_.Meaning.sizesOf Zp.p.X (2 * g))
        (_root_.Meaning.seatBy
          (_root_.Meaning.fLay (OnBytes.Road.K4.sentAt Zp).layout (OnBytes.Road.K4.numAt Zp))
          Zp.p.X (_root_.Meaning.sizesOf Zp.p.X) (2 * g)) ∧
      xl.link = 2 * g ∧ h.𝔇.sent = OnBytes.Road.K4.sentAt Zp := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨G₀, hG, -, Hh⟩ := k4Here_head h Lh
  obtain rfl : Bs.G₀ = G₀ := Option.some.inj (O.blank.symm.trans hG)
  have hpub : Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X := O.W ▸ O.public
  have N := nine_head h Lh
  obtain ⟨x₁, hx₁, el, e1, e2, e3, _⟩ := layAt_plan N.Sx.pubOf N.Sx.notHead N.Sx.step N.Sx.plan
  have ex : x₁ = xl := Option.some.inj (hx₁.symm.trans hx)
  rw [ex] at el e1 e2 e3
  obtain ⟨k4, _, _⟩ := _root_.Meaning.scope_plans h.scope h.reads hpub
  have Pf := pinsFill_const OnBytes.secondHashFunction Zp Np cF (P5J.At.EAt Z) h.plan.shape Z.lay h.plan.laid
    h.plan.hN h.plan.hG xh OnBytes.Flat.numsFull.rows
  obtain ⟨radM, Q3⟩ := Pf.ms
  have eg : (parOf x).g = g := Lh.grp
  have Pt := pinsTests_head h Lh
  have F := fitF_wide Zp radM h.𝔇 (eAll Zp cF VerifiableInference.Desc.K13.Law.LFull) mgBase
    (parOf x)
    Pf.sent Pf.arr Q3 Pf.nSent Pf.nIndex Pf.seat3 (by rw [eg]; exact Pt.first)
    (by rw [eg]; exact Lh.lt) xl (by rw [el, eg]; exact Lh.seg) (O.W ▸ Hh.G) (posFree 0)
    (publicSteps_of hpub) (refPub_in_scope h.scope h.reads hpub (by rw [eg]; exact Lh.lt))
    (O.W ▸ Hh.P) ⟨e1.trans N.Sx.shape, by rw [N.Sx.y]; exact e2, e3⟩ (group_at k4 _)
    (by rw [eg, ← Lh.seg]; exact N.Sx.notHead)
  have hσ := F.size
  have h1 := F.syms
  rw [eg] at hσ h1
  exact ⟨hσ, h1, el.trans Lh.seg, Pf.sent⟩

/-- CONDITIONAL: on h, Lh and hx; i is below the plan's number of matrices; i' and c lie inside the
matrix's packed rows and its columns; the symbol's address has the seat s, whose member is in the
list. **THE ARRAY, THE PLACE AND THE NUMBER AT A SYMBOL's SEAT.** -/
theorem k4_seat_number (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ} {x : Bool × Par}
    {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    {xl : VerifiableInference.Desc.First.Look.Place} (hx : layAt (P5J.At.X Zp) m = some xl)
    {i i' c : ℕ} (hiN : i < x.2.hp.tl.NM)
    (hi' : i' < Alg.symRows (x.2.hp.tl.mats.getD i {}).m) (hc : c < (x.2.hp.tl.mats.getD i {}).k)
    {s : Seat} (hk : s.msg < (sigListCalls h.𝔇.sent h.𝔇.l3.rad xl.link).length)
    (hs : seatCalls h.𝔇.sent xl.link (.cell (x.2.hp.tl.gtTree.getD i 0) i' c) = some s) :
    i < 9 ∧ ∃ A : ReqArray,
      arrayOf h.𝔇.sent.layout (ownerW g i).1 (arrayLabel (ownerW g i).2) = some A ∧
      laidAt A i' c = some (s.row, s.place) ∧
      msgNo5 h xl s.msg hk = P5J.At.num Zp (ownerW g i).1 A.message := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hpub : Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X := O.W ▸ O.public
  have W := written_of_head h.toAtMg
  have H9 : XNine Zp.p.X :=
    xNine_of_laid hpub (OnBytes.Road.Hd.core_of_scope h.scope h.reads hpub) W.layout h.plan.laid
  obtain ⟨hσ, h1, el, eS⟩ := symsOne_head h Lh hx
  have hi1 : i < (_root_.Meaning.sizesOf Zp.p.X (2 * g)).NM := by
    rw [← hσ]
    exact hiN
  have hi9 : i < 9 := by
    rw [← H9.nm g Lh.lt]
    exact hi1
  have hr1 : i' < Alg.symRows ((_root_.Meaning.sizesOf Zp.p.X (2 * g)).m i) := by
    rw [← hσ]
    exact hi'
  have hc1 : c < (_root_.Meaning.sizesOf Zp.p.X (2 * g)).k i := by
    rw [← hσ]
    exact hc
  obtain ⟨s', hk', q0, -, -, -, -, q5⟩ := h1 ⟨i, hi1⟩ ⟨i', hr1⟩ ⟨c, hc1⟩
  obtain rfl : s' = s := Option.some.inj (q0.symm.trans hs)
  -- the array, out of the text of `seatCalls`
  obtain ⟨bn, hbn, q1⟩ := Option.bind_eq_some_iff.1 hs
  obtain ⟨A, hA, q2⟩ := Option.bind_eq_some_iff.1 q1
  obtain ⟨rp, hrp, q3⟩ := Option.bind_eq_some_iff.1 q2
  have et : _root_.Meaning.tlAt Zp.p.X (2 * g) = x.2.hp.tl := tlAt_even Lh.lt Lh.hp
  have hnm := namesTied_of_scope h.scope h.reads O g Lh.lt i hi1
  rw [et] at hnm
  rw [eS, el] at hbn
  obtain rfl := Option.some.inj (hbn.symm.trans hnm)
  have hAl : arrayOf (OnBytes.Road.K4.sentAt Zp).layout
      (_root_.Meaning.ownerK (_root_.Meaning.labAt Zp.p.X (2 * g) i))
      (_root_.Meaning.nameOf (_root_.Meaning.ownerA (_root_.Meaning.labAt Zp.p.X (2 * g) i))) =
      some A := by
    rw [← eS]
    exact hA
  have hrp' : laidAt A i' c = some rp := by
    rw [← _root_.Meaning.laidPlace_eq_laidAt]
    exact hrp
  have hrow : rp = (s'.row, s'.place) := by
    split at q3
    · obtain rfl := Option.some.inj q3
      rfl
    · obtain ⟨j, -, rfl⟩ := Option.map_eq_some_iff.1 q3
      rfl
  have o := H9.own g Lh.lt i hi9
  have o1 : _root_.Meaning.ownerK (_root_.Meaning.labAt Zp.p.X (2 * g) i) = (ownerW g i).1 :=
    congrArg Prod.fst o
  have o2 : _root_.Meaning.ownerA (_root_.Meaning.labAt Zp.p.X (2 * g) i) = (ownerW g i).2 :=
    congrArg Prod.snd o
  have e5 := seatBy_at (num := OnBytes.Road.K4.numAt Zp)
    (⟨i, hi1⟩ : Fin (_root_.Meaning.sizesOf Zp.p.X (2 * g)).NM) hAl hrp'
  have e6' := List.find?_some q5
  have e6 := eq_of_beq e6'
  have e4 : h.𝔇.l3.arr (h.𝔇.l3.seat xl.link false s'.msg).1
        (h.𝔇.l3.seat xl.link false s'.msg).2 =
      OnBytes.Road.K4.numAt Zp (_root_.Meaning.ownerK (_root_.Meaning.labAt Zp.p.X (2 * g) i))
        A.message :=
    e6.trans (congrArg Prod.fst e5)
  rw [o1] at e4
  rw [o1, o2, ← eS] at hAl
  exact ⟨hi9, A, hAl, by rw [hrp', hrow], e4⟩

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.seatBy_at
#print axioms ProofFile.Honest.K4.W.symsOne_head
#print axioms ProofFile.Honest.K4.W.k4_seat_number
