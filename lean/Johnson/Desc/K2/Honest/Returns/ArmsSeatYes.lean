-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/ArmsSeatYes.lean: THE CODE SWITCH AT ITS TWO ARMS (339, the output
head's switch; 353, behind the last segment): UNDER THE HEAD `P5J.AtMgA` AND THE OPENING IN ITS
LETTERS, AT EVERY STATE REACHED THERE: THE SUB-PROTOCOL THAT THE PROOF FILE's DESCRIPTION SEATS SAYS
YES AT EVERY TWO ROUNDS THAT FIT THE PLAN's ENTRIES AND AT COLUMNS LAID AS THE ENTRIES ASK: THREE
TESTS ON SHAPES AND NO MORE: the like, at the arms, of `link_seat_yes` (Returns/SeatYes.lean) at the
23 links. So all 25 members of the kind stand alike. Joins. Statements with their proofs: calls.

  `head_seat_shape`, `fin_seat_shape` the seated sub-protocol's place, rounds and stated oracle
                    messages, at 339 and at 353
  `head_seat_laid` the head · the opening ⊢ there are b, nm, Pp, n: b is entry 339, at the place
                    `headPlaceAt`, with the kind's own rounds and stated messages at the plan's
                    numbers · for every s reached at 339, all r₁ r₂ ft d₁ d₂ cols: d₂'s positions
                    are r₂'s · the two rounds fit · the columns' keys, positions and widths are
                    those that the entries ask ⊢ ∃ t, b.decide s [r₁, r₂] (laidGroups …) = ok t
  `fin_seat_laid` the same at 353, at the place `k2PlaceF`

By, this folder's: `head_seat_reached` (Returns/HeadAfter.lean), `head_behind_returns`
(Returns/HeadBehindPaid.lean), `headGroup_reached`, `own_at_head` (Returns/HeadSeatYes.lean) ·
`fin_seat_reached` (Returns/FinAfter.lean) · `head_dress` (Returns/SeatAtArms.lean) ·
`head_tied_whole` (Returns/TiedWhole.lean), `code_look_reached` (Returns/ArmsPaid.lean) ·
`head_behind_seven`, `HeadSeven` (Returns/ArmsProver.lean), `HeadBehind.plain`
(Returns/ArmsBehind.lean), `head_returns_sent` (Returns/ArmsSent.lean), `head_oldCode_reached`
(Returns/ArmsPlan.lean) · `call_seven`, `laidGroups` (Returns/RoundsJoin.lean), `groups_give`
(Returns/ItemsFit.lean), `fin_yes_reached` (Returns/YesReached.lean) · `six_at_head`
(Returns/TiedReached.lean), `tests_at_head` (Returns/UnderHead.lean), `h25_of_hy`
(Returns/FinAtReached.lean). NOT OURS: `head_looks_reached`, `fin_looks_reached`
(Johnson/AtFull/Shape/HeadLooksReached.lean, FinFrontReached.lean: on no line) · `head_nums_reached`
(Johnson/AtFull/Shape/ArmsLeftNums.lean: lined). The library's: `k2_head_of`, `k2_finish_of`
(Johnson/IMR/K2Seat.lean), `hear_at_flat` (Johnson/IMR/FlatIx.lean), `flatIx_scope`
(Johnson/IMR/FlatScope.lean), `back_at_flat`, `links_flat_352` (Johnson/IMR/BackSeat.lean),
`alone_rounds`, `laid_planOk`, `retype_planOk` (Johnson/IMR/SeatForm.lean), `flat_planOk`,
`back_planOk` (Johnson/P1K2R/SitsDoor.lean), `place_of_is` (Johnson/Top/H0/K2Caller/SitsAtP.lean) ·
`finishFrontQ_st`, `finishFrontQ_rest` (Johnson/Top/H0/Tw/K2C/FinFront.lean). NEAR RELATIVES:
`link_seat_shape`, `link_seat_yes` (Returns/SeatYes.lean): THE PATTERN · `head_yes_tied`
(Returns/YesTied.lean): SIX LINES OF `head_seat_laid`'s PROOF ARE ITS OWN, ending in
`head_behind_seven` where it ends in `head_returns_seven`: because the way out at 339 wants the
law's premises, not the yes alone · `head_seat_yes`, `fin_seat_yes` (Returns/HeadSeatYes.lean,
FinSeatYes.lean): the same ends from premises that are not yet brought down to shapes: not called ·
the preludes of the two laws on shape are `head_seat_decides`' and `fin_seat_decides`' own
(Returns/SeatAtArms.lean).

Limits. THE YES IS NO SIGN THAT A MESSAGE IS HONEST: it holds at every two rounds and columns of the
right shape. THE HEAD IS SHOWN MET BY NOBODY HERE; that a state is reached is not said. At the
decision, not at the step. "Reached" is: over the list of the wrapped sub-protocols. The full size
alone; the format's second hash function alone. IT STANDS ON FILES THAT ARE IN NO SEALED LIBRARY, SOME ON NO
LINE FOR ONE: eight that are not ours on `leafOk` and on what the arms look up (on no line), and
lined files that are not ours on the plan's numbers; closed tests by Lean's kernel among what lies
beneath. This file's imports are heavy. Nothing on any property.
-/
import Johnson.Desc.K2.Honest.Returns.HeadSeatYes
import Johnson.Desc.K2.Honest.Returns.FinAfter
import Johnson.Desc.K2.Honest.Returns.ArmsPaid
import Johnson.Desc.K2.Honest.Returns.YesReached
import Johnson.Top.H0.K2Caller.SitsAtP

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (roundsFit groupsOf Block Chain FileDescription Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (rounds flat headFrontOf freshGroup finishFrontQ_st
  finishFrontQ_rest)
open VerifiableInference.Desc.Sound (below)
open VerifiableInference.PlanWritten (cutOf cutFirstFull)
open Johnson.Desc.First.Walk.Tied (Reach)
open Johnson.AtFull.Shape (head_looks_reached fin_looks_reached head_nums_reached)
open P1K2 (Prep Nums numsAt prepOf)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open IM (k2P under k2PlaceF)
open _root_.Tw.K2 (Col)
open ProofFile (Cl)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The seated sub-protocol's place, rounds and stated oracle messages, at 339.** -/
theorem head_seat_shape (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B) (hpl : F.planOk = true)
    (hcut : cutOf c.blocksInOrder = cutFirstFull) :
    ∃ b : Block S Cl, c.blocksInOrder[339]? = some b ∧ b.place = headPlaceAt ∧
      ∀ (nm : String) (Pp : Prep) (n : Nums), prepOf Z Bs.G₀ = some Pp →
        numsAt Pp (some 24) = some n →
        b.rounds = rounds (k2P Z headPlaceAt nm .head n) ∧
          b.oracles = [(k2P Z headPlaceAt nm .head n).sent, []] := by
  obtain ⟨Lk, b, x, e1, e2, hx, hl, hi⟩ := IM.k2_head_of hS hR O
  have hf := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by omega) 1] at hf
  have hb := P1K2.flat_planOk O hpl b (List.mem_of_getElem? hf)
  have hxp := (IM.retype_planOk x (IM.laid_planOk hl.laid hb)).1
  have hpc : x.place = headPlaceAt := P1K2.place_of_is hi hxp
  obtain ⟨Pp₀, n₀, HP, hP₀, hn₀, -, ex⟩ := head_dress hS hR O hpl hcut hx hxp hpc
  refine ⟨b, hf, congrArg Block.place (show b = _ from hl), fun nm Pp n hP hn => ?_⟩
  obtain rfl : Pp₀ = Pp := Option.some.inj (hP₀.symm.trans hP)
  obtain rfl : n₀ = n := Option.some.inj (hn₀.symm.trans hn)
  constructor
  · rw [IM.alone_rounds hl, ex]
    rfl
  · refine (congrArg Block.oracles (show b = _ from hl)).trans ?_
    show (x.retype : Block S Cl).oracles = _
    rw [ex]
    rfl

/-- **The same at 353.** -/
theorem fin_seat_shape (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B) (hpl : F.planOk = true) :
    ∃ b : Block S Cl, c.blocksInOrder[353]? = some b ∧ b.place = k2PlaceF ∧
      ∀ (nm : String) (Pp : Prep) (n : Nums), prepOf Z Bs.G₀ = some Pp →
        numsAt Pp none = some n →
        b.rounds = rounds (k2P Z k2PlaceF nm .finish n) ∧
          b.oracles = [(k2P Z k2PlaceF nm .finish n).sent, []] := by
  obtain ⟨b, x, e1, hx, -, hl, hi⟩ := IM.k2_finish_of O
  have hb := P1K2.back_planOk O hpl (List.mem_of_getElem? e1)
  have hxp := (IM.retype_planOk x (IM.laid_planOk hl.laid hb)).1
  obtain ⟨Pp₀, n₀, hP₀, hn₀, ex⟩ : ∃ Pp n, prepOf Z Bs.G₀ = some Pp ∧ numsAt Pp none = some n ∧
      x = under x.name k2PlaceF (VerifiableInference.Desc.First.K2.finishPlace
        (k2P Z k2PlaceF x.name .finish n)) := by
    rcases hi with ⟨h0, -⟩ | h
    · rw [h0] at hxp
      cases hxp
    · exact h
  have hf := IM.back_at_flat e1
  rw [(IM.links_flat_352 hS hR O).1, (IM.links_flat_352 hS hR O).2] at hf
  refine ⟨_, hf, ?_, fun nm Pp n hP hn => ?_⟩
  · show b.place = _
    exact congrArg Block.place (show b = _ from hl)
  obtain rfl : Pp₀ = Pp := Option.some.inj (hP₀.symm.trans hP)
  obtain rfl : n₀ = n := Option.some.inj (hn₀.symm.trans hn)
  constructor
  · show b.rounds = _
    rw [IM.alone_rounds hl, ex]
    rfl
  · show b.oracles = _
    refine (congrArg Block.oracles (show b = _ from hl)).trans ?_
    show (x.retype : Block S Cl).oracles = _
    rw [ex]
    rfl

end

variable {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
  {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **THE SEATED DECISION's YES AT 339.** -/
theorem head_seat_laid (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    ∃ (b : Block S Cl) (nm : String) (Pp : Prep) (n : Nums),
      cF.blocksInOrder[339]? = some b ∧ b.place = headPlaceAt ∧
      prepOf Zp Bs.G₀ = some Pp ∧ numsAt Pp (some 24) = some n ∧
      b.rounds = rounds (k2P Zp headPlaceAt nm .head n) ∧
      b.oracles = [(k2P Zp headPlaceAt nm .head n).sent, []] ∧
      ∀ (z : ProofFile.InstPub) (s : S), Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 339 (z, s) →
        ∀ (r₁ r₂ : Fmt.RoundView) (ft : Nat) (d₁ d₂ : Fmt.Drawn) (cols : List OpenedColumn),
          d₂.poss = r₂.drawn.poss →
          roundsFit (rounds (k2P Zp headPlaceAt nm .head n)) [r₁, r₂] = true →
          cols.map (fun y => (y.1, y.2.1, y.2.2.length)) =
            (groupsOf ft (rounds (k2P Zp headPlaceAt nm .head n)) [d₁, d₂]).flatMap id →
          ∃ t, b.decide s [r₁, r₂]
            (laidGroups (k2P Zp headPlaceAt nm .head n) ft d₁ d₂ cols) = .ok t := by
  obtain ⟨hpl, hcut, -⟩ := six_at_head h.toAtMg O
  obtain ⟨b, nm, HP, Pp, n, hb, -, hP, hn, -, hseat⟩ :=
    head_seat_reached h.scope h.reads O h.laid.value hpl hcut
  obtain ⟨b', hb', hpc, hsh⟩ := head_seat_shape h.scope h.reads O hpl hcut
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
  obtain ⟨hro, hor⟩ := hsh nm Pp n hP hn
  refine ⟨b, nm, Pp, n, hb, hpc, hP, hn, hro, hor,
    fun z s hr r₁ r₂ ft d₁ d₂ cols hp hrf hcols => ?_⟩
  have h25 := h25_of_hy h.scope O (tests_at_head h.toAtMg O).1
  obtain ⟨a, Q, here, group⟩ := head_looks_reached h.scope h.reads O h25 hr
  obtain ⟨c₀, hc⟩ := code_look_reached h.scope h.reads O (by omega) (by omega) hr
  have hT := head_tied_whole h.toAtMg O hP hn hr headPlaceAt nm r₁ r₂
    (flat (k2P Zp headPlaceAt nm .head n)
      (laidGroups (k2P Zp headPlaceAt nm .head n) ft d₁ d₂ cols)) here group hc r₂.drawn.poss
  obtain ⟨-, t1, t2, t3⟩ := head_nums_reached h O hP hn hr headPlaceAt nm here group
  have ho := head_oldCode_reached h.scope h.reads O h.laid.value h.laid.planOk hP hn hr here
    Q.target hc
  rw [Array.getD_eq_getD_getElem?, ho] at t2
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := call_seven (k2P Zp headPlaceAt nm .head n)
    (headFrontOf s a Q.target) s.book s.roots r₁ r₂ c₀ ft d₁ d₂ cols hp hrf hcols t1 t2 t3 hT
  have HB := head_behind_seven h O hP hn hr headPlaceAt nm r₁ r₂ _ hrf here group hc
    ⟨⟨e1, e2, e3, e4, e5⟩, e6, e7⟩
  obtain ⟨G, HPl⟩ := HB.plain
  obtain ⟨u, hu⟩ := head_returns_sent HPl
  have eG : G = freshGroup s.check.frame.shape.code s.check.frame.shape.maskCode :=
    Option.some.inj (HPl.call.front.group.symm.trans (headGroup_reached h.toAtMg O hr a here))
  have hB : BehindReturns u := by
    refine head_behind_returns HPl ?_ hu
    rw [eG]
    exact own_at_head h.toAtMg O hP hn hr a Q.target
  exact hseat z s hr [r₁, r₂] _ u rfl HPl.groups hu hB

/-- **THE SEATED DECISION's YES AT 353.** -/
theorem fin_seat_laid (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    ∃ (b : Block S Cl) (nm : String) (Pp : Prep) (n : Nums),
      cF.blocksInOrder[353]? = some b ∧ b.place = k2PlaceF ∧
      prepOf Zp Bs.G₀ = some Pp ∧ numsAt Pp none = some n ∧
      b.rounds = rounds (k2P Zp k2PlaceF nm .finish n) ∧
      b.oracles = [(k2P Zp k2PlaceF nm .finish n).sent, []] ∧
      ∀ (z : ProofFile.InstPub) (s : S), Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 353 (z, s) →
        ∀ (r₁ r₂ : Fmt.RoundView) (ft : Nat) (d₁ d₂ : Fmt.Drawn) (cols : List OpenedColumn),
          d₂.poss = r₂.drawn.poss →
          roundsFit (rounds (k2P Zp k2PlaceF nm .finish n)) [r₁, r₂] = true →
          cols.map (fun y => (y.1, y.2.1, y.2.2.length)) =
            (groupsOf ft (rounds (k2P Zp k2PlaceF nm .finish n)) [d₁, d₂]).flatMap id →
          ∃ t, b.decide s [r₁, r₂]
            (laidGroups (k2P Zp k2PlaceF nm .finish n) ft d₁ d₂ cols) = .ok t := by
  obtain ⟨hpl, -⟩ := six_at_head h.toAtMg O
  obtain ⟨b, nm, Pp, n, hb, hP, hn, -, hseat⟩ := fin_seat_reached h.scope h.reads O hpl
  obtain ⟨b', hb', hpc, hsh⟩ := fin_seat_shape h.scope h.reads O hpl
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
  obtain ⟨hro, hor⟩ := hsh nm Pp n hP hn
  refine ⟨b, nm, Pp, n, hb, hpc, hP, hn, hro, hor,
    fun z s hr r₁ r₂ ft d₁ d₂ cols hp hrf hcols => ?_⟩
  have h25 := h25_of_hy h.scope O (tests_at_head h.toAtMg O).1
  obtain ⟨t, a, Q, hq, here, laid⟩ := fin_looks_reached h.scope h.reads O h25 hr
  obtain ⟨c₀, hc₀⟩ := code_look_reached h.scope h.reads O (by omega) (by omega) hr
  have hc : t.st.codes.base[t.check.frame.shape.code]? = some c₀ := by
    rw [finishFrontQ_st hq, (finishFrontQ_rest hq).2.2.2.2.1]
    exact hc₀
  obtain ⟨u, hu⟩ := fin_yes_reached h O hP hn hr hq k2PlaceF nm r₁ r₂ ft d₁ d₂ cols hp hrf hcols
    here laid hc
  exact hseat z s t hr hq [r₁, r₂] _ u rfl
    (groups_give (k2P Zp k2PlaceF nm .finish n) ft d₁ d₂ cols) hu

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_seat_shape
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_seat_shape
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_seat_laid
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_seat_laid
