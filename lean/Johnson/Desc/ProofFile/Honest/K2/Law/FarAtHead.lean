-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/FarAtHead.lean: the kind "the code switch" (K2): NUMBERS OF A
PUBLIC PLAN: THE SWITCHES' LOTS STAND FAR FROM THE SHARED SENDING's. Under the head and the opening,
at every place of the kind's list: each lot of messages (`switchMsgLots` at `switchNum`) bears the
witness's number at a tree and tenant whose first holder in the plan's list of seats has no kept
copy's role and stands in none of the shared sending's 52 sendings; each lot of pads
(`switchPadLots` at the tree and tenants that `switchSeatIn` finds) sits at a seat of the plan's
list that stands in none of these. The two ends are written after the premises hfar of the laws
`k1_lotsAgree_far`, `k1_msgsAgree_with`, `k1_padLotsAgree_far` and `k1_padsAgree_with`
(Honest/K1/Law/AgreeFar.lean, of other authors), at one place's lists; that file is not imported,
and no call is made here. Three definitions: public tests with code. Closed facts by evaluation in
Lean's kernel, with controls that say no; lemmas.

  `farSend`   A PUBLIC TEST: a sending's number is not 0, not 3 l + 1 or 3 l + 2 at l < 25, not 81
  `farMsg`    A PUBLIC TEST: the first holder of the tree and tenant of message n's seat has no kept
              copy's role, and its sending is far
  `farPad`    A PUBLIC TEST: message n's seat stands in the tree of message 0's, and its sending is
              far
  `farMsgW`, `farPadW`   BY LEAN's KERNEL: at the 25 written places: `farMsg` at every message of
              which the switch is the first sender; `farPad` at every message
  `far_can_fail`   CONTROLS: `farMsg` says no at every kept copy of every written place, and there
              are 36; `farSend` says no at 0, 1, 74 and 81 and yes at 3; `farPad` says no at every
              message of the first written place where the link is moved beyond the plan
  `farSend_gives`, `keptRole_gives`, `farMsg_gives`, `farPad_gives`   what a yes gives
  `far_msgs_at_head`, `far_pads_at_head`   THE ENDS

Limits. NUMBERS, SEATS AND ROLES ALONE: no lot's text is opened; no coin, input or run occurs. ONE
PLACE's LISTS: that a list over all places is their concatenation is left to the caller. That lots
agree is no tie. A kept copy has no lot of messages, so nothing is said of one; by the control the
first end's test would say no there. `farPad`'s ONE CONTROL IS WEAK: the plan has no seat there, and
that alone makes it say no; no control shows either of its two clauses saying no where a seat
stands. The full size and the format's second hash function alone. The head and the opening are premises;
that they can be met is not said. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.SwitchNumsAtHead
import Johnson.Desc.K1.Law.LaterOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1 (momL)
open P5T (PSeat Role seatsAllFull)
open P5J (AtMg F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest.FirstThread (MsgLot PadLot)

/-- **A PUBLIC TEST**: a sending's number is none of the shared sending's 52. -/
def farSend (s : Nat) : Bool :=
  s != 0 && (List.range 25).all (fun l => s != 3 * l + 1 && s != 3 * l + 2) && s != 81

/-- **A PUBLIC TEST**: message n has a seat; the first holder of that seat's tree and tenant has no
kept copy's role, and its sending is far. -/
def farMsg (ps : List PSeat) (l n : Nat) : Bool :=
  (switchSeatIn ps l n).any fun q₀ =>
    (ps.find? fun x => x.j == q₀.j && x.t == q₀.t).any fun q => !keptRole q.role && farSend q.send

/-- **A PUBLIC TEST**: messages 0 and n have seats; message n's stands in the tree of message 0's,
and its sending is far. -/
def farPad (ps : List PSeat) (l n : Nat) : Bool :=
  (switchSeatIn ps l 0).any fun q₀ =>
    (switchSeatIn ps l n).any fun q => q.j == q₀.j && farSend q.send

set_option maxRecDepth 1000000 in
/-- At every message of which the switch is the first sender, at every written place. -/
theorem farMsgW :
    (placesW.all fun p => allMsgs p fun n => !firstSender p n || farMsg seatsAllFull p.link n) =
      true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- At every message of every written place. -/
theorem farPadW : (placesW.all fun p => allMsgs p (farPad seatsAllFull p.link)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **Controls that say no.** -/
theorem far_can_fail :
    (placesW.all fun p => allMsgs p fun n => firstSender p n || !farMsg seatsAllFull p.link n) =
        true ∧
      ((placesW.map fun p => ((List.range (switchSent p.sizes p.others).size).filter fun n =>
        !firstSender p n).length).sum = 36) ∧
      farSend 0 = false ∧ farSend 1 = false ∧ farSend 74 = false ∧ farSend 81 = false ∧
      farSend 3 = true ∧
      ((placesW.take 1).any fun p => (List.range (switchSent p.sizes p.others).size).any
        (farPad seatsAllFull (p.link + 30))) = false := by
  decide +kernel

/-- What the first test's yes gives. -/
theorem farSend_gives {s : Nat} (h : farSend s = true) :
    s ≠ 0 ∧ (∀ l, l < 25 → ∀ d, s ≠ 3 * l + momL d) ∧ s ≠ 81 := by
  unfold farSend at h
  rw [Bool.and_eq_true, Bool.and_eq_true, bne_iff_ne, bne_iff_ne, List.all_eq_true] at h
  refine ⟨h.1.1, fun l hl d => ?_, h.2⟩
  have t := h.1.2 l (List.mem_range.2 hl)
  rw [Bool.and_eq_true, bne_iff_ne, bne_iff_ne] at t
  cases d
  · exact t.1
  · exact t.2

/-- A role that the test calls no kept copy's is none. -/
theorem keptRole_gives {r : Role} (h : keptRole r = false) : ∀ l k, r ≠ .kept l k := by
  intro l k e
  rw [e] at h
  cases h

/-- What the second test's yes gives. -/
theorem farMsg_gives {ps : List PSeat} {l n : Nat} (h : farMsg ps l n = true) :
    ∃ j t q, (ps.find? fun p => p.j == j && p.t == t) = some q ∧
      switchNumIn ps l n = P5T.arrOf ps j t ∧ (∀ l' k', q.role ≠ .kept l' k') ∧ q.send ≠ 0 ∧
      (∀ l, l < 25 → ∀ d, q.send ≠ 3 * l + momL d) ∧ q.send ≠ 81 := by
  unfold farMsg at h
  cases hs : switchSeatIn ps l n with
  | none =>
    rw [hs] at h
    cases h
  | some q₀ =>
    rw [hs] at h
    cases hf : (ps.find? fun x => x.j == q₀.j && x.t == q₀.t) with
    | none =>
      rw [Option.any_some, hf] at h
      cases h
    | some q =>
      rw [Option.any_some, hf, Option.any_some, Bool.and_eq_true, Bool.not_eq_true'] at h
      have f := farSend_gives h.2
      refine ⟨q₀.j, q₀.t, q, hf, ?_, keptRole_gives h.1, f.1, f.2.1, f.2.2⟩
      unfold switchNumIn
      rw [hs]

/-- What the third test's yes gives. -/
theorem farPad_gives {ps : List PSeat} {l n : Nat} (h : farPad ps l n = true) :
    ∃ q ∈ ps, ((switchSeatIn ps l 0).map (·.j)).getD 0 = q.j ∧
      ((switchSeatIn ps l n).map (·.t)).getD 0 = q.t ∧ q.send ≠ 0 ∧
      (∀ l, l < 25 → ∀ d, q.send ≠ 3 * l + momL d) ∧ q.send ≠ 81 := by
  unfold farPad at h
  cases h0 : switchSeatIn ps l 0 with
  | none =>
    rw [h0] at h
    cases h
  | some q₀ =>
    rw [h0] at h
    cases hs : switchSeatIn ps l n with
    | none =>
      rw [Option.any_some, hs] at h
      cases h
    | some q =>
      rw [Option.any_some, hs, Option.any_some, Bool.and_eq_true, beq_iff_eq] at h
      have f := farSend_gives h.2
      exact ⟨q, List.mem_of_find?_eq_some hs, h.1.symm, rfl, f.1, f.2.1, f.2.2⟩

variable {W : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {W₀ Rc Xi Tr : Type} {Bk : ProverCoinCounts}

/-- **UNDER THE HEAD AND THE OPENING: EACH LOT OF MESSAGES OF EACH PLACE STANDS FAR.** -/
theorem far_msgs_at_head (h : AtMg OnBytes.secondHashFunction W D₀ r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (ch : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers) (closing : Closing)
    (fx : Nat) :
    ∀ p ∈ switchPlaces Zp Bs.G₀,
      ∀ L' ∈ switchMsgLots (Bk := Bk) ch D readers closing p (switchNum Zp p) fx, ∃ j t q,
        ((P5J.At.pseatsAll Zp).find? fun p => p.j == j && p.t == t) = some q ∧
          L'.n = P5J.At.arr Zp j t ∧ (∀ l' k', q.role ≠ .kept l' k') ∧ q.send ≠ 0 ∧
          (∀ l, l < 25 → ∀ d, q.send ≠ 3 * l + momL d) ∧ q.send ≠ 81 := by
  rw [places_at_head h O]
  intro p hp L' hL'
  obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hL'
  obtain ⟨hr, h1⟩ := List.mem_filter.1 hn
  have t := List.all_eq_true.1 (List.all_eq_true.1 farMsgW p hp) n hr
  rw [h1, Bool.not_true, Bool.false_or, ← pseatsAll_at_head h] at t
  exact farMsg_gives t

/-- **UNDER THE HEAD AND THE OPENING: EACH LOT OF PADS OF EACH PLACE STANDS FAR.** -/
theorem far_pads_at_head (h : AtMg OnBytes.secondHashFunction W D₀ r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) (ch : Nat) :
    ∀ p ∈ switchPlaces Zp Bs.G₀,
      ∀ L' ∈ switchPadLots (Bk := Bk) (W₀ := W₀) (Rc := Rc) (Xi := Xi) (Tr := Tr) ch p
          (((switchSeatIn (P5J.At.pseatsAll Zp) p.link 0).map (·.j)).getD 0)
          (fun n => ((switchSeatIn (P5J.At.pseatsAll Zp) p.link n).map (·.t)).getD 0),
        ∃ q ∈ P5J.At.pseatsAll Zp, L'.j = q.j ∧ L'.t = q.t ∧ q.send ≠ 0 ∧
          (∀ l, l < 25 → ∀ d, q.send ≠ 3 * l + momL d) ∧ q.send ≠ 81 := by
  rw [places_at_head h O]
  intro p hp L' hL'
  obtain ⟨n, hr, rfl⟩ := List.mem_map.1 hL'
  have t := List.all_eq_true.1 (List.all_eq_true.1 farPadW p hp) n hr
  rw [← pseatsAll_at_head h] at t
  exact farPad_gives t

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.farSend
#print axioms ProofFile.Honest.K2.Law.farMsg
#print axioms ProofFile.Honest.K2.Law.farPad
#print axioms ProofFile.Honest.K2.Law.farMsgW
#print axioms ProofFile.Honest.K2.Law.farPadW
#print axioms ProofFile.Honest.K2.Law.far_can_fail
#print axioms ProofFile.Honest.K2.Law.farSend_gives
#print axioms ProofFile.Honest.K2.Law.keptRole_gives
#print axioms ProofFile.Honest.K2.Law.farMsg_gives
#print axioms ProofFile.Honest.K2.Law.farPad_gives
#print axioms ProofFile.Honest.K2.Law.far_msgs_at_head
#print axioms ProofFile.Honest.K2.Law.far_pads_at_head
