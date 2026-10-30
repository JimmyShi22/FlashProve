-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/OwnAtSender.lean: the kind "the code switch" (K2): THE PREMISE
hd OF `key_at_walk` AND ITS KIN (Honest/K2/Law/KeyAtWalk.lean, which this file does not import), AT
THE SENDER's OWN DATA AS THE KIND's LOT LAYS THEM: the main rows of each message of the sender's
sending, but the last, are one at the sender and at a later switch's closing. One test with code;
statements with their proofs.

  `ownAddrsFit`    A PUBLIC TEST at two places: the sending's size is 1 + the kept + the others; at
                 each own message of moment 0 the later place's look-up names the sender's own
                 address, and the segment's shape has the degree of the sender's
  `mainRows_same`, `ownAt_sender`, `hd_of_fit`   hd, out of the test's yes and h0
  `ownAddrsFitW`, `ownAddrsFitW_can_fail`, `ownAddrsFitW_asked`   THE CLOSED FACT at the written
                 places; a control: the sender's place bent; the test is asked at 300 pairs, and
                 at each the sender has an own message of moment 0
  `hd_at_head`     THE END, under the head

WHAT IS LEFT OF hd: h0: the filling D lays each own message of the sender's sending at no challenge
(`heardAt` = 0 at its address): a fact on D, not paid in this file. It need not stay a premise where
the sender's closing returns: `h0_of_closing` (Honest/K2/Law/ReadyOfClosing.lean, which this file
does not import) draws it out of that return. THE SENDER's OWN DATA: `senderOwn`
(Honest/K2/Law/SenderOwn.lean): an abbreviation of `switchWit`'s text.

Limits. ONE D AND ONE Rd STAND AT BOTH SIDES: at the kind's lot both are made of one input
(`switchWit`'s text: D w.x, readers w): `rowsLaid_inv` (SenderOwn.lean) says so for the sender; for
the later switch it is a matter of the caller's letters. The closed facts are by Lean's kernel,
replayed by no independent checker. No coin stands in this file. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.CopyAtClosing
import Johnson.Desc.ProofFile.Honest.K2.Law.TiesWritten
import Johnson.Desc.ProofFile.Honest.K2.Law.SenderOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K2.Honest (Left mainRows Sizes)
open P5J (AtMg F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open Reads

variable {W₀ Rc Xi Tr : Type}

/-! ## 1 The test, and hd out of its yes -/

/-- **A PUBLIC TEST** at two places. -/
def ownAddrsFit (segs : List SegmentPub) (p₀ p : SwitchPlace) : Bool :=
  decide ((switchSent p₀.sizes p₀.others).size = 1 + p₀.sizes.kept.length + p₀.others.size) &&
    (List.range (p₀.others.size - 1)).all fun m =>
      decide (p.addrs p₀.link m = some (p₀.ownAddr m)) &&
        ((((segs[p₀.link]?).map fun (Sg : SegmentPub) => Sg.ownShapes (p₀.link == 0)).getD []).getD
          m {}).mainDeg == (p₀.others.getD m default).shape.mainDeg

/-- `mainRows` reads of the own data one message alone, and none in front of the own messages. -/
theorem mainRows_same (Z : Sizes) (W : Left) {own own' : Nat → Nat → Nat → Cb.Gl.E} {n : Nat}
    (h : Z.kept.length < n → own (n - 1 - Z.kept.length) = own' (n - 1 - Z.kept.length)) :
    mainRows Z W own n = mainRows Z W own' n := by
  by_cases h1 : (n == 0) = true
  · simp only [mainRows, if_pos h1]
  · by_cases h2 : n ≤ Z.kept.length
    · simp only [mainRows, if_neg h1, if_pos h2]
    · simp only [mainRows, if_neg h1, if_neg h2]
      exact h (by omega)

/-- One own message, at the later switch's closing and at the sender. -/
theorem ownAt_sender (segs : List SegmentPub) (p₀ p : SwitchPlace) (D : RowData) (Rd : Readers)
    (heard : List Fmt.Drawn) {m : Nat} (ha : p.addrs p₀.link m = some (p₀.ownAddr m))
    (hs : ((((segs[p₀.link]?).map fun (Sg : SegmentPub) => Sg.ownShapes (p₀.link == 0)).getD
      []).getD m {}).mainDeg = (p₀.others.getD m default).shape.mainDeg)
    (h0 : D.heardAt (p₀.ownAddr m) = 0) :
    lotOwn segs p D Rd heard p₀.link m = senderOwn D Rd p₀ m := by
  funext b j
  show ownBy D Rd p.addrs _ heard p₀.link m b j = _
  unfold ownBy
  rw [ha]
  show asRow (_ == 3) (D.at_ Rd heard (p₀.ownAddr m) b j) = _
  rw [hs, at_of_take D Rd (heard' := []) (p₀.ownAddr m) (by rw [h0]; rfl)]

/-- **hd.** -/
theorem hd_of_fit {segs : List SegmentPub} {p₀ p : SwitchPlace}
    (hfit : ownAddrsFit segs p₀ p = true)
    (D : RowData) (Rd : Readers) (heard : List Fmt.Drawn)
    (h0 : ∀ m, m < p₀.others.size - 1 → D.heardAt (p₀.ownAddr m) = 0) (W : Left) :
    ∀ n, n < (switchSent p₀.sizes p₀.others).size - 1 →
      mainRows p₀.sizes W (lotOwn segs p D Rd heard p₀.link) n =
        mainRows p₀.sizes W (senderOwn D Rd p₀) n := by
  unfold ownAddrsFit at hfit
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hfit
  obtain ⟨hsz, hall⟩ := hfit
  intro n hn
  refine mainRows_same p₀.sizes W fun hk => ?_
  have hm : n - 1 - p₀.sizes.kept.length < p₀.others.size - 1 := by omega
  have hx := List.all_eq_true.1 hall _ (List.mem_range.2 hm)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hx
  exact ownAt_sender segs p₀ p D Rd heard hx.1 hx.2 (h0 _ hm)

/-! ## 2 The closed facts -/

theorem ownAddrsFitW :
    (placesW.all fun p => placesW.all fun p₀ =>
      decide (p.link ≤ p₀.link) || ownAddrsFit segsW p₀ p) = true := by
  decide +kernel

/-- A control: with the sender's place bent into the later one's the test says no, at each pair. -/
theorem ownAddrsFitW_can_fail :
    (placesW.all fun p => placesW.all fun p₀ =>
      decide (p.link ≤ p₀.link) || !ownAddrsFit segsW { p₀ with place := p.place } p) = true := by
  decide +kernel

/-- Neither of the two is empty: the pairs at which the fence says no; and those among them at
which the sender has an own message of moment 0, so that the test's second half is asked. -/
theorem ownAddrsFitW_asked :
    (placesW.map fun p =>
        (placesW.filter fun p₀ => decide (p₀.link < p.link)).length).sum = 300 ∧
      (placesW.map fun p =>
        (placesW.filter fun p₀ =>
          decide (p₀.link < p.link) && decide (1 < p₀.others.size)).length).sum = 300 := by
  decide +kernel

/-! ## 3 At the library's head -/

variable {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {Wp : VerifierAndGoals.PublicFiles} {Dw : OnBytes.Maker.WholeD} {rn : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **THE END.** -/
theorem hd_at_head (h : AtMg OnBytes.secondHashFunction Wp Dw rn Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction Wp.pol Wp.lay Wp.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {p₀ p : SwitchPlace} (hp₀ : p₀ ∈ switchPlaces Zp Bs.G₀) (hp : p ∈ switchPlaces Zp Bs.G₀)
    (hl : p₀.link < p.link) (D : RowData) (Rd : Readers) (heard : List Fmt.Drawn)
    (h0 : ∀ m, m < p₀.others.size - 1 → D.heardAt (p₀.ownAddr m) = 0) (W : Left) :
    ∀ n, n < (switchSent p₀.sizes p₀.others).size - 1 →
      mainRows p₀.sizes W (lotOwn (segmentsOf Zp Bs.G₀) p D Rd heard p₀.link) n =
        mainRows p₀.sizes W (senderOwn D Rd p₀) n := by
  rw [places_at_head h O] at hp₀ hp
  rw [segments_at_head h O]
  have h2 := List.all_eq_true.1 (List.all_eq_true.1 ownAddrsFitW p hp) p₀ hp₀
  rw [Bool.or_eq_true] at h2
  have h2' : ownAddrsFit segsW p₀ p = true := by
    rcases h2 with e | e
    · exact absurd (of_decide_eq_true e) (by omega)
    · exact e
  exact hd_of_fit h2' D Rd heard h0 W

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.ownAddrsFit
#print axioms ProofFile.Honest.K2.Law.mainRows_same
#print axioms ProofFile.Honest.K2.Law.ownAt_sender
#print axioms ProofFile.Honest.K2.Law.hd_of_fit
#print axioms ProofFile.Honest.K2.Law.ownAddrsFitW
#print axioms ProofFile.Honest.K2.Law.ownAddrsFitW_can_fail
#print axioms ProofFile.Honest.K2.Law.ownAddrsFitW_asked
#print axioms ProofFile.Honest.K2.Law.hd_at_head
