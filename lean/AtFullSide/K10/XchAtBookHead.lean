-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/XchAtBookHead.lean: the closing of a segment (K10): the fields on the book of the records `FreshBySwitch`,
`FreshByShared`, `TieBySwitch` and `TieByShared` (Johnson/Desc/ProofFile/Honest/K10/Pay/), in the records' own terms, at the book
of whatever the maker returns, under the head, at all 25 closings.

  `tie_later_book`, `tie_open_book`, `fresh_open_book`   at the written book, at the shared kind's jobs
  **`fresh_switch_field`**, **`tie_switch_field`**, **`front_switch_field`**   segments 1 to 24
  **`tie_later_field`**   every segment: a later moment's message
  **`tie_open_field`**, **`fresh_open_field`**   the first segment

Limits. Premises: the head, that the maker returns, and the closing's tie Tied; at the fields, that p is a written place of link l,
that the ground's segments are the written ones, that the parameters q have the written shape and codes, and for a later moment
the closed test laterB at its number. Owners, starts and counts alone: what a coin holds is not said. The full size alone.
-/
import AtFullSide.K10.XchAtBookShared
import AtFullSide.K10.PaysAtHead
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeParts
import Johnson.Desc.ProofFile.Honest.K10.Pay.FrameFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K10
open ProofFile.Honest ProofFile.Honest.K10 AtFullSide.K14
open ProofFile.Honest.K2 (SwitchPlace dueBefore messageDue fromE switchSent switchFresh segmentsOf)
open ProofFile.Honest.K2.Law (segsW placesW)
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.Desc.ReqLit (shapeFull)
open Johnson.G (codesFull2 proofSendsFull)
open OnBytes.Maker (WholeD)
open P2Law.ProofPlan (WP)
open P5J (AtMgA TS)

/-- The job of a later moment of segment l. -/
abbrev laterJ {Xi X : Type} (q : OnBytes.Params.First) (gp : _root_.Desc.Plain.GPar) (l : Nat) (d : Bool) (first : Nat)
    (D : RowDataOf Xi) : ProofFile.Honest.K1.SendJob (ProofFile.Honest.K1.PlaceIn Xi) X :=
  ProofFile.Honest.K1.laterJobAt q gp l (IM.k1Ix l d + 1) (if d then 2 else 1) first D

/-- The job of the first segment's opening. -/
abbrev openJ {Xi X : Type} (q : OnBytes.Params.First) (gp : _root_.Desc.Plain.GPar) (first : Nat) (D : RowDataOf Xi) :
    ProofFile.Honest.K1.SendJob (ProofFile.Honest.K1.PlaceIn Xi) X :=
  ProofFile.Honest.K1.placeJob (VerifiableInference.Desc.K1.firstPar q gp) first (ProofFile.Honest.K1.firstFold q) D

section
variable {q : OnBytes.Params.First} {gp : _root_.Desc.Plain.GPar} {B : ProverCoinCounts} {Xi X : Type}

/-- A later moment's count, at the written values. -/
theorem later_due (hs : q.shape = shapeFull) (hc : q.codes = codesFull2) (l : Nat) (d : Bool) (first : Nat)
    (D : RowDataOf Xi) :
    ProofFile.Honest.K1.dueR (laterJ (X := X) q gp l d first D).P (laterJ (X := X) q gp l d first D).ride =
      dueS codesFull2 (sentLater l (if d then 2 else 1)) (fun _ => none) (sentLater l (if d then 2 else 1)).size := by
  have er : ProofFile.Honest.K1.rideOf none = (fun _ => none) := funext fun _ => rfl
  show dueS q.codes (VerifiableInference.Desc.K1.parLater q gp l (IM.k1Ix l d + 1) (if d then 2 else 1)).sent
      (ProofFile.Honest.K1.rideOf none)
      (VerifiableInference.Desc.K1.parLater q gp l (IM.k1Ix l d + 1) (if d then 2 else 1)).sent.size = _
  rw [later_sent hs, hc, er]

/-- **The field book of `TieByShared` at a later moment, at the written book.** lo: the message's number among the group's. -/
theorem tie_later_book (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
    (mergesByName WP.first.blocksInOrder) = .ok B) {Q : Par} (hQ : Q ∈ parsW) (hs : q.shape = shapeFull)
    (hc : q.codes = codesFull2) (first : Nat) (D : RowDataOf Xi) (d : Bool) (lo : Nat)
    (ht : laterB 0 lo Q.link d = true) :
    ∀ n, n < 1 → ∃ e, (K12.Light.carriedOf B (closeAddr Q))[0 + frontAt Q.link + (lo + n)]? = some e ∧
      e.owner = ⟨(laterJ (X := X) q gp Q.link d first D).P.place, 0⟩ ∧
      e.start = ProofFile.Honest.K1.startR (laterJ (X := X) q gp Q.link d first D).P
        (laterJ (X := X) q gp Q.link d first D).ride n ∧
      e.start.f + e.count.f ≤ (ProofFile.Honest.K1.dueR (laterJ (X := X) q gp Q.link d first D).P
        (laterJ (X := X) q gp Q.link d first D).ride).f ∧
      e.start.e + e.count.e ≤ (ProofFile.Honest.K1.dueR (laterJ (X := X) q gp Q.link d first D).P
        (laterJ (X := X) q gp Q.link d first D).ride).e := by
  intro n hn
  obtain rfl : n = 0 := by omega
  unfold laterB at ht
  cases hv : (viewAt (addrAt Q.link))[frontAt Q.link + lo]? with
  | none =>
    rw [hv] at ht
    cases ht
  | some v =>
    rw [hv] at ht
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ht
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := ht
    have a : ((K12.Light.carriedOf B (closeAddr Q)).map viewE)[0 + frontAt Q.link + (lo + 0)]? = some v := by
      rw [view_close hB hQ, show 0 + frontAt Q.link + (lo + 0) = frontAt Q.link + lo by omega]
      exact hv
    obtain ⟨e, he, ev⟩ := at_view a
    have eo : e.owner = v.1 := congrArg (·.1) ev
    have es : e.start = v.2.1 := congrArg (·.2.1) ev
    have ec : e.count = v.2.2 := congrArg (·.2.2) ev
    refine ⟨e, he, eo.trans h1, es.trans h2, ?_, ?_⟩
    · rw [later_due hs hc, es, ec]
      exact h3
    · rw [later_due hs hc, es, ec]
      exact h4

/-- The opening's count and starts, at the written values. -/
theorem open_start (hs : q.shape = shapeFull) (hc : q.codes = codesFull2) (first : Nat) (D : RowDataOf Xi) (n : Nat) :
    ProofFile.Honest.K1.startR (openJ (X := X) q gp first D).P (openJ (X := X) q gp first D).ride n =
      dueS codesFull2 sentOpen rideOpen n := by
  show dueS q.codes (VerifiableInference.Desc.K1.firstPar q gp).sent (ProofFile.Honest.K1.rideOf (ProofFile.Honest.K1.firstFold q)) n = _
  rw [open_sent hs, open_ride hs, hc]

theorem open_due (hs : q.shape = shapeFull) (hc : q.codes = codesFull2) (first : Nat) (D : RowDataOf Xi) :
    ProofFile.Honest.K1.dueR (openJ (X := X) q gp first D).P (openJ (X := X) q gp first D).ride =
      dueS codesFull2 sentOpen rideOpen sentOpen.size := by
  show dueS q.codes (VerifiableInference.Desc.K1.firstPar q gp).sent (ProofFile.Honest.K1.rideOf (ProofFile.Honest.K1.firstFold q))
    (VerifiableInference.Desc.K1.firstPar q gp).sent.size = _
  rw [open_sent hs, open_ride hs, hc]

/-- **The field book of `TieByShared` at the first segment's opening, at the written book.** -/
theorem tie_open_book (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
    (mergesByName WP.first.blocksInOrder) = .ok B) {Q : Par} (hQ : Q ∈ parsW) (h0 : Q.link = 0) (hs : q.shape = shapeFull)
    (hc : q.codes = codesFull2) (first : Nat) (D : RowDataOf Xi) :
    ∀ n, n < 3 → ∃ e, (K12.Light.carriedOf B (closeAddr Q))[0 + frontAt Q.link + (0 + n)]? = some e ∧
      e.owner = ⟨(openJ (X := X) q gp first D).P.place, 0⟩ ∧
      e.start = ProofFile.Honest.K1.startR (openJ (X := X) q gp first D).P (openJ (X := X) q gp first D).ride n ∧
      e.start.f + e.count.f ≤ (ProofFile.Honest.K1.dueR (openJ (X := X) q gp first D).P
        (openJ (X := X) q gp first D).ride).f ∧
      e.start.e + e.count.e ≤ (ProofFile.Honest.K1.dueR (openJ (X := X) q gp first D).P
        (openJ (X := X) q gp first D).ride).e := by
  intro n hn
  have t := List.all_eq_true.1 open_written n (List.mem_range.2 hn)
  cases hv : (viewAt (addrAt 0))[frontAt 0 + (0 + n)]? with
  | none =>
    simp only [hv] at t
    cases t
  | some v =>
    simp only [hv, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at t
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := t
    have a : ((K12.Light.carriedOf B (closeAddr Q)).map viewE)[0 + frontAt Q.link + (0 + n)]? = some v := by
      rw [view_close hB hQ, h0, show 0 + frontAt 0 + (0 + n) = frontAt 0 + (0 + n) by omega]
      exact hv
    obtain ⟨e, he, ev⟩ := at_view a
    have eo : e.owner = v.1 := congrArg (·.1) ev
    have es : e.start = v.2.1 := congrArg (·.2.1) ev
    have ec : e.count = v.2.2 := congrArg (·.2.2) ev
    have hz : (dueS codesFull2 sentOpen rideOpen n).plus ⟨0, 0⟩ = dueS codesFull2 sentOpen rideOpen n := by
      rcases dueS codesFull2 sentOpen rideOpen n with ⟨x, y⟩
      rfl
    rw [hz] at h2
    refine ⟨e, he, eo.trans h1, ?_, ?_, ?_⟩
    · rw [open_start hs hc, es, h2]
    · rw [open_due hs hc, es, ec]
      exact h3
    · rw [open_due hs hc, es, ec]
      exact h4

/-- **The field book of `FreshByShared` at the first segment, at the written book.** -/
theorem fresh_open_book (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
    (mergesByName WP.first.blocksInOrder) = .ok B) {Q : Par} (hQ : Q ∈ parsW) (h0 : Q.link = 0) (hs : q.shape = shapeFull)
    (hc : q.codes = codesFull2) (first : Nat) (D : RowDataOf Xi) :
    ∀ e ∈ B.ahead, (e.spender == closeAddr Q) = true → e.once = true →
      e.owner = ⟨(openJ (X := X) q gp first D).P.place, 0⟩ ∧
      e.start.e = ProofFile.Honest.K1.maskStart (openJ (X := X) q gp first D).P (openJ (X := X) q gp first D).ride 3 := by
  intro e he h1 h2
  have hm := once_short hB hQ he h1 h2
  have ht : (rawShortW.filter fun x => x.once && x.spender == addrAt 0).map (fun x => (x.owner, x.start.e)) =
      [((⟨⟨1, some 0, 1, .K1⟩, 0⟩ : Addr), maskOpen + 0)] := beq_iff_eq.1 fresh_open_written
  have hq : closeAddr Q = addrAt 0 := by rw [addr_of_par hQ, h0]
  rw [← hq] at ht
  have hv := List.mem_map_of_mem (f := fun x : Ahead => (x.owner, x.start.e)) hm
  rw [ht] at hv
  have hv' := List.mem_singleton.1 hv
  refine ⟨congrArg Prod.fst hv', (congrArg Prod.snd hv').trans ?_⟩
  show maskOpen = (ProofFile.Honest.K1.startR (openJ (X := X) q gp first D).P (openJ (X := X) q gp first D).ride 3).e +
    if (Johnson.Prover.Send.shapeAt (openJ (X := X) q gp first D).P 3).mainDeg == 3 then
      (ProofFile.Honest.K1.stepsOf (openJ (X := X) q gp first D).P.codes (Johnson.Prover.Send.shapeAt (openJ (X := X) q gp first D).P 3)
        ((openJ (X := X) q gp first D).ride 3)).main else 0
  have e1 : Johnson.Prover.Send.shapeAt (openJ (X := X) q gp first D).P 3 = (sentOpen.getD 3 default).shape := by
    show ((VerifiableInference.Desc.K1.firstPar q gp).sent.getD 3 default).shape = _
    rw [open_sent hs]
  have e2 : (openJ (X := X) q gp first D).ride 3 = rideOpen 3 := by
    show ProofFile.Honest.K1.rideOf (ProofFile.Honest.K1.firstFold q) 3 = _
    rw [open_ride hs]
  have e3 : (openJ (X := X) q gp first D).P.codes = codesFull2 := hc
  rw [open_start hs hc, e1, e2, e3]
  rfl

end

/-! ## At the book of whatever the maker returns -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X}
  {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
  {l : Nat} {pw : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block TS ProofFile.Cl}
  (Td : Tied cF Zp l pw Qc blk)

include h hA in
/-- The maker's book is the written book. -/
theorem book_is_written : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
    (mergesByName WP.first.blocksInOrder) = .ok A.B := by
  obtain ⟨B, hB, -, -, -, hall⟩ := makers_book_one h
  obtain ⟨eB, -⟩ := hall _ _ _ _ _ P A hA
  rw [eB]
  exact hB

include h Td in
/-- The closing's numbers are written, its link is l, and its block stands at its place. -/
theorem tied_written : Qc ∈ parsW ∧ Qc.link = l ∧ (⟨blk.place, 0⟩ : Addr) = closeAddr Qc := by
  have hk := frame_plink h Td
  obtain ⟨-, hQ, -, -, hm, hp, -⟩ := Td
  obtain ⟨q1, -⟩ := IM.k10Par_fields hQ
  refine ⟨pars_at_head h ▸ hm, q1.trans hk, ?_⟩
  rw [hp]
  rfl

include h hA Td in
/-- **The field book of `FreshBySwitch`, at the maker's book.** -/
theorem fresh_switch_field {p : SwitchPlace} (hp : p ∈ placesW) (hl : p.link = l) :
    ∀ e ∈ A.B.ahead, (e.spender == ⟨blk.place, 0⟩) = true → e.once = true → e.owner = ⟨p.place, 0⟩ ∧
      e.start.e = (dueBefore p.sizes.codes (switchSent p.sizes p.others) (switchFresh p.sizes p.others p.foldVars)
          ((switchSent p.sizes p.others).size - 1)).e +
        fromE p.sizes.codes
          ((switchSent p.sizes p.others).getD ((switchSent p.sizes p.others).size - 1) default).shape := by
  obtain ⟨hQ, hk, ea⟩ := tied_written h Td
  rw [ea]
  exact fresh_switch_book (book_is_written h hA) hQ hp (hl.trans hk.symm)

/-- How many messages the segments in front have sent, at the lot's segments. -/
theorem front_lot {Gr : ProofFile.Ground} (hseg : segmentsOf Zp Gr = segsW) (Q : Par) :
    ((lotSegs Zp Gr Q).dropLast.map (·.messages)).sum = frontAt Q.link := by
  unfold lotSegs frontAt
  rw [hseg]

include h hA Td in
/-- **The field book of `TieBySwitch`, at the maker's book.** -/
theorem tie_switch_field {Gr : ProofFile.Ground} (hseg : segmentsOf Zp Gr = segsW) {p : SwitchPlace} (hp : p ∈ placesW)
    (hl : p.link = l) :
    ∀ n, n + 1 < (switchSent p.sizes p.others).size → ∃ e, (K12.Light.carriedOf A.B ⟨blk.place, 0⟩)[
        0 + ((lotSegs Zp Gr Qc).dropLast.map (·.messages)).sum + (0 + n)]? = some e ∧
      e.owner = ⟨p.place, 0⟩ ∧
      e.start = dueBefore p.sizes.codes (switchSent p.sizes p.others) (switchFresh p.sizes p.others p.foldVars) n ∧
      e.count = messageDue p.sizes.codes ((switchSent p.sizes p.others).getD n default).shape
        (K2.foldAt (switchFresh p.sizes p.others p.foldVars) n) := by
  obtain ⟨hQ, hk, ea⟩ := tied_written h Td
  rw [ea, front_lot hseg]
  exact tie_switch_book (book_is_written h hA) hQ hp (hl.trans hk.symm)

include h hA Td in
/-- **The field bookFront of `TieBySwitch`, at the maker's book.** -/
theorem front_switch_field {Gr : ProofFile.Ground} (hseg : segmentsOf Zp Gr = segsW) {p : SwitchPlace} (hp : p ∈ placesW)
    (hl : p.link = l) :
    ∀ n, n < 0 + ((lotSegs Zp Gr Qc).dropLast.map (·.messages)).sum →
      ∃ e e', (K12.Light.carriedOf A.B ⟨blk.place, 0⟩)[n]? = some e ∧
        (K12.Light.carriedOf A.B ⟨p.place, 0⟩)[n]? = some e' ∧
        e.owner = e'.owner ∧ e.start = e'.start ∧ e.count = e'.count := by
  obtain ⟨hQ, hk, ea⟩ := tied_written h Td
  rw [ea, front_lot hseg]
  exact tie_switch_front (book_is_written h hA) hQ hp (hl.trans hk.symm)

include h hA Td in
/-- **The field book of `TieByShared` at a later moment, at the maker's book.** -/
theorem tie_later_field {Gr : ProofFile.Ground} (hseg : segmentsOf Zp Gr = segsW) {q : OnBytes.Params.First}
    (hs : q.shape = shapeFull) (hc : q.codes = codesFull2) (gp : _root_.Desc.Plain.GPar) {Xi Xj : Type} (first : Nat)
    (Dt : RowDataOf Xi) (d : Bool) (lo : Nat) (ht : laterB 0 lo l d = true) :
    ∀ n, n < 1 → ∃ e, (K12.Light.carriedOf A.B ⟨blk.place, 0⟩)[
        0 + ((lotSegs Zp Gr Qc).dropLast.map (·.messages)).sum + (lo + n)]? = some e ∧
      e.owner = ⟨(laterJ (X := Xj) q gp l d first Dt).P.place, 0⟩ ∧
      e.start = ProofFile.Honest.K1.startR (laterJ (X := Xj) q gp l d first Dt).P (laterJ (X := Xj) q gp l d first Dt).ride n ∧
      e.start.f + e.count.f ≤ (ProofFile.Honest.K1.dueR (laterJ (X := Xj) q gp l d first Dt).P
        (laterJ (X := Xj) q gp l d first Dt).ride).f ∧
      e.start.e + e.count.e ≤ (ProofFile.Honest.K1.dueR (laterJ (X := Xj) q gp l d first Dt).P
        (laterJ (X := Xj) q gp l d first Dt).ride).e := by
  obtain ⟨hQ, hk, ea⟩ := tied_written h Td
  subst hk
  rw [ea, front_lot hseg]
  exact tie_later_book (book_is_written h hA) hQ hs hc first Dt d lo ht

include h hA Td in
/-- **The field book of `TieByShared` at the first segment's opening, at the maker's book.** -/
theorem tie_open_field {Gr : ProofFile.Ground} (hseg : segmentsOf Zp Gr = segsW) (h0 : l = 0) {q : OnBytes.Params.First}
    (hs : q.shape = shapeFull) (hc : q.codes = codesFull2) (gp : _root_.Desc.Plain.GPar) {Xi Xj : Type} (first : Nat)
    (Dt : RowDataOf Xi) :
    ∀ n, n < 3 → ∃ e, (K12.Light.carriedOf A.B ⟨blk.place, 0⟩)[
        0 + ((lotSegs Zp Gr Qc).dropLast.map (·.messages)).sum + (0 + n)]? = some e ∧
      e.owner = ⟨(openJ (X := Xj) q gp first Dt).P.place, 0⟩ ∧
      e.start = ProofFile.Honest.K1.startR (openJ (X := Xj) q gp first Dt).P (openJ (X := Xj) q gp first Dt).ride n ∧
      e.start.f + e.count.f ≤ (ProofFile.Honest.K1.dueR (openJ (X := Xj) q gp first Dt).P
        (openJ (X := Xj) q gp first Dt).ride).f ∧
      e.start.e + e.count.e ≤ (ProofFile.Honest.K1.dueR (openJ (X := Xj) q gp first Dt).P
        (openJ (X := Xj) q gp first Dt).ride).e := by
  obtain ⟨hQ, hk, ea⟩ := tied_written h Td
  rw [ea, front_lot hseg]
  exact tie_open_book (book_is_written h hA) hQ (hk.trans h0) hs hc first Dt

include h hA Td in
/-- **The field book of `FreshByShared` at the first segment, at the maker's book.** -/
theorem fresh_open_field (h0 : l = 0) {q : OnBytes.Params.First} (hs : q.shape = shapeFull) (hc : q.codes = codesFull2)
    (gp : _root_.Desc.Plain.GPar) {Xi Xj : Type} (first : Nat) (Dt : RowDataOf Xi) :
    ∀ e ∈ A.B.ahead, (e.spender == ⟨blk.place, 0⟩) = true → e.once = true →
      e.owner = ⟨(openJ (X := Xj) q gp first Dt).P.place, 0⟩ ∧
      e.start.e = ProofFile.Honest.K1.maskStart (openJ (X := Xj) q gp first Dt).P (openJ (X := Xj) q gp first Dt).ride 3 := by
  obtain ⟨hQ, hk, ea⟩ := tied_written h Td
  rw [ea]
  exact fresh_open_book (book_is_written h hA) hQ (hk.trans h0) hs hc first Dt

end

end AtFullSide.K10

#print axioms AtFullSide.K10.later_due
#print axioms AtFullSide.K10.tie_later_book
#print axioms AtFullSide.K10.open_start
#print axioms AtFullSide.K10.open_due
#print axioms AtFullSide.K10.tie_open_book
#print axioms AtFullSide.K10.fresh_open_book
#print axioms AtFullSide.K10.book_is_written
#print axioms AtFullSide.K10.tied_written
#print axioms AtFullSide.K10.fresh_switch_field
#print axioms AtFullSide.K10.front_lot
#print axioms AtFullSide.K10.tie_switch_field
#print axioms AtFullSide.K10.front_switch_field
#print axioms AtFullSide.K10.tie_later_field
#print axioms AtFullSide.K10.tie_open_field
#print axioms AtFullSide.K10.fresh_open_field
