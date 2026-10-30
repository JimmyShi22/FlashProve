-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/MadeOwnAtHead.lean: under the library's head and the opening: the public test on the reads' data says yes at each of the 25 seats of
the array "U3"; so, in front of the closing of a segment, the test `ownHeard` (Honest/K2/AtPlan.lean: the data of every own
message of the segments up to that one are ready at the challenges heard) hangs on two named premises alone.

  `u3FrontB`, `u3Front_written`, `u3Front_bite`   a test on the written seats of "U3" below segment 24: the array's columns are the
                     written count, and the sending begins where the written rows say that the segment's own rounds end; by
                     Lean's kernel, with a control
  `valsHalf_at_head`, `u3Fits_at_head`   the public test at every seat, at covered positions of the right length
  `own_seat_seg`      the seat at the address of an own message of the segments up to l is a segment's up to l
  `VecAt`             THE NAMED PREMISE ON THE READS: at each seat of a segment up to l the maker of the segment's vector returns
                     at the challenges in front of the sending
  `reads_at_closing`  the premise on the reads' filling of `ownHeard_of_two` (MadeOwnAB.lean), from `VecAt`
  **`ownHeard_at_closing`**   `ownHeard` at the filling `widerRows Sz.ref`, from `DigitsFit` (MadeOwnDigits.lean) and `VecAt`

By, of other authors: `u3Fits_halves`, `u3SeatsFit_at_head`, `seats_at_head` (Johnson/HonestTrace/U3Fit/SeatsAtHead.lean) ·
`valsHalf_head_at_head` (HeadAtHead.lean) · `layersVals_at_head` (LayersAtHead.lean) · `attVals_at_head`
(Honest/K5/Law/AttValsAtHead.lean) · `valsAt_layers_at_head`, `valsAt_att_at_head` (ValsSorts.lean) · `lookFits_layers`,
`lookFits_head` (LookFits.lean) · `covOf_sized_of_okStart` (Honest/K2/Law/CovOfAtStart.lean).

Limits. `DigitsFit` and `VecAt` are premises, shown of nothing here. The head and the opening are hypotheses. The full size and
the older hash alone.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeOwnStand
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeOwnReads
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeOwnABFit
import Johnson.Desc.ProofFile.Honest.AtPureWider
import Johnson.Desc.ProofFile.Honest.K2.Law.CovOfAtStart
import Johnson.Desc.ProofFile.Honest.K5.Law.AttValsAtHead
import Johnson.HonestTrace.U3Fit.ReturnsAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (Chain Block)
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.PlanWritten (cutFirstFull)
open OnBytes.Maker (WholeD)
open OnBytes.Model (Head.Covered)
open OnBytes.HonestTrace (Sz Seat seatsOf allSeated)
open OnBytes.HonestTrace.U3 (SegVals valsAt u3Seats u3Fits u3Rows u3RowsOf covOf)
open OnBytes.HonestTrace.U3.Fit (seatsW seats_at_head u3Fits_halves valsHalf u3SeatsFit seatsFitBy
  u3SeatsFit_at_head valsHalf_head_at_head layersVals_at_head valsAt_layers_at_head
  valsAt_att_at_head lookFits_layers lookFits_head colsW rowsBeforeW)
open OnBytes.HonestTrace.U3.Att (attVals_at_head)
open ProofFile.Honest.K2 (segmentsOf mineDigits mineReads ownHeard)
open ProofFile.Honest.K2.Law (segsW addrsW zipIdx_take_mem segments_at_head covOf_sized_of_okStart)
open P5J (AtMgA TS F0T)
open _root_.Desc.K14.Law (secondAt seatZ)

/-! ## 1 The written seats of "U3" -/

/-- At each written seat below segment 24: the array's columns are the written count, and the
sending begins where the written rows say that the segment's own rounds end. off: a shift, for the
control. -/
def u3FrontB (off : Nat) : Bool :=
  (seatsW "U3").all fun s => s.seg == 24 ||
    (s.array.sizeC == colsW s.seg &&
      (cutFirstFull[14 * s.seg + 4 + off]?).map
        (fun c => rowsBeforeW (14 * s.seg + 4 + off) + c.2.2.1) == some s.heard)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
theorem u3Front_written : u3FrontB 0 = true := by decide +kernel

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
/-- A control: against the rows one further on the test says no. -/
theorem u3Front_bite : u3FrontB 1 = false := by decide +kernel

/-! ## 2 The public test under the head -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem valsHalf_at_head (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {cov : Head.Covered}
    (hc : cov.sized G.W.hS.T = true) : ∀ s ∈ u3Seats Zp G, valsHalf Zp G cov s = true := by
  intro s hs
  have hsW : s ∈ seatsW "U3" := by
    rw [← seats_at_head h hG "U3"]
    exact hs
  have hlt : s.seg < 25 :=
    of_decide_eq_true (Eq.mp (Bool.and_eq_true _ _) (List.all_eq_true.1 seatFront_u3 s hsW)).1
  by_cases e24 : s.seg = 24
  · exact valsHalf_head_at_head h hG hc (lookFits_head h hG) s hs e24
  · rcases Eq.mp (Bool.or_eq_true _ _) (List.all_eq_true.1 u3Front_written s hsW) with t | t
    · exact absurd (beq_iff_eq.1 t) e24
    · obtain ⟨t1, t2⟩ := Eq.mp (Bool.and_eq_true _ _) t
      have c1 : s.array.sizeC = colsW s.seg := beq_iff_eq.1 t1
      have c2 : (cutFirstFull[14 * s.seg + 4]?).map
          (fun c => rowsBeforeW (14 * s.seg + 4) + c.2.2.1) = some s.heard := beq_iff_eq.1 t2
      have key : ∀ V : SegVals, valsAt Zp G cov s.seg = .ok V → V.n = colsW s.seg →
          (cutFirstFull[14 * s.seg + 4]?).map
            (fun c => rowsBeforeW (14 * s.seg + 4) + c.2.2.1) = some V.front →
          valsHalf Zp G cov s = true := by
        intro V hV e1 e2
        have f1 : V.front = s.heard := Option.some.inj (e2.symm.trans c2)
        unfold valsHalf
        rw [hV]
        show (V.front == s.heard && s.array.sizeC == V.n) = true
        rw [f1, c1, e1, beq_self_eq_true, beq_self_eq_true]
        rfl
      obtain ⟨g, hg⟩ : ∃ g, s.seg = 2 * g ∨ s.seg = 2 * g + 1 := ⟨s.seg / 2, by omega⟩
      rcases hg with hg | hg
      · obtain ⟨V, hV, e1, e2⟩ := layersVals_at_head h hG (g := g) (by omega)
          (lookFits_layers h hG (by omega))
        refine key V ?_ (by rw [hg]; exact e1) (by rw [hg]; exact e2)
        rw [hg, valsAt_layers_at_head h hG (by omega) cov]
        exact hV
      · obtain ⟨V, hV, e1, e2⟩ := attVals_at_head h hG (g := g) (by omega)
        refine key V ?_ (by rw [hg]; exact e1) (by rw [hg]; exact e2)
        rw [hg, valsAt_att_at_head h hG (by omega) cov]
        exact hV

/-- **The public test on the reads' data says yes at every seat.** -/
theorem u3Fits_at_head (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {cov : Head.Covered}
    (hc : cov.sized G.W.hS.T = true) :
    ∀ s ∈ u3Seats Zp G, u3Fits Zp G cov s = true ∧ s.seg < G.first.shape.link.length := by
  intro s hs
  have k := u3SeatsFit_at_head h hG
  unfold u3SeatsFit seatsFitBy at k
  obtain ⟨⟨k1, -⟩, k3⟩ := (by simpa only [Bool.and_eq_true] using k :
    (allSeated G.first.shape.link.length (u3Seats Zp G) = true ∧ _) ∧ _)
  refine ⟨?_, ?_⟩
  · rw [u3Fits_halves, List.all_eq_true.1 k3 s hs, valsHalf_at_head h hG hc s hs]
    rfl
  · unfold allSeated at k1
    have hm : s.seg ∈ (u3Seats Zp G).map (·.seg) := List.mem_map_of_mem hs
    rw [beq_iff_eq.1 k1] at hm
    exact List.mem_range.1 hm

end

/-! ## 3 In front of a closing -/

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}

/-- The seat at the address of an own message of the segments up to l is a segment's up to l. -/
theorem own_seat_seg (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {l : Nat} {Qc : Par} (hQ : Qc.link = l)
    {name : String} (hB : seatSegB name = true) {a : MsgAddr}
    (ha : OwnAddr (addrsAt Zp Bs.G₀) (lotSegs Zp Bs.G₀ Qc) a) {t : Seat}
    (ht : OnBytes.HonestTrace.seatAt (seatsOf Zp Bs.G₀ name) a = some t) : t.seg ≤ l := by
  rw [seats_at_head h O.blank name] at ht
  obtain ⟨y, hy, s, hs, e⟩ := ha
  have eS : lotSegs Zp Bs.G₀ Qc = segsW.take (l + 1) := by
    show (segmentsOf Zp Bs.G₀).take (Qc.link + 1) = _
    rw [segments_at_head h.toAtMg O, hQ]
  rw [eS] at hy
  have hyW := zipIdx_take_mem segsW (l + 1) hy
  have hyl : y.2 < l + 1 := by
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_take] at hy
    split at hy
    · assumption
    · cases hy
  rw [addrs_at_head h O] at e
  have t1 := List.all_eq_true.1 (List.all_eq_true.1 hB y hyW) s hs
  rw [e, Option.all_some, ht, Option.all_some] at t1
  have e1 : t.seg = y.2 := beq_iff_eq.1 t1
  omega

/-- **The named premise on the reads**: at the seat of each address, of a segment up to l, the maker of the segment's
vector returns at the challenges in front of the sending. -/
def VecAt (Z : Pub) (G : Ground) (cov : Head.Covered) (heard : List Fmt.Drawn) (l : Nat) : Prop :=
  ∀ a s, OnBytes.HonestTrace.seatAt (u3Seats Z G) a = some s → s.seg ≤ l →
    ∀ V, valsAt Z G cov s.seg = .ok V → ∃ v, V.vec (heard.take s.heard) = .ok v

/-- **THE READS' DATA ARE READY IN FRONT OF A CLOSING**, where the makers of the vectors return. -/
theorem reads_at_closing (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {l : Nat} (hl : l < 25) {Qc : Par} (hQ : Qc.link = l)
    {ξ : ProofFile.Inst} (hx : (F0T OnBytes.secondHashFunction Zp Np cF).okStart ξ = true) {heard : List Fmt.Drawn}
    (hd : drawsFit (declsTo cF.blocksInOrder (14 * l + IM.nAt l + 5)) heard = true)
    (Vr : VecAt Zp Bs.G₀ ((covOf Zp Bs.G₀ ξ).toOption.getD default) heard l) :
    ∀ a, OwnAddr (addrsAt Zp Bs.G₀) (lotSegs Zp Bs.G₀ Qc) a → mineReads Zp Bs.G₀ a = true →
      (u3RowsOf Zp Bs.G₀ ξ).readyAt heard a = true := by
  intro a ha _
  show (u3Rows Zp Bs.G₀ ((covOf Zp Bs.G₀ ξ).toOption.getD default)).readyAt heard a = true
  obtain ⟨e1, e2⟩ := heard_fits_front h hd
  cases hs : OnBytes.HonestTrace.seatAt (u3Seats Zp Bs.G₀) a with
  | none => exact reads_ready_none hs heard
  | some s =>
    have hm : s ∈ u3Seats Zp Bs.G₀ := List.mem_of_find?_eq_some hs
    obtain ⟨f1, f2⟩ := u3Fits_at_head h O.blank (covOf_sized_of_okStart h O hx) s hm
    refine reads_ready hs f2 f1 e2 ?_ (Vr a s hs (own_seat_seg h O hQ seatSeg_u3 ha hs))
    rw [e1]
    exact own_seat_le h O hl hQ seatFront_u3 seatSeg_u3 ha hs

/-- **IN FRONT OF A CLOSING THE DATA OF EVERY OWN MESSAGE OF THE SEGMENTS UP TO IT ARE READY**, from
the two named premises. -/
theorem ownHeard_at_closing (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {l : Nat} (hl : l < 25) {Qc : Par} (hQ : Qc.link = l)
    {ξ : ProofFile.Inst} (hx : (F0T OnBytes.secondHashFunction Zp Np cF).okStart ξ = true) {heard : List Fmt.Drawn}
    (hd : drawsFit (declsTo cF.blocksInOrder (14 * l + IM.nAt l + 5)) heard = true)
    (F : ∀ a, mineDigits Zp Bs.G₀ a = true → DigitsFit Zp Bs.G₀ (K3.matsOwn Bs.G₀.W) a)
    (Vr : VecAt Zp Bs.G₀ ((covOf Zp Bs.G₀ ξ).toOption.getD default) heard l) :
    ownHeard (widerRows Sz.ref Zp Bs.G₀ ξ) (askPlace (addrsAt Zp Bs.G₀)) (lotSegs Zp Bs.G₀ Qc)
      heard = true :=
  ownHeard_of_two (allFit_at_head h O) (digits_at_stand h O hl hQ F hd)
    (reads_at_closing h O hl hQ hx hd Vr)

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.u3Front_written
#print axioms ProofFile.Honest.K10.u3Front_bite
#print axioms ProofFile.Honest.K10.valsHalf_at_head
#print axioms ProofFile.Honest.K10.u3Fits_at_head
#print axioms ProofFile.Honest.K10.own_seat_seg
#print axioms ProofFile.Honest.K10.reads_at_closing
#print axioms ProofFile.Honest.K10.ownHeard_at_closing
