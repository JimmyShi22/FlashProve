-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/K7CarryCell.lean: the open item `carry 23` of the first chain's
invariant passes over the next token's sub-protocol (kind K7, number 338), at `keeps` := `fHeadI`
(FHeadI.lean). No definition.

The item's statement is the variable `carryX` of `lettersHead`. The authors of kind K2 have written
a text for it, `carryExact` (Johnson/Desc/K2/Honest/Carry/Exact.lean). It reads the verifier's state
through the library's `doorZ` (Johnson/Top/H0/K2Caller/CarryClosed.lean). Before number 338 the
chain is between two segments, and `doorZ` runs the output head's first step itself, at a blank plan
of the smallness test. After number 338 the chain is in the head's segment, not yet opened, and
`doorZ` returns the state as it is. The library's `carry_over_reply`
(Johnson/Top/H0/K2Caller/CarryOverReply.lean) shows for its own statement of the item that the two
say the same. This file goes the same way for the library's relation `DoorLike`
(Johnson/Top/H0/Walk/FrameCarryEnds.lean), under which `carryExact` passes (`carryExact_doorLike`,
CarryFrame.lean).

  1  `doorZ_headFront`, `doorLike_reply`   where the switch that spends the item is the head's:
     `H1Keeps` from `s` to `s'` gives `DoorLike Z m s' s`. General in the public part and in `m`
  2  `stands23_head`   under the library's `AtMgA` the switch number 23 is the head's
  3  `carry7At_full`, `carry7At_control`, `carry_k7_is`   a closed test by Lean's kernel on the
     written lists: an item `carry m` that is open on both sides of number 338 has m = 23. The
     negative test: with 22 the test fails
  4  `cell_carry_k7`   the hypothesis `RidesPastAtS` (Honest/Thread/SharesS.lean) by the kind of the
     place, under `hD`: `carryX` passes under `DoorLike` (the hypothesis `hD` of `carry_frame`,
     CarryFrame.lean)
  5  `cell_carry_k7_exact`   the cell at `carryX := carryExact Zp (P5J.At.arr Zp)`, without `hD`

Limits.
  * Full size only, and only under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * At `keeps` := `fHeadI` only. At `fHeadH` the clause at K7 does not give `H1Keeps` up to the
    state after the step.
  * Where the switch that spends an item `carry m` is a segment's, `doorLike_reply` says nothing.
  * Nothing here shows that the item's statement holds at any state of a run.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FHeadI
import Johnson.Desc.ProofFile.Honest.Thread.CarryFrame
import Johnson.Desc.ProofFile.Honest.Thread.CarryRides
import Johnson.Desc.ProofFile.Honest.Thread.OpenNext
import Johnson.Desc.ProofFile.Honest.Thread.PileKeptK2
import Johnson.Top.H0.K2Caller.CarryReads
import Johnson.Top.H0.K2Caller.StandsLow
import Johnson.Top.H0.Tw.K2C.Asks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (S Item)
open VerifiableInference.Desc.First.K2 (frontAt headFrontQ headFrontQ_iff)
open VerifiableInference.Desc.First.K2Caller (rest doorZ rest_out)
open VerifiableInference.Desc.K2.Honest (carryExact)
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.Desc.First.Walk.Tied (FrontsLike DoorLike)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-! ## 1 The way in, before and after the next token's sub-protocol -/

/-- Where the switch is the head's: at a state in the head's segment, not yet opened, `doorZ`
returns the state itself. -/
theorem doorZ_headFront {Z : ProofFile.Pub} {m : Nat} (hs : (ProofFile.pAtK2 Z m).stands = .head) {u : S}
    {a : VerifiableInference.Desc.First.HeadOwn} (ha : u.here = .head a)
    (ho : a.opened = false) : doorZ Z m u = some u := by
  unfold doorZ
  rw [hs]
  simp only [ha, ho]
  rfl

/-- **What `doorZ` lets in before the sub-protocol it lets in after it, alike.** -/
theorem doorLike_reply {Z : ProofFile.Pub} {m : Nat} (hs : (ProofFile.pAtK2 Z m).stands = .head)
    {tl : OnBytes.Model.HTailF2} {V : Nat} {s s' : S} (K : H1Keeps tl V s s') :
    DoorLike Z m s' s := by
  obtain ⟨-, t, h0, o, x, ho, hop, -, -, rfl⟩ := K
  obtain ⟨x0, s₁, a0, k0⟩ := (headFrontQ_iff tl s t).1 h0
  have hq : s.here = .between := by
    have hb := k0.between
    cases hq : s.here <;>
      first
        | rfl
        | simp [VerifiableInference.Desc.First.S.atBetween, hq] at hb
  have hout : s.inLink = false := by
    simp [VerifiableInference.Desc.First.S.inLink, VerifiableInference.Desc.First.S.fork?, hq]
  have hnh : ∀ a, s.here ≠ .head a := fun a e => by
    rw [hq] at e
    cases e
  obtain ⟨t', h1, hfr, hbk, hrt⟩ :=
    VerifiableInference.Desc.First.K2Caller.headFrontQ_tl tl {} s t h0
  have hds : doorZ Z m s = some t' := by
    have e1 := Johnson.Desc.First.Walk.Tied.doorZ_head (Z := Z) (m := m) hs hnh
    rw [rest_out s hout, h1] at e1
    exact e1
  intro t₀ hd
  obtain rfl : t' = t₀ := Option.some.inj (hds.symm.trans hd)
  refine ⟨{ t with out := { t.out with reply := some x } },
    doorZ_headFront (u := { t with out := { t.out with reply := some x } }) hs ho hop,
    hbk, hrt, fun fx hfx => ⟨fx, ?_, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩⟩
  have e : frontAt (ProofFile.pAtK2 Z m) { t with out := { t.out with reply := some x } } =
      frontAt (ProofFile.pAtK2 Z m) t := rfl
  rw [e, ← hfr]
  exact hfx

/-! ## 3 The closed test -/

set_option maxRecDepth 1000000 in
/-- Which items `carry` are open on both sides of number 338. -/
theorem carry7At_full : (((IM.openAt P5J.At.links P5J.At.ps 338).filter fun i =>
      (IM.openAt P5J.At.links P5J.At.ps 339).contains i).all fun i =>
      match i with
      | .carry m => m == 23
      | _ => true) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: with 22 in the place of 23 the same test fails. -/
theorem carry7At_control : (((IM.openAt P5J.At.links P5J.At.ps 338).filter fun i =>
      (IM.openAt P5J.At.links P5J.At.ps 339).contains i).all fun i =>
      match i with
      | .carry m => m == 22
      | _ => true) = false := by
  decide +kernel

/-- The test at an item. -/
theorem carry_k7_is {m : Nat} (ho : Item.carry m ∈ IM.openAt P5J.At.links P5J.At.ps 338)
    (ho' : Item.carry m ∈ IM.openAt P5J.At.links P5J.At.ps 339) : m = 23 :=
  eq_of_beq (show (m == 23) = true from
    List.all_eq_true.1 carry7At_full _ (List.mem_filter.2 ⟨ho, List.contains_iff_mem.2 ho'⟩))

/-! ## 2, 4 and 5 At the invariant -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
  (G : ProofFile.Ground) (take : Nat → Bool)
  (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
  (P13 : VerifiableInference.Desc.K13.Where)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

include h in
/-- The switch number 23 is the head's. -/
theorem stands23_head : (ProofFile.pAtK2 Zp 23).stands = .head := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact VerifiableInference.Desc.First.K2Caller.stands23 h.scope h.reads O h.laid.planOk
    (H2K12.spots_atAll h (OnBytes.Road.K4.cut_of_head h.toAtMg)) (P1K2.links25_atAll h)

/-- The item `carry m` at a place of the kind K7. -/
theorem cell_carry_k7
    (hD : ∀ m (z : ProofFile.InstPub) (s s' : TS) (y y' : Strs) (v : WtF), DoorLike Zp m s' s →
      carryX m (z, s) y v → carryX m (z, s') y' v)
    {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K7) {m : Nat}
    (hi : Item.carry m ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadI Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.opened b)
    (h1 : Item.carry m ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadI Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.row b).shuts) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadI Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      b (Item.carry m) := by
  obtain ⟨ho, ho'⟩ := head_open_both h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadI Zp cF G take P11 p12 P13 h.𝔇.pubD)) w hb hi h1 (fun e => by cases e)
  obtain rfl := k7_number_of hb hp hk
  obtain rfl := carry_k7_is ho ho'
  exact ridesPastAtS_of _ _ (ridesPastAt_carry_of h H Q test carryX item n₁ n₂ b₀ Vd Rd
    (kpBy (fHeadI Zp cF G take P11 p12 P13 h.𝔇.pubD)) w 23 fun s s' hK z y y' v =>
      hD 23 z s s' y y' v (doorLike_reply (stands23_head h)
        (show H1Keeps G.W.H.tl G.W.hS.V s s' from
          ((kpBy_at _ hk s s').1 ((head_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd
            (kpBy (fHeadI Zp cF G take P11 p12 P13 h.𝔇.pubD)) w hp s s').1 hK)).2)))

/-- The item `carry m` at a place of the kind K7, at the text `carryExact`. -/
theorem cell_carry_k7_exact {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K7) {m : Nat}
    (hi : Item.carry m ∈ (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
      Rd (kpBy (fHeadI Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.opened b)
    (h1 : Item.carry m ∉ ((lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
      Rd (kpBy (fHeadI Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.row b).shuts) :
    RidesPastAtS (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
      Rd (kpBy (fHeadI Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      b (Item.carry m) :=
  cell_carry_k7 h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd w G take
    P11 p12 P13 Said
    (fun m z s s' y y' v hd c => carryExact_doorLike Zp (P5J.At.arr Zp) m z s s' y y' v hd c)
    hb hp hk hi h1

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.doorZ_headFront
#print axioms ProofFile.Honest.FirstThread.doorLike_reply
#print axioms ProofFile.Honest.FirstThread.carry7At_full
#print axioms ProofFile.Honest.FirstThread.carry7At_control
#print axioms ProofFile.Honest.FirstThread.carry_k7_is
#print axioms ProofFile.Honest.FirstThread.stands23_head
#print axioms ProofFile.Honest.FirstThread.cell_carry_k7
#print axioms ProofFile.Honest.FirstThread.cell_carry_k7_exact
