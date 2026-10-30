-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/FallsHeadFull.lean: `fallsHead` (Honest/Law/FallsHead.lean) under
the library's hypothesis `AtMgA`. The definition of the first chain's list of falls leaves a record
out where a look-up does not return. Under `AtMgA`, at the ground that the library's maker yields,
all four look-ups return, so the list has its 87 records. Every record stands at a fall's seat. And
at each of the fifty numbers of the chain at which a batching or the sub-protocol after it stands,
the list has the named record at that sub-protocol's place.

By the library's `IM.k9_of` (Johnson/IMR/LinkSeat.lean), `IM.ground_gets`
(Johnson/IMR/PureJoin.lean), `IM.k4_of` (Johnson/IMR/K4Seat.lean) and `P5J.At.places_paid`
(Johnson/P5J/PlacesPaid.lean), and by the lemmas of Honest/Law/FallsHeadAt.lean.

  1  `hear_len_yes`, `hear_len_control`   the batching's piece, as the library states it, is the
     written one: a closed statement by `decide +kernel`, and a control that rejects
  2  `k9At_full`, `built_full`, `plan_full`, `places_full`   the look-ups return; the chain's places
  3  `fallsHead_87`   the list has 87 records
  4  `fallsHead_seats_full`   every record stands at a fall's seat
  5  `front_full`, `front_full_head`, `behind_full`, `behind_full_head`   at the fifty numbers

Limits.
  * `AtMgA` is a hypothesis. `hB` says that `Bs` is what the library's maker returns at the public
    part.
  * The five open arguments of `fallsHead` stay open.
  * The statements of section 5 say that there is a record. Their proofs give the named one.
  * Nothing is said on how likely a record is to speak.
  * Full size only, at the hash function `secondHashFunction` (Honest/Thread/FirstAt.lean says which that is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.FallsHeadAt
import Johnson.IMR.K4Seat
import Johnson.IMR.PureJoin
import Johnson.P5J.PlacesPaid
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Place KindName Block Chain)
open VerifiableInference.Desc.First (S kindsBeforeBatching)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

/-! ## 1 The batching's piece -/

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
theorem hear_len_yes : ((List.range 25).all fun l =>
    (kindsBeforeBatching (IM.subAt l) (l == 0)).length + 1 == 8 + 2 * oAt l) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- A control: with 7 in the stead of 8 the test rejects. -/
theorem hear_len_control : ((List.range 25).all fun l =>
    (kindsBeforeBatching (IM.subAt l) (l == 0)).length + 1 == 7 + 2 * oAt l) = false := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}
  {cols tau : Nat → Nat} {share notGood : Nat → Odds} {r0 : Nat → Nat}

/-! ## 2 The look-ups return -/

/-- At each segment `IM.k9At` and `testsWhere` return, and what the first returns stands in chain 1,
in that segment, at the batching's piece. -/
theorem k9At_full (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l < 25) :
    ∃ p u, IM.k9At Zp l = some p ∧
      VerifiableInference.Desc.K9.testsWhere Zp.p.X l 0 = some u ∧
      p.chain = 1 ∧ p.link = l ∧ p.piece = 8 + 2 * oAt l := by
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain ⟨Lk, p, u, T, -, hp, q3, q1, q2, -, -, -, -, -, -, -, -, -, hu, -, -, -, -⟩ :=
    (IM.k9_of h.scope h.reads O).2 l hl
  have t := List.all_eq_true.1 hear_len_yes l (List.mem_range.2 hl)
  exact ⟨p, u, hp, hu, q1, q2, q3.trans (beq_iff_eq.1 t)⟩

/-- At each segment the planned link is there. -/
theorem built_full (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {l : Nat} (hl : l < 25) :
    (Bs.G₀.built[l]?).isSome = true := by
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hB)
  obtain ⟨sz, -⟩ := IM.ground_gets h.scope h.reads O.pub O.blank
  rw [Array.getElem?_eq_getElem (by omega)]
  rfl

/-- At each feed-forward segment the plan is there. -/
theorem plan_full (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {g : Nat} (hg : g < 12) :
    (Bs.G₀.W.G[g]?).isSome = true := by
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hB)
  obtain ⟨Lk, b, y, -, -, -, -, -, -, -, e, -⟩ := IM.k4_of h.scope h.reads O g hg
  rw [e]
  rfl

/-- The chain's places are the written list. -/
theorem places_full (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    cF.blocksInOrder.map (·.place) = P5J.At.ps :=
  P5J.At.places_paid h.scope h.reads h.laid

/-! ## 3 Eighty-seven records -/

/-- Under `AtMgA` the list has 87 records. -/
theorem fallsHead_87 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    (fallsHead Zp Bs.G₀ cols tau share notGood r0).length = 87 :=
  fallsHead_length
    (fun l hl => by
      obtain ⟨p, u, hp, -⟩ := k9At_full h hl
      rw [hp]
      rfl)
    (fun l hl => by
      obtain ⟨p, u, -, hu, -⟩ := k9At_full h hl
      rw [hu]
      rfl)
    (fun _ hl => built_full h hB hl) (fun _ hg => plan_full h hB hg)

/-! ## 4 Every record stands at a fall's seat -/

/-- The field `hfs` of `FirstAsks`, at this list. -/
theorem fallsHead_seats_full (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G₀ : ProofFile.Ground) :
    ∀ f ∈ fallsHead Zp G₀ cols tau share notGood r0, fallSeat P5J.At.links f.place = true :=
  fallsHead_seats fun l hl p hp => by
    obtain ⟨p', u, hp', -, q⟩ := k9At_full h hl
    obtain rfl : p' = p := Option.some.inj (hp'.symm.trans hp)
    exact q

/-! ## 5 At the fifty numbers -/

/-- At the batching of segment `l`, for `l` below 24. -/
theorem front_full (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G₀ : ProofFile.Ground) {l : Nat}
    (hl : l < 24) :
    ∀ blk, cF.blocksInOrder[14 * l + 9]? = some blk →
      ∃ F ∈ fallsHead Zp G₀ cols tau share notGood r0, F.place = blk.place ∧
        ∀ s ds, F.test s ds = none → K8.k8Front s ds = none :=
  front_at (places_full h) hl

/-- At the batching of segment 24. -/
theorem front_full_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G₀ : ProofFile.Ground) :
    ∀ blk, cF.blocksInOrder[347]? = some blk →
      ∃ F ∈ fallsHead Zp G₀ cols tau share notGood r0, F.place = blk.place ∧
        ∀ s ds, F.test s ds = none → K8.k8Front s ds = none :=
  front_at_head (places_full h)

/-- At the sub-protocol after the batching of segment `l`, for `l` below 24: both records, at
whatever the two look-ups return. -/
theorem behind_full (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G₀ : ProofFile.Ground} {l : Nat}
    (hl : l < 24) {Xl : OnBytes.Model.Stages.LinkH}
    {u : VerifiableInference.Desc.K9.SegSort × Nat × VerifiableInference.Desc.K9.TWhere}
    (hX : G₀.built[l]? = some Xl)
    (hu : VerifiableInference.Desc.K9.testsWhere Zp.p.X l 0 = some u) :
    ∀ blk, cF.blocksInOrder[14 * l + 10]? = some blk →
      (∃ F ∈ fallsHead Zp G₀ cols tau share notGood r0, F.place = blk.place ∧
        ∀ s ds, F.test s ds = none → K9.freeSlotShare u.2.2.filled s = none) ∧
      ∃ F ∈ fallsHead Zp G₀ cols tau share notGood r0, F.place = blk.place ∧
        ∀ s ds, F.test s ds = none → K8.k8Share (ProofFile.k8ParW Zp G₀ Xl l).nU s = none := by
  intro blk hb
  obtain ⟨p, u', hp, hu', q1, q2, q3⟩ := k9At_full h (l := l) (by omega)
  obtain rfl : u' = u := Option.some.inj (hu'.symm.trans hu)
  rw [show oAt l = 0 from if_neg (by omega)] at q3
  exact ⟨quiet_at (places_full h) hl hp ⟨q1, q2, q3⟩ hu' blk hb,
    share_at (places_full h) hl hX blk hb⟩

/-- The same at segment 24. -/
theorem behind_full_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G₀ : ProofFile.Ground}
    {Xl : OnBytes.Model.Stages.LinkH}
    {u : VerifiableInference.Desc.K9.SegSort × Nat × VerifiableInference.Desc.K9.TWhere}
    (hX : G₀.built[24]? = some Xl)
    (hu : VerifiableInference.Desc.K9.testsWhere Zp.p.X 24 0 = some u) :
    ∀ blk, cF.blocksInOrder[348]? = some blk →
      (∃ F ∈ fallsHead Zp G₀ cols tau share notGood r0, F.place = blk.place ∧
        ∀ s ds, F.test s ds = none → K9.freeSlotShare u.2.2.filled s = none) ∧
      ∃ F ∈ fallsHead Zp G₀ cols tau share notGood r0, F.place = blk.place ∧
        ∀ s ds, F.test s ds = none → K8.k8Share (ProofFile.k8ParW Zp G₀ Xl 24).nU s = none := by
  intro blk hb
  obtain ⟨p, u', hp, hu', q1, q2, q3⟩ := k9At_full h (l := 24) (by omega)
  obtain rfl : u' = u := Option.some.inj (hu'.symm.trans hu)
  exact ⟨quiet_at_head (places_full h) hp ⟨q1, q2, q3⟩ hu' blk hb,
    share_at_head (places_full h) hX blk hb⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.hear_len_yes
#print axioms ProofFile.Honest.hear_len_control
#print axioms ProofFile.Honest.k9At_full
#print axioms ProofFile.Honest.built_full
#print axioms ProofFile.Honest.plan_full
#print axioms ProofFile.Honest.places_full
#print axioms ProofFile.Honest.fallsHead_87
#print axioms ProofFile.Honest.fallsHead_seats_full
#print axioms ProofFile.Honest.front_full
#print axioms ProofFile.Honest.front_full_head
#print axioms ProofFile.Honest.behind_full
#print axioms ProofFile.Honest.behind_full_head
