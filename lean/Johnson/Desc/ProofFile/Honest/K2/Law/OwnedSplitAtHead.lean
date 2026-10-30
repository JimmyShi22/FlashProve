-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/OwnedSplitAtHead.lean: NUMBERS OF A PUBLIC PLAN: UNDER THE
LIBRARY's HEAD AND THE OPENING THE FIELD owned OF `JoinFit` (Honest/Thread/JoinFit.lean, of other
authors), AT THE PLAN's LIST OF THE FIRST CHAIN's SEATS, FOLLOWS FROM THREE SENDERS' LIMBS; AND THE
SWITCHES' LIMBS HOLD WHEREVER THE LIST HOLDS THE KIND's SHARE. Definitions with code; forms of
premises; closed facts by Lean's kernel, two of them controls; statements with their proofs.

THE COUNT, AT THE WRITTEN PLAN. The first chain has 199 seats: 57 in the shared sending's 52
sendings (the plan's sendings 0, 3 l + 1, 3 l + 2 and 81) · 132 in the switches' 25 (sendings 3, 6,
…, 75) · 10 in the sendings 76 to 80. A kept copy's seat bears the number of the message that it
repeats: so a lot of messages is asked for each NUMBER, a lot of pads for each SEAT.

  `sharedSend`, `lastSend`   whose a sending's number is: the shared sending's · 76 to 80
  `sharedSeatsW`, `lastSeatsW`   the written seats of these sendings
  `arrW`, `k2PadsW`, `k2NumsW`, `otherNumsW`   the witness's number of a seat, the switches' seats,
                    the numbers of the messages of which a switch is the first sender, and the
                    numbers of the two other classes' seats, all off the written lists
  `arrW_is`         `arrW` is a second text of the sealed `OnBytes.Road.K4.arrW`: one term
  `arrW_at_head`    under the head the plan's numbering `P5J.At.arr Zp` is `arrW`: a call of the
                    sealed `P5J.AtMg.arr_is`
  `MsgsOwnedAt`, `PadsOwnedAt`   THE FORMS OF THE LIMBS: at each seat of a list a lot of messages
                    bears the seat's number · a lot of pads sits at the seat
  `ownedW`          BY LEAN's KERNEL: each written seat is one of the three classes; each written
                    seat's number is a switch's first sender's, or that of a seat of the two other
                    classes. CONTROLS: without the third class each test says no
  `owned_of_three`  THE SPLIT: the six limbs ⊢ the field owned at lists ml, pl
  `share_nums_limb`, `share_pads_limb`   the switches' two limbs where a record holds the kind's
                    share
  `owned_at_join`   the same at the joined lists: four limbs are left, the shared sending's and the
                    third sender's

Limits. NUMBERS AND SEATS ALONE: "owned" asks that a lot bears the number or sits at the seat, not
that its text answers. THE FOUR LIMBS OF THE TWO OTHER SENDERS ARE PREMISES: shown here at no list.
Whose the sendings 76 to 80 are this file does not say. The head and the opening are premises. The
full size; the format's second hash function. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.FlatSeatsAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.JoinShareAtHead
import Johnson.Road.K4.K4PlanWritten
import Johnson.LPFE1R.K10ClearAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1 (momL)
open ProofFile.Honest.FirstThread (MsgLot PadLot TreeLot Others joinMl joinPl)
open P5T (PSeat seatsAllFull psFull)
open P5J (AtMg F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

/-- The number of one of the shared sending's 52 sendings in the plan's list. -/
def sharedSend (s : Nat) : Bool :=
  s == 0 || s == 81 || (List.range 25).any fun l => [false, true].any fun d => s == 3 * l + momL d

/-- The sendings 76 to 80. -/
def lastSend (s : Nat) : Bool := decide (76 ≤ s) && decide (s ≤ 80)

/-- The written seats of the shared sending's sendings. -/
def sharedSeatsW : List PSeat := psFull.filter fun q => sharedSend q.send

/-- The written seats of the sendings 76 to 80. -/
def lastSeatsW : List PSeat := psFull.filter fun q => lastSend q.send

/-- The witness's number of a seat, off the written list of all three chains' seats. A SECOND TEXT
of the sealed `OnBytes.Road.K4.arrW` (Johnson/Road/K4/K4PlanWritten.lean): `arrW_is` ties the two.
-/
def arrW : Nat → Nat → Nat := P5T.arrOf seatsAllFull

/-- The two texts are one term. -/
theorem arrW_is : arrW = OnBytes.Road.K4.arrW := rfl

/-- The switches' seats, off the written lists. -/
def k2PadsW : List (Nat × Nat) := padSeats seatsAllFull placesW

/-- The numbers of the messages of which a switch is the first sender, off the written lists. -/
def k2NumsW : List Nat := firstNums (fun p n => switchNumIn seatsAllFull p.link n) placesW

/-- The numbers of the seats of the two other classes. -/
def otherNumsW : List Nat := (sharedSeatsW ++ lastSeatsW).map fun q => arrW q.j q.t

variable {Bk : ProverCoinCounts} {Wl : Type}

/-- **THE FORM OF A LIMB**: at each seat of the list a lot of messages bears the seat's number. -/
def MsgsOwnedAt (ml : List (MsgLot Bk Wl)) (arr : Nat → Nat → Nat) (qs : List PSeat) : Prop :=
  ∀ q ∈ qs, ∃ L ∈ ml, L.n = arr q.j q.t

/-- **THE FORM OF A LIMB**: at each seat of the list a lot of pads sits. -/
def PadsOwnedAt (pl : List (PadLot Bk Wl)) (qs : List PSeat) : Prop :=
  ∀ q ∈ qs, ∃ L ∈ pl, L.j = q.j ∧ L.t = q.t

set_option maxRecDepth 1000000 in
/-- **At the written lists**; two controls that say no. -/
theorem ownedW :
    sharedSeatsW.length = 57 ∧ k2PadsW.length = 132 ∧ lastSeatsW.length = 10 ∧
      (psFull.all fun q =>
        sharedSend q.send || k2PadsW.contains (q.j, q.t) || lastSend q.send) = true ∧
      (psFull.all fun q =>
        k2NumsW.contains (arrW q.j q.t) || otherNumsW.contains (arrW q.j q.t)) = true ∧
      (psFull.all fun q => sharedSend q.send || k2PadsW.contains (q.j, q.t)) = false ∧
      (psFull.all fun q => k2NumsW.contains (arrW q.j q.t) ||
        (sharedSeatsW.map fun q₀ => arrW q₀.j q₀.t).contains (arrW q.j q.t)) = false := by
  decide +kernel

variable {W : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}

/-- Under the head the witness's numbers are the written ones: the sealed `P5J.AtMg.arr_is`
(Johnson/LPFE1R/K10ClearAt.lean), at this file's name for the term. -/
theorem arrW_at_head (h : AtMg OnBytes.secondHashFunction W D₀ r Zp Np cF) : P5J.At.arr Zp = arrW :=
  h.arr_is

/-- THE SIX LIMBS ARE PREMISES. **THE FIELD owned OF `JoinFit`, AT THE PLAN's LIST OF THE FIRST
CHAIN's SEATS, FROM THREE SENDERS' LIMBS.** -/
theorem owned_of_three (h : AtMg OnBytes.secondHashFunction W D₀ r Zp Np cF)
    {ml : List (MsgLot Bk Wl)} {pl : List (PadLot Bk Wl)}
    (m1 : MsgsOwnedAt ml (P5J.At.arr Zp) sharedSeatsW) (p1 : PadsOwnedAt pl sharedSeatsW)
    (m2 : ∀ n ∈ k2NumsW, ∃ L ∈ ml, L.n = n)
    (p2 : ∀ s ∈ k2PadsW, ∃ L ∈ pl, L.j = s.1 ∧ L.t = s.2)
    (m3 : MsgsOwnedAt ml (P5J.At.arr Zp) lastSeatsW) (p3 : PadsOwnedAt pl lastSeatsW) :
    ∀ s ∈ P5J.At.seats Zp,
      (∃ L ∈ ml, L.n = P5J.At.arr Zp s.1 s.2) ∧ ∃ L ∈ pl, L.j = s.1 ∧ L.t = s.2 := by
  intro s hs
  rw [planSeats_at_head h] at hs
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hs
  refine ⟨?_, ?_⟩
  · show ∃ L ∈ ml, L.n = P5J.At.arr Zp q.j q.t
    have t := List.all_eq_true.1 ownedW.2.2.2.2.1 q hq
    rw [Bool.or_eq_true] at t
    rcases t with t | t
    · obtain ⟨L, hL, e⟩ := m2 _ (List.contains_iff_mem.1 t)
      exact ⟨L, hL, by rw [e, arrW_at_head h]⟩
    · obtain ⟨q₀, hq₀, e₀⟩ := List.mem_map.1 (List.contains_iff_mem.1 t)
      have e₁ : P5J.At.arr Zp q₀.j q₀.t = P5J.At.arr Zp q.j q.t := by
        rw [arrW_at_head h]
        exact e₀
      rcases List.mem_append.1 hq₀ with c | c
      · obtain ⟨L, hL, e⟩ := m1 q₀ c
        exact ⟨L, hL, e.trans e₁⟩
      · obtain ⟨L, hL, e⟩ := m3 q₀ c
        exact ⟨L, hL, e.trans e₁⟩
  · show ∃ L ∈ pl, L.j = q.j ∧ L.t = q.t
    have t := List.all_eq_true.1 ownedW.2.2.2.1 q hq
    rw [Bool.or_eq_true, Bool.or_eq_true] at t
    rcases t with (t | t) | t
    · exact p1 q (List.mem_filter.2 ⟨hq, t⟩)
    · exact p2 (q.j, q.t) (List.contains_iff_mem.1 t)
    · exact p3 q (List.mem_filter.2 ⟨hq, t⟩)

section
variable {W₀ Rc Xi Tr : Type} {bs : List (Block S ProofFile.Cl)} {front : Nat} {D : RowDataOf Xi}
  {readers : Local W₀ Rc Xi Tr → Readers} {rest : Nat → TreeLot Bk (Local W₀ Rc Xi Tr)}
  {Ot : Others Bk (Local W₀ Rc Xi Tr)}

/-- **The switches' limb on messages, where a record holds the kind's share.** -/
theorem share_nums_limb (h : AtMg OnBytes.secondHashFunction W D₀ r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hin : ShareIn (switchShareAt Bk bs front Zp Bs.G₀ D readers rest) Ot) :
    ∀ n ∈ k2NumsW, ∃ L ∈ Ot.ml, L.n = n := by
  intro n hn
  have e : ProofFile.Honest.FirstThread.nums (switchShareAt Bk bs front Zp Bs.G₀ D readers rest).ml =
      k2NumsW := by
    unfold switchShareAt k2NumsW
    rw [nums_share, places_at_head h O, switchNum_at_head h]
  rw [← e] at hn
  obtain ⟨L, hL, rfl⟩ := List.mem_map.1 hn
  exact ⟨L, hin.ml L hL, rfl⟩

/-- **The switches' limb on pads, where a record holds the kind's share.** -/
theorem share_pads_limb (h : AtMg OnBytes.secondHashFunction W D₀ r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hin : ShareIn (switchShareAt Bk bs front Zp Bs.G₀ D readers rest) Ot) :
    ∀ s ∈ k2PadsW, ∃ L ∈ Ot.pl, L.j = s.1 ∧ L.t = s.2 := by
  intro s hs
  have e : ProofFile.Honest.FirstThread.seatsOf
      (switchShareAt Bk bs front Zp Bs.G₀ D readers rest).pl = k2PadsW := by
    unfold switchShareAt k2PadsW
    rw [seats_share, places_at_head h O, pseatsAll_at_head h]
    rfl
  rw [← e] at hs
  obtain ⟨L, hL, rfl⟩ := List.mem_map.1 hs
  exact ⟨L, hin.pl L hL, rfl, rfl⟩

/-- THE FOUR LIMBS OF THE TWO OTHER SENDERS ARE PREMISES. **THE FIELD owned AT THE JOINED LISTS,
WHERE THE LIST HOLDS THE KIND's SHARE.** -/
theorem owned_at_join {Xj X : Type} (h : AtMg OnBytes.secondHashFunction W D₀ r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {wit : Local W₀ Rc Xi Tr → K1.PlaceIn Xj} {own₀ : X}
    {jobs : List (Nat × K1.SendJob (K1.PlaceIn Xj) X)}
    (hin : ShareIn (switchShareAt Bk cF.blocksInOrder front Zp Bs.G₀ D readers rest) Ot)
    (m1 : MsgsOwnedAt (joinMl cF.blocksInOrder front (P5J.At.arr Zp) wit own₀ jobs Ot) (P5J.At.arr Zp)
      sharedSeatsW)
    (p1 : PadsOwnedAt (joinPl cF.blocksInOrder jobs Ot) sharedSeatsW)
    (m3 : MsgsOwnedAt (joinMl cF.blocksInOrder front (P5J.At.arr Zp) wit own₀ jobs Ot) (P5J.At.arr Zp)
      lastSeatsW)
    (p3 : PadsOwnedAt (joinPl cF.blocksInOrder jobs Ot) lastSeatsW) :
    ∀ s ∈ P5J.At.seats Zp,
      (∃ L ∈ joinMl cF.blocksInOrder front (P5J.At.arr Zp) wit own₀ jobs Ot,
          L.n = P5J.At.arr Zp s.1 s.2) ∧
        ∃ L ∈ joinPl cF.blocksInOrder jobs Ot, L.j = s.1 ∧ L.t = s.2 :=
  owned_of_three h m1 p1
    (fun n hn => by
      obtain ⟨L, hL, e⟩ := share_nums_limb h O hin n hn
      exact ⟨L, List.mem_append.2 (Or.inr hL), e⟩)
    (fun s hs => by
      obtain ⟨L, hL, e⟩ := share_pads_limb h O hin s hs
      exact ⟨L, List.mem_append.2 (Or.inr hL), e⟩)
    m3 p3

end

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.sharedSend
#print axioms ProofFile.Honest.K2.Law.lastSend
#print axioms ProofFile.Honest.K2.Law.sharedSeatsW
#print axioms ProofFile.Honest.K2.Law.lastSeatsW
#print axioms ProofFile.Honest.K2.Law.arrW
#print axioms ProofFile.Honest.K2.Law.arrW_is
#print axioms ProofFile.Honest.K2.Law.k2PadsW
#print axioms ProofFile.Honest.K2.Law.k2NumsW
#print axioms ProofFile.Honest.K2.Law.otherNumsW
#print axioms ProofFile.Honest.K2.Law.MsgsOwnedAt
#print axioms ProofFile.Honest.K2.Law.PadsOwnedAt
#print axioms ProofFile.Honest.K2.Law.ownedW
#print axioms ProofFile.Honest.K2.Law.arrW_at_head
#print axioms ProofFile.Honest.K2.Law.owned_of_three
#print axioms ProofFile.Honest.K2.Law.share_nums_limb
#print axioms ProofFile.Honest.K2.Law.share_pads_limb
#print axioms ProofFile.Honest.K2.Law.owned_at_join
