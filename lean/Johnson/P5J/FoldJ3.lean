-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/FoldJ3.lean: THE JOIN OF FoldFacts, PIECE J3: THE VALUE OF THE STRUCTURE THAT ANOTHER
FILE HAS BUILT (Johnson/IMR/AtReachFits.lean:
foldFacts_of_rest: twenty-four of the 26 fields as terms, at its own FoldData, list of segments and
list of places) CARRIED TO THE HEAD's CLOSED TERM `At.foldD Zp cF L` (Johnson/P5J/FoldAt.lean),
`At.reqW`, `At.links` AND `At.ps`. ONE CALL AND ONE EQUATION OF DATA. A JOINING: IT PAYS NOTHING OF
ITS OWN. NO BLOCK IMPORTS THIS FILE.

  (a) linksW_at · placesW_at · toldOf_at · ps_full   the written lists of IM and At and "what each
                     sub-protocol tells" are one
  (b) At.N₀ · N₀_told   the table's numbers in front of withTold; with IM.placesW and toldOf
                     laid they are At.N Zp cF
      At.foldW · foldW_is   **the equation of data**: AtReachFits.lean's FoldData at N := At.N₀,
                     built := the plan's built segments, free0 | fvs := At.foldD's own (free letters
                     there) IS At.foldD Zp cF L
  (c) SendsB · sends_at · sendsB_of_madeRow   the one public test that stays named: the planner's
                     sendings are the written places' own, at whatever blank ground the public part
                     gives (the opening's ground is bound inside the head); it follows from
                     PlanWritten.madeRow Zp = true
  (d) foldFacts_of_room   **the value at the head's closed term**, GENERAL IN X, Rch AND at_, under
                     hRch ("what is reached is reached by the wrapped sub-protocols' steps"), from
                     room and roomEarly as premises in the fields' own types
      foldFacts_at_head   the same in the head's binders: Rch over the seated description's own
                     types, hR : Rch gives RchAt, at_ := fun a => a.1
      atMgR_of       so the head with the facts on every reached state

AT o := OnBytes.secondHashFunction: the payers stand at the opening at that letter alone.
Premises that stay, beside the head h: hl (the list of seats is laid) · hB : SendsB Zp · room ·
roomEarly · for atMgR_of: hs.
Limits. Nothing is shown met here: NO MEMBER. At Rch := never every field is free. No soundness
statement.

-/
import Johnson.P5J.AtMgR
import Johnson.P5J.RchIsReach
import Johnson.IMR.AtReachFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open OnBytes.Maker (WholeD)
open Johnson.Desc.First.Walk.Tied (Reach RchAt)

/-! ### (a) The written lists are one -/

theorem linksW_at : IM.linksW = At.links := by decide

theorem placesW_at : IM.placesW = At.ps := by
  show flatPlacesOf IM.linksW true = flatPlacesOf At.links true
  rw [linksW_at]

theorem ps_full : At.ps = flatPlacesOf Sound.linksFull true := rfl

theorem toldOf_at (cF : Chain TS ProofFile.Cl) : Meaning.Carry.toldOf cF.blocksInOrder = At.told cF :=
  (At.told_is cF).symm

/-! ### (b) AtReachFits.lean's FoldData is the head's closed term -/

/-- The table's numbers in front of withTold. -/
def At.N₀ (Zp : ProofFile.Pub) (cF : Chain TS ProofFile.Cl) : Numbers :=
  (P5T.numbersOf (At.pseats Zp)).withRows (At.shape Zp) (possAt cF.blocksInOrder At.links.length)
    At.links.length

theorem N₀_told (Zp : ProofFile.Pub) (cF : Chain TS ProofFile.Cl) :
    (At.N₀ Zp cF).withTold IM.placesW (Meaning.Carry.toldOf cF.blocksInOrder) = At.N Zp cF := by
  rw [placesW_at, toldOf_at]
  rfl

/-- AtReachFits.lean's FoldData, at the head's letters where it has free ones. -/
def At.foldW (Zp : ProofFile.Pub) (cF : Chain TS ProofFile.Cl) (L : K12.Door.Laid) : FoldData :=
  { ft := 0, sent := Meaning.K2.sentAt Zp, groupAt := fun m => m,
    ownAt := FillSent.ownAt Zp.first.shape
      ((At.N₀ Zp cF).withTold IM.placesW (Meaning.Carry.toldOf cF.blocksInOrder))
      IM.linksW IM.placesW Zp.made.p.built.links,
    keptAt := FillSent.keptAt Zp.first.shape
      ((At.N₀ Zp cF).withTold IM.placesW (Meaning.Carry.toldOf cF.blocksInOrder))
      IM.linksW IM.placesW Zp.made.p.built.links,
    L := L, M := K12.Door.msgsOfChain Zp.made.proof.1, free0 := (At.foldD Zp cF L).free0,
    fvs := (At.foldD Zp cF L).fvs }

/-- **It is the head's closed term.** -/
theorem foldW_is (Zp : ProofFile.Pub) (cF : Chain TS ProofFile.Cl) (L : K12.Door.Laid) :
    At.foldW Zp cF L = At.foldD Zp cF L := by
  unfold At.foldW
  rw [N₀_told, linksW_at, placesW_at]
  rfl

/-- The planner's sendings of the first chain are the written places' own, at whatever blank ground
the public part gives. -/
def SendsB (Zp : ProofFile.Pub) : Prop :=
  ∀ G₀, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀ →
    K12.Door.sendsAreB Zp.made.proof.1 358 (K12.Door.snAt Zp G₀ At.ps) = true

theorem sends_at {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    {Zp : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)} {cF : Chain TS ProofFile.Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (O : IM.Open o pol lay KL F Zp Bs base cF A B)
    (hB : SendsB Zp) :
    K12.Door.sendsAreB Zp.made.proof.1 358 (K12.Door.snAt Zp Bs.G₀ IM.placesW) = true := by
  rw [placesW_at]
  exact hB _ O.blank

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF)

include h in
/-- SendsB follows from the row on the made plan. -/
theorem sendsB_of_madeRow (hy : VerifiableInference.PlanWritten.madeRow Zp = true) :
    SendsB Zp := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  intro G₀ hG
  obtain rfl : Bs.G₀ = G₀ := Option.some.inj (O.blank.symm.trans hG)
  rw [← placesW_at]
  exact Meaning.K2.sendsAre_of_madeRow h.scope h.reads O h.laid.planOk hy

/-! ### (d) The value of the structure -/

section Value
variable {X : Type} (Rch : ℕ → X → Prop) (at_ : X → ProofFile.InstPub × TS)
  (hRch : ∀ k a, Rch k a → Reach 0 (cF.blocksInOrder.map Sound.below) (ProofFile.startS Zp) k (at_ a))

include h hRch in
/-- **FoldFacts at the head's closed term**: one call and the equation of data. -/
theorem foldFacts_of_room {L : K12.Door.Laid} (hl : At.laid? Zp = some L) (hB : SendsB Zp)
    (room' : ∀ k a p m, Rch k a → (at_ a).2.failed = none → At.ps[k]? = some p →
      p.link = some m → 2 ≤ p.piece → Johnson.Desc.First.Walk.Tied.roomIsB (At.foldD Zp cF L).free0
        (At.foldD Zp cF L).fvs m (at_ a).2 = true)
    (roomEarly' : ∀ k a p m, Rch k a → (at_ a).2.failed = none → At.ps[k]? = some p →
      p.link = some m → p.piece < 2 → 0 < m → Johnson.Desc.First.Walk.Tied.roomIsB
        (At.foldD Zp cF L).free0 (At.foldD Zp cF L).fvs m (at_ a).2 = true) :
    FoldFacts Rch at_ (At.foldD Zp cF L) At.reqW At.links At.ps := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have F : FoldFacts Rch at_ (At.foldW Zp cF L) At.reqW IM.linksW IM.placesW :=
    Meaning.K2.foldFacts_of_rest h.scope h.reads O h.laid.planOk Rch at_ hRch (At.N₀ Zp cF)
      Zp.made.p.built.links (sends_at O hB) hl h.laid.value (At.foldD Zp cF L).free0
      (At.foldD Zp cF L).fvs
      (fun k a p m hr hm hp => room' k a p m hr hm (by rw [ps_full]; exact hp))
      (fun k a p m hr hm hp => roomEarly' k a p m hr hm (by rw [ps_full]; exact hp))
  rw [foldW_is, linksW_at, placesW_at] at F
  exact F

end Value

section Head
variable {Str : Type}
  (Rch : ℕ → ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) × Str → Prop)
  (hR : ∀ k a, Rch k a → RchAt (F0T OnBytes.secondHashFunction Zp Np cF) k a)

/-- The head's reader of a statement: its public part and the verifier's state. -/
abbrev At.at1 (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl) (Str : Type) :
    ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) × Str →
      ProofFile.InstPub × TS := fun a => a.1

include h hR in
/-- **In the head's binders.** -/
theorem foldFacts_at_head {L : K12.Door.Laid} (hl : At.laid? Zp = some L) (hB : SendsB Zp)
    (room' : ∀ k a p m, Rch k a → (At.at1 Zp Np cF Str a).2.failed = none → At.ps[k]? = some p →
      p.link = some m → 2 ≤ p.piece → Johnson.Desc.First.Walk.Tied.roomIsB (At.foldD Zp cF L).free0
        (At.foldD Zp cF L).fvs m (At.at1 Zp Np cF Str a).2 = true)
    (roomEarly' : ∀ k a p m, Rch k a → (At.at1 Zp Np cF Str a).2.failed = none →
      At.ps[k]? = some p → p.link = some m → p.piece < 2 → 0 < m →
      Johnson.Desc.First.Walk.Tied.roomIsB (At.foldD Zp cF L).free0 (At.foldD Zp cF L).fvs m
        (At.at1 Zp Np cF Str a).2 = true) :
    FoldFacts Rch (fun a => a.1) (At.foldD Zp cF L) At.reqW At.links At.ps :=
  foldFacts_of_room h Rch (At.at1 Zp Np cF Str) (hRch_at OnBytes.secondHashFunction Zp Np cF Rch hR) hl hB
    room' roomEarly'

include h hR in
/-- **The head with the facts on every reached state.** -/
theorem atMgR_of {L : K12.Door.Laid} (hl : At.laid? Zp = some L)
    (hs : FillP1.startB Zp (K12.Door.msgsOfChain Zp.made.proof.1) (At.N Zp cF).indexNo = true)
    (hB : SendsB Zp)
    (room' : ∀ k a p m, Rch k a → (At.at1 Zp Np cF Str a).2.failed = none → At.ps[k]? = some p →
      p.link = some m → 2 ≤ p.piece → Johnson.Desc.First.Walk.Tied.roomIsB (At.foldD Zp cF L).free0
        (At.foldD Zp cF L).fvs m (At.at1 Zp Np cF Str a).2 = true)
    (roomEarly' : ∀ k a p m, Rch k a → (At.at1 Zp Np cF Str a).2.failed = none →
      At.ps[k]? = some p → p.link = some m → p.piece < 2 → 0 < m →
      Johnson.Desc.First.Walk.Tied.roomIsB (At.foldD Zp cF L).free0 (At.foldD Zp cF L).fvs m
        (At.at1 Zp Np cF Str a).2 = true) :
    AtMgR OnBytes.secondHashFunction Z D r Zp Np cF Rch (fun a => a.1) L :=
  { h with listed := hl, start := hs, fold := foldFacts_at_head h Rch hR hl hB room' roomEarly' }

end Head

end P5J

#print axioms P5J.linksW_at
#print axioms P5J.placesW_at
#print axioms P5J.toldOf_at
#print axioms P5J.N₀_told
#print axioms P5J.foldW_is
#print axioms P5J.sends_at
#print axioms P5J.sendsB_of_madeRow
#print axioms P5J.foldFacts_of_room
#print axioms P5J.foldFacts_at_head
#print axioms P5J.atMgR_of
