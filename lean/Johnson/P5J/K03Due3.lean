-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K03Due3.lean: the kind "lookup" (K3): WHAT IS STILL DUE FOR THE KIND's NAMED CONDITION
AT THE CLOSED CONSTANT, THIRD COUNT: `k03_cond_due3` : `h.K3Cond 𝔏`
(Johnson/Goal/Skeleton/Kinds/K3Bridge.lean), by one call of `k03_cond_due2`
(Johnson/P5J/K03Due2.lean, which does not turn). FROM the head, q₁ q₂ q₃ and:
  ONE CONDITION ON EVERY REACHED STATE: F : `First.FoldFacts` (the field fold of the head `AtMgR`);
  SEVEN TESTS WITH CODE: digRow · headRow · fenceFit · padsAtZ · oneC l, namedC l (l < 24) · offC;
  AT THE 25 CALLS' PLACES: `ObjEndR`: THREE MORE TESTS (hB · hTests · h6);
  AT THE 24 CALLS' PLACES IN FRONT OF THE HEAD's: `CallsEndR` (tie: a test · othersPub);
  AT THE 25 DIGITS' PLACES: `DigEndR` (othersPub · rides · three tests: hB · hTests · h6);
  AT THE HEAD's CALLS: `HeadEndR` (model) and hObj ("formsInT 24 3 objects" holds behind an accept).

PAID HERE BEYOND `k03_cond_due2`: othersP at all fifty (Johnson/P5J/K03OthersPAt.lean) · rides at
the 25 calls' places (Johnson/P5J/K03RidesAt.lean) · hBare at the 25 calls' places
(Johnson/P5J/K03BareAt.lean) · the head's parts (Johnson/P5J/K03HeadPartsAt.lean, under hObj). arrs
is closed: the head's segment's list of arrays.

AND `k03_cond_due3_start`: THE SAME WITHOUT F: `First.FoldFacts` at `h.toAtMg.rch` is had from the
head and ONE MORE CLOSED TEST, startB (`atMgR_rch_at_head`: Johnson/P5J/AtMgRAtHead.lean, over other
files' joinings of the 26 fields); the premises that read L are asked at the L that `At.laid? Zp`
returns.

SO WHAT IS LEFT OVER WITNESSES AND ACCEPTS: othersPub at 49 places · rides at the 25 digits' places
· model and hObj at the head.

Limits: all of the above are premises; no member is known. At secondHashFunction alone. Nothing on soundness by
itself; nothing on hiding.


-/
import Johnson.P5J.K03Due2
import Johnson.P5J.K03End
import Johnson.P5J.K03OthersPAt
import Johnson.P5J.K03RidesAt
import Johnson.P5J.K03BareAt
import Johnson.P5J.K03HeadPartsAt
import Johnson.P5J.AtMgRAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open Inst.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (attAt layAt digAt lookAt tlAt idxAt)
open VerifiableInference.Desc.Kinds.Head.Law (OffPad.padsAtZ)
open VerifiableInference.Desc.K12.Door (msgsOfChain)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a)
  (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

local notation "PS" => VerifiableInference.Desc.First.flatPlacesOf linksFull true

set_option maxHeartbeats 4000000 in
/-- **WHAT IS STILL DUE, THIRD COUNT.** -/
theorem k03_cond_due3 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (s₀ : VerifiableInference.Desc.First.S) (z₀ : ProofFile.InstPub)
    (L : VerifiableInference.Desc.K12.Door.Laid)
    (F : VerifiableInference.Desc.First.FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF L)
      At.reqW At.links At.ps)
    (hDig : VerifiableInference.Desc.K3Asks.digRow (At.X Zp)
      (VerifiableInference.Desc.K3Asks.sentOf Zp) = true)
    (hRow : VerifiableInference.Desc.K3Asks.headRow (At.X Zp) = true)
    (hg : VerifiableInference.Desc.First.fenceFit (At.N Zp cF) linksFull PS = true)
    (hp : OffPad.padsAtZ Zp = true)
    (hOne : ∀ l < 24, h.oneC l = true) (hNamed : ∀ l < 24, h.namedC l = true)
    (hOff : h.toAtMg.offC = true)
    (Sd : ∀ l < 25, ∀ y tl, digAt (At.X Zp) l = some (y, tl) →
      ∀ q, (h.toAtMg.row 𝔏)[k3K l true]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l true = some b' →
        DigEndR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch l y q b'
          ((At.foldD Zp cF L).ownAt l 3) (At.nsDig Zp l) L (msgsOfChain Zp.made.proof.1))
    (Oc : ∀ l < 25, ∀ y, lookAt (At.X Zp) l false = some y →
      ObjEndR (h.toAtMg.𝔇 h.𝔇) (k3K l false) l y L (msgsOfChain Zp.made.proof.1))
    (Hm : ∀ q, (h.toAtMg.row 𝔏)[k3K 24 false]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape 24 false = some b' →
        HeadEndR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch K3Lot.ofForm (At.seats Zp) s₀ x
          q b' ((h.toAtMg.𝔇 h.𝔇).sent.arrayOf.getD 24 #[]) (IM.k3Place 24 false)
          (MgAt.nextOf 24 false) (At.told cF))
    (hObj : ∀ q, (h.toAtMg.row 𝔏)[k3K 24 false]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape 24 false = some b' →
      ∀ B', SeatOf b' B' → ∀ (z : ProofFile.InstPub) u τ v, (strictAt B' q).ior.red.out u τ = some v →
        SameBut u.1 v.1 →
        onQ (Fr := FrD) (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS
          (fun s => (z, s)) (k3K 24 false) u →
        h.toAtMg.rch (k3K 24 false) ((z, u.1), u.2) → u.1.failed = none →
        (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).pub (.formsInT 24 3 "objects") (z, v.1) = true)
    (Va : ∀ l < 25, ∀ y A tl, attAt (At.X Zp) l = some (y, A, tl) →
      ∀ q, (h.toAtMg.row 𝔏)[k3K l false]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l false = some b' →
        CallsEndR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch (At.num Zp)
          (idxAt (At.sentAt Zp) (At.num Zp) l) (IM.k3Place l false) (k3K l false) l y tl q b')
    (Vl : ∀ l < 25, ∀ y tl, layAt (At.X Zp) l = some y → tlAt (At.X Zp) l = some tl →
      ∀ q, (h.toAtMg.row 𝔏)[k3K l false]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l false = some b' →
        CallsEndR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch (At.num Zp)
          (idxAt (At.sentAt Zp) (At.num Zp) l) (IM.k3Place l false) (k3K l false) l y tl q b') :
    h.K3Cond 𝔏 := by
  have rides := k03_rides_calls h 𝔏 q₁ q₂ q₃ hg
  refine k03_cond_due2 h 𝔏 q₁ q₂ q₃ s₀ ((h.toAtMg.𝔇 h.𝔇).sent.arrayOf.getD 24 #[]) z₀ L F hDig hRow
    hg hp hOne hNamed hOff ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro l hl y tl hy q hq b' hb'
    exact digLast_of_end _ _ _ l y q b' _ _ _ _ (k03_othersP_digits h hl q b')
      (Sd l hl y tl hy q hq b' hb')
  · intro l hl y A tl hy q hq b' hb'
    have hk := k03_look_att h hl hy
    exact objLast_of_end _ _ _ _ _ _ _ _ _ _ _ (k03_hBare h 𝔏 q₁ q₂ q₃ hl hk q hq b' hb')
      (Oc l hl y hk)
  · intro l hl y hy q hq b' hb'
    have hk := k03_look_lay h hl hy
    exact objLast_of_end _ _ _ _ _ _ _ _ _ _ _ (k03_hBare h 𝔏 q₁ q₂ q₃ hl hk q hq b' hb')
      (Oc l hl y hk)
  · intro q hq b' hb'
    have hk := k03_look_head h
    exact objLast_of_end _ _ _ _ _ _ _ _ _ _ _
      (k03_hBare h 𝔏 q₁ q₂ q₃ (by omega) hk q hq b' hb') (Oc 24 (by omega) x hk)
  · intro q hq b' hb'
    exact headShort_of_end _ _ _ _ _ _ _ _ _ _ _ _ _
      (k03_head_parts_at h 𝔏 q₁ q₂ q₃ hg q hq b' hb' (hObj q hq b' hb'))
      (rides 24 (by omega) x (k03_look_head h) q hq b' hb') (Hm q hq b' hb')
  · intro l hl y A tl hy q hq b' hb'
    exact callsLast_of_end _ _ _ _ _ _ _ _ _ tl q b' (k03_othersP_calls h hl b' q)
      (rides l hl y (k03_look_att h hl hy) q hq b' hb') (Va l hl y A tl hy q hq b' hb')
  · intro l hl y tl hy ht q hq b' hb'
    exact callsLast_of_end _ _ _ _ _ _ _ _ _ tl q b' (k03_othersP_calls h hl b' q)
      (rides l hl y (k03_look_lay h hl hy) q hq b' hb') (Vl l hl y tl hy ht q hq b' hb')

/-- **THE SAME, WITH THE FACTS ON EVERY REACHED STATE PAID FROM THE HEAD AND ONE CLOSED TEST.** -/
theorem k03_cond_due3_start (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (s₀ : VerifiableInference.Desc.First.S) (z₀ : ProofFile.InstPub)
    (hs : VerifiableInference.Desc.First.FillP1.startB Zp (msgsOfChain Zp.made.proof.1)
      (At.N Zp cF).indexNo = true)
    (hDig : VerifiableInference.Desc.K3Asks.digRow (At.X Zp)
      (VerifiableInference.Desc.K3Asks.sentOf Zp) = true)
    (hRow : VerifiableInference.Desc.K3Asks.headRow (At.X Zp) = true)
    (hg : VerifiableInference.Desc.First.fenceFit (At.N Zp cF) linksFull PS = true)
    (hp : OffPad.padsAtZ Zp = true)
    (hOne : ∀ l < 24, h.oneC l = true) (hNamed : ∀ l < 24, h.namedC l = true)
    (hOff : h.toAtMg.offC = true)
    (Sd : ∀ L, At.laid? Zp = some L → ∀ l < 25, ∀ y tl, digAt (At.X Zp) l = some (y, tl) →
      ∀ q, (h.toAtMg.row 𝔏)[k3K l true]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l true = some b' →
        DigEndR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch l y q b'
          ((At.foldD Zp cF L).ownAt l 3) (At.nsDig Zp l) L (msgsOfChain Zp.made.proof.1))
    (Oc : ∀ L, At.laid? Zp = some L → ∀ l < 25, ∀ y, lookAt (At.X Zp) l false = some y →
      ObjEndR (h.toAtMg.𝔇 h.𝔇) (k3K l false) l y L (msgsOfChain Zp.made.proof.1))
    (Hm : ∀ q, (h.toAtMg.row 𝔏)[k3K 24 false]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape 24 false = some b' →
        HeadEndR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch K3Lot.ofForm (At.seats Zp) s₀ x
          q b' ((h.toAtMg.𝔇 h.𝔇).sent.arrayOf.getD 24 #[]) (IM.k3Place 24 false)
          (MgAt.nextOf 24 false) (At.told cF))
    (hObj : ∀ q, (h.toAtMg.row 𝔏)[k3K 24 false]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape 24 false = some b' →
      ∀ B', SeatOf b' B' → ∀ (z : ProofFile.InstPub) u τ v, (strictAt B' q).ior.red.out u τ = some v →
        SameBut u.1 v.1 →
        onQ (Fr := FrD) (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS
          (fun s => (z, s)) (k3K 24 false) u →
        h.toAtMg.rch (k3K 24 false) ((z, u.1), u.2) → u.1.failed = none →
        (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).pub (.formsInT 24 3 "objects") (z, v.1) = true)
    (Va : ∀ l < 25, ∀ y A tl, attAt (At.X Zp) l = some (y, A, tl) →
      ∀ q, (h.toAtMg.row 𝔏)[k3K l false]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l false = some b' →
        CallsEndR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch (At.num Zp)
          (idxAt (At.sentAt Zp) (At.num Zp) l) (IM.k3Place l false) (k3K l false) l y tl q b')
    (Vl : ∀ l < 25, ∀ y tl, layAt (At.X Zp) l = some y → tlAt (At.X Zp) l = some tl →
      ∀ q, (h.toAtMg.row 𝔏)[k3K l false]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l false = some b' →
        CallsEndR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch (At.num Zp)
          (idxAt (At.sentAt Zp) (At.num Zp) l) (IM.k3Place l false) (k3K l false) l y tl q b') :
    h.K3Cond 𝔏 := by
  obtain ⟨L, R⟩ := atMgR_rch_at_head h hs
  exact k03_cond_due3 h 𝔏 q₁ q₂ q₃ s₀ z₀ L R.fold hDig hRow hg hp hOne hNamed hOff
    (Sd L R.listed) (Oc L R.listed) Hm hObj Va Vl

end P5J

#print axioms P5J.k03_cond_due3
#print axioms P5J.k03_cond_due3_start
