-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K03Due4.lean: the kind "lookup" (K3): WHAT IS STILL DUE FOR THE KIND's NAMED CONDITION
AT THE CLOSED CONSTANT, FOURTH COUNT: `k03_cond_due4` : `h.K3Cond 𝔏`
(Johnson/Goal/Skeleton/Kinds/K3Bridge.lean), by one call of `k03_cond_due3`
(Johnson/P5J/K03Due3.lean, which does not turn). FROM the head, q₁ q₂ q₃ and:
  TESTS WITH CODE ON PUBLIC DATA: oneC l (l < 24) · tie at the 24 calls' places ·
    `ObjEndR` at the 25 calls' places (hB · hTests · h6) · `DigTestsR` at the 25 digits' places
    (hB · hTests · h6);
  WHERE A PIECE ACCEPTS:
    Hc: behind the lookup on the calls at l < 24 the item formsInT l 2 "objects" holds;
    hObj: the like at the head's calls (formsInT 24 3 "objects");
    Fd: `DigFormsR`: the forms of other runs across an accept of the digits' piece (25);
    Rd: rides at the 25 digits' places;
    Hm: `HeadEndR`: the head's model.

PAID HERE BEYOND `k03_cond_due3`: the facts on every reached state, `First.FoldFacts`, FROM THE HEAD
ALONE (`atMgR_rch_of_head`: Johnson/P5J/StartAtHead.lean, over other files' joinings) · digRow,
headRow, fenceFit, padsAtZ, offC FROM THE HEAD ALONE (Johnson/P5J/K03TestsAt.lean: the tests have
moved into the head) · namedC likewise (Johnson/P5J/K03NamedHead.lean: a share of the head's own
field) · othersPub at the 24 calls, from Hc (Johnson/P5J/K03OthersPubAt.lean) ·
othersPub at the 25 digits, from Fd (Johnson/P5J/K03DigOthersAt.lean).

Limits: all of the above are premises; no member is known. At secondHashFunction alone. Nothing on soundness by
itself; nothing on hiding.


-/
import Johnson.P5J.K03Due3
import Johnson.P5J.K03OthersPubAt
import Johnson.P5J.K03DigOthersAt
import Johnson.P5J.K03TestsAt
import Johnson.P5J.StartAtHead
import Johnson.P5J.K03NamedHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open Inst.Model Inst.Model.All
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look.Stored (oWc wOfC msgWc smpWc strWc)
open VerifiableInference.Desc.First (ModelPart Item Pub Part Meaning Numbers openSets pubSets start
  sampledIn pubFit shift sameStand bookFit pubStep pubRowM stepOpen pubOfItems)
open OnBytes.Road.Rows (Bare)
open VerifiableInference.Desc (Link)
open VerifiableInference.Desc.K9 (segAt? readersOfLink statesOfLink LinkHoles)
open _root_.Meaning (linkTieB BaseSegF seatBy fLay hidAtF ReadsOne sizesFit)

open VerifiableInference.Desc.First (moreItem)
open VerifiableInference.Desc.First.FillSent (sentIsB sentName)
open VerifiableInference.Desc.First.Att.P (maskMsg)

local notation "PS" => Desc.First.flatPlacesOf linksFull true

open Cb.Fo.Pin

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
  (Dm : MgData Xi P Tok rows cols nR X) (l : ℕ) (x : Desc.First.Look.Place)

/-- **The three tests at a segment's digits.** -/
structure DigTestsR (nos : Array ℕ) (Ld : Desc.K12.Door.Laid) (M : List OracleShape) : Prop where
  hB : maskB Dm.sent (digList x Dm.sent Dm.l3.rad) x.link x.arrays.ns = true
  hTests : maskTestsB (maskOwnIx Dm.sent x.link) 0 nos Dm.N PS[k3K l true + 1]? Ld M
    (Dm.N.group l) (Dm.l3.seat x.link true) = true
  h6 : oneShapeB Dm.ms = true

end

end VerifiableInference.OnPublicFiles

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open Inst.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (attAt layAt digAt lookAt tlAt idxAt)
open VerifiableInference.Desc.K12.Door (msgsOfChain)
open _root_.Meaning (linkTieB)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a)
  (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

local notation "PS" => VerifiableInference.Desc.First.flatPlacesOf linksFull true

set_option maxHeartbeats 4000000 in
/-- **WHAT IS STILL DUE, FOURTH COUNT.** -/
theorem k03_cond_due4 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (s₀ : VerifiableInference.Desc.First.S) (z₀ : ProofFile.InstPub)
    (hOne : ∀ l < 24, h.oneC l = true)
    (Ta : ∀ l < 25, ∀ y A tl, attAt (At.X Zp) l = some (y, A, tl) →
      linkTieB (At.X Zp) (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).rad3 (At.num Zp)
        (idxAt (At.sentAt Zp) (At.num Zp) l) y.link tl = true)
    (Tl : ∀ l < 25, ∀ y tl, layAt (At.X Zp) l = some y → tlAt (At.X Zp) l = some tl →
      linkTieB (At.X Zp) (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).rad3 (At.num Zp)
        (idxAt (At.sentAt Zp) (At.num Zp) l) y.link tl = true)
    (Oc : ∀ L, At.laid? Zp = some L → ∀ l < 25, ∀ y, lookAt (At.X Zp) l false = some y →
      ObjEndR (h.toAtMg.𝔇 h.𝔇) (k3K l false) l y L (msgsOfChain Zp.made.proof.1))
    (Td : ∀ L, At.laid? Zp = some L → ∀ l < 25, ∀ y tl, digAt (At.X Zp) l = some (y, tl) →
      DigTestsR (h.toAtMg.𝔇 h.𝔇) l y ((At.foldD Zp cF L).ownAt l 3) L
        (msgsOfChain Zp.made.proof.1))
    (Hc : ∀ l < 24, ∀ q, (h.toAtMg.row 𝔏)[k3K l false]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l false = some b' →
      ∀ B', SeatOf b' B' → ∀ (z : ProofFile.InstPub)
        (u v : VerifiableInference.Desc.First.S × (FrD).E.Str),
        onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
          (k3K l false) u →
        h.toAtMg.rch (k3K l false) ((z, u.1), u.2) → u.1.failed = none →
        (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
        (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).pub (.formsInT l 2 "objects") (z, v.1) = true)
    (hObj : ∀ q, (h.toAtMg.row 𝔏)[k3K 24 false]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape 24 false = some b' →
      ∀ B', SeatOf b' B' → ∀ (z : ProofFile.InstPub) u τ v, (strictAt B' q).ior.red.out u τ = some v →
        SameBut u.1 v.1 →
        onQ (Fr := FrD) (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS
          (fun s => (z, s)) (k3K 24 false) u →
        h.toAtMg.rch (k3K 24 false) ((z, u.1), u.2) → u.1.failed = none →
        (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).pub (.formsInT 24 3 "objects") (z, v.1) = true)
    (Fd : ∀ l < 25, ∀ sub, linksFull[l]? = some sub →
      ∀ q, (h.toAtMg.row 𝔏)[k3K l true]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l true = some b' →
        DigFormsR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch l sub q b')
    (Rd : ∀ l < 25, ∀ q, (h.toAtMg.row 𝔏)[k3K l true]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l true = some b' →
        RidesAtR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) h.toAtMg.rch
          (k3K l true) q b')
    (Hm : ∀ q, (h.toAtMg.row 𝔏)[k3K 24 false]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape 24 false = some b' →
        HeadEndR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch K3Lot.ofForm (At.seats Zp) s₀ x
          q b' ((h.toAtMg.𝔇 h.𝔇).sent.arrayOf.getD 24 #[]) (IM.k3Place 24 false)
          (MgAt.nextOf 24 false) (At.told cF)) :
    h.K3Cond 𝔏 := by
  obtain ⟨L, R⟩ := atMgR_rch_of_head h
  refine k03_cond_due3 h 𝔏 q₁ q₂ q₃ s₀ z₀ L R.fold (k03_digRow_at h.toAtMg)
    (k03_headRow_at h.toAtMg) (k03_fence_at h.toAtMg) (k03_pads_at h.toAtMg).2 hOne
    (fun l hl => h.namedC_head (by omega))
    (k03_offC_at h.toAtMg) ?_ (Oc L R.listed) Hm hObj ?_ ?_
  · intro l hl y tl hy q hq b' hb'
    obtain ⟨sub, hsub⟩ : ∃ sub, linksFull[l]? = some sub := by
      interval_cases l <;> exact ⟨_, rfl⟩
    have T := Td L R.listed l hl y tl hy
    exact ⟨k03_othersPub_dig h 𝔏 q₁ q₂ q₃ hl hsub hy q hq b' hb' (Fd l hl sub hsub q hq b' hb'),
      Rd l hl q hq b' hb', T.hB, T.hTests, T.h6⟩
  · intro l hl y A tl hy q hq b' hb'
    have h24 : l < 24 := by have := attAt_odd hy; omega
    exact ⟨Ta l hl y A tl hy,
      k03_othersPub_att h 𝔏 q₁ q₂ q₃ l hl y A tl hy q hq b' hb' (Hc l h24 q hq b' hb')⟩
  · intro l hl y tl hy ht q hq b' hb'
    exact ⟨Tl l hl y tl hy ht,
      k03_othersPub_lay h 𝔏 q₁ q₂ q₃ l hl y hy q hq b' hb'
        (Hc l (k03_lay_lt h hl hy) q hq b' hb')⟩

end P5J

#print axioms P5J.k03_cond_due4
