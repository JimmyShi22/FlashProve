-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03MaskLeanAt.lean: THE KIND "LOOKUP" (K3): THE NAMED PREMISE K03MaskAt
(Johnson/P5J/K03ObjInAt.lean) PAID FROM FEWER PREMISES: THE HEAD, THE FACTS ALONG THE FOLD IN FRONT,
AND THE ONE CLOSED TEST maskC A SEGMENT. One definition with code; theorems. WHY A SECOND PAYER.
Johnson/P5J/K03MaskSeatAt.lean's `k03_maskAt` is one call of `hmask_mgAll`
(Johnson/Desc/Sound/MgAt/K3CallsPaid.lean), which goes through `MaskOkCalls` and so asks 0 < y.ns,
hB, hsome, h6 and the fold's fact on shapes besides. What `maskSeat` reads needs none of these.

  `maskSeat_at` (ON ONE STATE; general letters; at a place's link): the lookup's files'
    `maskOkCalls_at`'s own road (Johnson/Desc/First/Look/K3CallsMaskOk.lean) cut down to what
    `maskSeat` reads: from the live request's shape, groups, link, "next" and own numbers, `bookAt`,
    `atFirstSeats` and the test `maskTestsB`: the mask row's message has a seat among own. It
    names no border and no sub-protocol: it may serve at any state that meets its premises.
  `callsSentFrontB`, `callsSentFront`, `callsSentFront_control`: a closed fact on the table, by the
    kernel: "frame.sentIs" l is open IN FRONT of the calls' place of every one of the 25 segments;
    segment 0's item is not open in front of segment 1's calls.
  `k03_maskAt_lean`: the head · the filling · FoldFacts · l < 25 · lookAt's place y · `h.maskC L y l
    = true` give `K03MaskAt h l q b'`.
THE ROAD SPENDS NO PROMISE BEHIND THE ACCEPT: in front: shape, groups, seats from the fold's facts;
the frame's link, "next" and own numbers from "frame.sentIs" in the promise in front; the book's
clause from that promise. Carried over the accept by SameBut (off the accept itself:
`k3_calls_sameBut`); the book's clause at the next border by `bookAt_step`
(Johnson/Desc/First/BookFit.lean): the lookup tells no tree.
Limits. FoldFacts and maskC are premises here. At OnBytes.secondHashFunction. The full size alone. Nothing on
soundness.

-/
import Johnson.P5J.K03MaskSeatAt
import Johnson.P5J.K03PubAt
import Johnson.Desc.First.Look.K3CallsMaskOkAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.Params
open VerifiableInference.Desc.K9 (segAt? seatAt maskSeat maskAt)
open VerifiableInference.Desc.K9L (maskOracle)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Numbers bookAt pubSets moreItem)
open VerifiableInference.Desc.First.FillSent (sentName)
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.First.Att.P (oracleOfMsg maskOracle_mask maskMsg seat_mask)

set_option maxHeartbeats 2000000 in
/-- **The mask row's seat is there: on one state.** -/
theorem maskSeat_at (x : Desc.First.Look.Place) {s : Desc.First.S} {D : Sent} {nos : Array ℕ}
    {N : Numbers} {p : Option Desc.Place} {Ld : Desc.K12.Door.Laid} {M : List OracleShape}
    {own : List (ℕ × ℕ)} (seatN : ℕ → ℕ × ℕ) (hshape : s.live.frame.shape = D.shape)
    (hgroups : s.live.frame.groups = reqGroups s.live.frame.shape)
    (hlink : s.live.frame.link = x.link) (hnext : s.live.frame.next = .laterOrClose)
    (hown : s.live.frame.own = nos) (hbook : bookAt N p s = true)
    (hseats : Desc.K12.Door.atFirstSeats Ld s = true)
    (hTests : maskTestsB (maskMsg D x.link) (Desc.First.Look.keptAt D x.link).length nos N p Ld M
      own seatN = true) :
    ∀ a, segAt? s = some a → (maskSeat own a).isSome = true := by
  intro a ha
  obtain ⟨hL, -, -, ebk⟩ := segAt_parts ha
  obtain ⟨kM, o, hkM, hle, hno, hlt, hpl, hin, -⟩ := maskTests_yes hTests
  rw [live_of_link hL] at hshape hgroups hlink hnext hown
  have hfr := frameIs_of hshape hgroups hlink hnext
  have horc : oracleOfMsg a.L.check.frame (Desc.First.Look.keptAt D x.link).length kM = some o := by
    unfold oracleOfMsg
    rw [if_neg (by omega), hown]
    exact hno
  obtain ⟨-, -, -, hw⟩ := maskOracle_mask hfr (seat_mask hkM 0)
  have e1 : maskAt a.L.check.frame = some o := hw.trans horc
  have hs : seatAt own a.d.book o = some (seatN kM) := by
    rw [ebk]
    exact seatAt_of (book_place hbook hseats hlt hpl) hin
  unfold VerifiableInference.Desc.K9.maskSeat
  rw [e1]
  show (seatAt own a.d.book o).isSome = true
  rw [hs]
  rfl

local notation "PS" => Desc.First.flatPlacesOf linksFull true

/-- In front of the calls' place of segment l "frame.sentIs" l is open. -/
def callsSentFrontB (l : ℕ) : Bool :=
  ((pubSets mgMore linksFull PS)[k3K l false]?.getD []).contains (moreItem (sentName l))

set_option maxRecDepth 1000000 in
theorem callsSentFront : (List.range 25).all callsSentFrontB = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **A negative test**: in front of the calls' place of segment 1, segment 0's item is not open. -/
theorem callsSentFront_control :
    ((pubSets mgMore linksFull PS)[k3K 1 false]?.getD []).contains (moreItem (sentName 0)) =
      false := by decide +kernel

end VerifiableInference.OnPublicFiles

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (FoldFacts moreItem pubSets)
open VerifiableInference.Desc.First.FillSent (sentName five_of_sentIs)
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.K12.Door (Laid msgsOfChain)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place} {L : Laid}

local notation "PS" => VerifiableInference.Desc.First.flatPlacesOf linksFull true

set_option maxHeartbeats 4000000 in
/-- **K03MaskAt, PAID FROM FEWER PREMISES.** -/
theorem k03_maskAt_lean (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (F : FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF L) At.reqW At.links At.ps)
    {l : ℕ} (hl : l < 25) {y : VerifiableInference.Desc.First.Look.Place}
    (hlook : lookAt (At.X Zp) l false = some y) (hT : h.maskC L y l = true) :
    ∀ q, (h.toAtMg.row 𝔏)[k3K l false]? = some q →
    ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l false = some b' →
    K03MaskAt h l q b' := by
  intro q hq b' hb' B' hB' z u v hu hr hf hy c hc
  have K := k03_pieces_at h.toAtMg 𝔏 q₁ q₂ q₃
  obtain ⟨hpcX, -⟩ := K3Lot.k03_place K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp)
    Zp.first.codes Zp.first.shape l false b' hb'
  have e : placeAt (At.X Zp) l false = some (VerifiableInference.Desc.First.Look.P.ofPlace
      (Params.settingOf (At.X Zp).P.frame) false y) := by
    unfold placeAt
    rw [hlook]
    rfl
  obtain ⟨piece, laid, before, guests, rs, cols, -, hd⟩ :=
    seat_yes K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) Zp.first.codes Zp.first.shape hb'
      (K.planOk l hl false b' hb') rfl hpcX e (K.back l hl false q hq) B' hB' u v hy
  have hsb := k3_calls_sameBut K3Lot.ofForm piece laid before _ guests u.1 v.1 rs cols hd
  have ey : y.link = l := lookAt_link hlook
  obtain ⟨hLv, -, -, -⟩ := segAt_parts hc
  have hLu : u.1.link? = some c.L := hsb.link.symm.trans hLv
  have eLive : v.1.live = u.1.live := by
    rw [live_of_link hLv, live_of_link hLu]
  have hmem : moreItem (sentName l) ∈
      (pubSets (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).more linksFull PS)[k3K l false]?.getD [] := by
    rw [mgAll_more_closed (h.toAtMg.𝔇 h.𝔇) mgBase rfl]
    have h0 := List.all_eq_true.1 callsSentFront l (List.mem_range.2 hl)
    unfold callsSentFrontB at h0
    simpa using h0
  have hsent := pubSent_mgAll (h.toAtMg.𝔇 h.𝔇) mgBase l z u.1
    (onQ_front hu hf _ (List.mem_append_left _ hmem))
  obtain ⟨fnext, flink, -, fown, -⟩ := five_of_sentIs hLu hsent
  have hk : k3K l false < (PS).length :=
    (List.getElem?_eq_some_iff.1 (K3Lot.k03_at_full l hl false)).1
  have hbook := VerifiableInference.Desc.First.bookAt_step (h.toAtMg.𝔇 h.𝔇).N PS (At.told cF)
    (k03_book_at Zp cF) (k3K l false) hk (k03_tells_at h.toAtMg l hl false) u.1 v.1 hsb.book
    (by rw [hsb.st]) (onQ_book hu hf)
  refine maskSeat_at y (D := (h.toAtMg.𝔇 h.𝔇).sent) ((h.toAtMg.𝔇 h.𝔇).seat3 y.link false)
    ?_ ?_ ?_ ?_ ?_ hbook ?_ hT c hc
  · rw [eLive]
    exact k03_hLive h F (k3K l false) z u hr hf
  · rw [eLive]
    exact k03_hGroups h F (k3K l false) z u hr hf
  · rw [live_of_link hLv, ey]
    exact flink
  · rw [live_of_link hLv]
    exact fnext
  · rw [live_of_link hLv, ey]
    exact fown
  · have h0 := k03_hSeats h F (k3K l false) z u hr hf
    unfold VerifiableInference.Desc.K12.Door.atFirstSeats at h0 ⊢
    rw [hsb.book]
    exact h0

end P5J

#print axioms VerifiableInference.OnPublicFiles.maskSeat_at
#print axioms VerifiableInference.OnPublicFiles.callsSentFront
#print axioms VerifiableInference.OnPublicFiles.callsSentFront_control
#print axioms P5J.k03_maskAt_lean
