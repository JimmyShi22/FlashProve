-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AT ANY FILLING: general in the prover H and the Script Q, at the head's letters; no Script is laid.
Johnson/Desc/ProofFile/Honest/K3/Term/MaskEntriesAtTheWitness.lean: the honest side of the kind
"lookup" (K3): what the state that a lookup's member leaves says of the link's mask row, read from
`ThrS` and the member's step alone, under the head `P5J.AtMgA`.

Why. The bundles' clause on the sender and the field masks of their clause on the witness both read
the mask row through the state's part a. The library's `MaskOk` and `MaskOkCalls` say what is asked
of that part. Here they are shown at the thread's state. With them the field masks hold at every
witness by the library's four dictionaries, and the six facts `ReaderAt` hold, at one number for both lookups
of a link.

  `maskSeatsAgree`, `maskSeatsAgreeWritten`, `maskSeatsAgreeAtHead`: a closed test, evaluated by the
    kernel, and its yes under the head: the mask row's message has one seat at the digits' list and
    at the calls' list.
  `maskRowMessageNumber`: the number, in the witness, of a link's mask row's message.
  `maskMemberAtLink`: its member of the table's list: seat at both lists, number, no pad.
  `maskFactsBehindDigitsAtLink`, `maskFactsBehindCallsAtPlace`: `MaskOk`, `MaskOkCalls` at the state
    behind, and the ledger's number of slots.
  `readerAtOfMaskOk`, `readerAtOfMaskOkCalls`: `ReaderAt` out of those.
  `maskOkBehindDigitsLookup`, `maskOkCallsBehindCallsLookup`: the state's debt and the room of what
    the site spends, at a site, at every Said stronger than `SaidOk`.
  `digitsMaskEntriesAtEveryWitness`, `attentionMaskEntriesAtEveryWitness`,
  `layersMaskEntriesAtEveryWitness`, `headMaskEntriesAtEveryWitness`: the field masks.
  `readerAtBehindDigitsLookup`, `readerAtBehindCallsLookup`: the six facts at a site, at one number.
  Helpers: `maskSeatsAgreeReadsTheShapeAlone`, `maskMessageOfTest`, `siteFaceIsFaceOfShape`,
  `maskSeatBearsPlanNumber`, `slotsFitLedger`, `callsPlaceHasItsShape`, `callsPlaceAtLink`.

Limits. Conditional on the head, `ThrS` and the member's step: where no thread stands these say
nothing, and no state is shown here at which `ThrS` holds. Said must imply `SaidOk`. The field masks
are the one field of four of the clause on the witness, and `ReaderAt` is the verifier's half of the
clause on the sender: nothing here says what a message holds. `maskSeatsAgreeWritten` is one
evaluation at the library's written shape and seats. The elder row. The full size alone. Nothing on
any property.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.VerifierStateBehindLookup
import Johnson.Desc.ProofFile.Honest.K5.Law.MaskRoomAtHead
import Johnson.Desc.ProofFile.Honest.K5.Law.MaskNos
import Johnson.Desc.ProofFile.Honest.Law.Rule.ReaderPays
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.OnOutMember
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.BehindPays
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeHeadAll
import Johnson.Desc.First.Look.K3DigitsMaskOk
import Johnson.Desc.First.Look.K3CallsMaskOk
import Johnson.Desc.First.Look.K3HeadObjects
import Johnson.P5J.K03Due5
import Johnson.P5J.K03MaskBAt
import Johnson.P5J.K03SeatsAt
import Johnson.P5J.K03PubHeadAt
import Johnson.P5J.K03DigPartsAt
import Johnson.P1K8R.BlindOwesAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block Chain OpenedColumn)
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart shift bookAt moreItem)
open VerifiableInference.Desc.First.FillSent (sentName five_of_sentIs)
open VerifiableInference.Desc.First.Att.P (maskMsg sentOfBuilt built_of_pub)
open VerifiableInference.Desc.K9 (segAt? seatAt)
open VerifiableInference.Desc.K9L (maskOracle)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile.Honest.FirstThread (lettersHead Script WtF)
open ProofFile.Honest.K3.Law
open ProofFile.Honest.K3.Law.AtThr
open ProofFile.Honest.K3.Law.Exchange
open ProofFile.Honest.K3.Law.Total
open P5J

/-- The test at the library's list of calls: the mask row's message has one seat at both lists. -/
def maskSeatsAgree (D : Sent) (ps : List P5T.PSeat) : Bool :=
  (List.range D.shape.link.length).all fun l =>
    match maskMsg D l with
    | none => true
    | some kM => P6T.seatCallsT ps D l kM == P6T.seatT ps l (kM - P6T.keptN D l)

/-- The test reads D at its shape alone. -/
theorem maskSeatsAgreeReadsTheShapeAlone {D D' : Sent} (e : D.shape = D'.shape) (ps : List P5T.PSeat) :
    maskSeatsAgree D ps = maskSeatsAgree D' ps := by
  unfold maskSeatsAgree P6T.seatCallsT P6T.callAt P6T.keptN Desc.First.Look.keptAt
  rw [e, P6T.isCall_congr e, P6T.maskMsg_congr e]

set_option maxRecDepth 1000000 in
/-- **At the library's written shape and seats the test accepts.** By evaluation in Lean's kernel. -/
theorem maskSeatsAgreeWritten : maskSeatsAgree P6T.sentShape P5T.psFull = true := by decide +kernel

/-- A yes of the test on the calls' mask row: the message, and its member in the list. -/
theorem maskMessageOfTest {D : Sent} {L : List (OracleShape × ℕ)} {i upTo : ℕ}
    (hB : maskCallsB D L i upTo = true) :
    ∃ m, ((messagesAt D i).findIdx? fun y => y.shape.maskRows != 0) = some m ∧
      (Desc.First.Look.keptAt D i).length + m < L.length := by
  unfold maskCallsB at hB
  split at hB
  · rename_i m hm
    split at hB
    · rename_i o ho
      exact ⟨m, hm, (List.getElem?_eq_some_iff.1 ho).1⟩
    · cases hB
  · cases hB

/-- The site's face is its shape's. -/
theorem siteFaceIsFaceOfShape {Z : Pub} {s : Site} (hs : s ∈ lookSites Z) :
    s.at_.face = VerifiableInference.Desc.K3.faceOf s.shape := by
  unfold lookSites at hs
  obtain ⟨x, _, hsx⟩ := List.mem_filterMap.1 hs
  obtain ⟨_, _, _, _, _, f6, _, _⟩ := site_facts _ _ x s hsx
  exact f6

/-- The number, in the witness, of the message that holds link l's mask row: the plan's number of
the link's own message. -/
def maskRowMessageNumber (Zp : ProofFile.Pub) (l : ℕ) : ℕ :=
  At.num Zp l ((((messagesAt (At.sentAt Zp) l).findIdx? fun y => y.shape.maskRows != 0)).getD 0)

/-- What a thread's step leaves at a border: P of the state behind, at every step from ThrS. -/
def HoldsBehindEveryStep {Bk : ProverCoinCounts} {S Cl V W X Pb : Type} (T : Thread Bk S Cl V W X Pb)
    (Said : Nat → Coins Bk → Mid W X → Prop) (b : ℕ) (P : S → Prop) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k st m En ds y cols st', ThrS T Said b k st m En →
    drawsFit blk.rounds ds = true → T.Stepped blk k st m En ds y cols st' → P st'

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Desc.Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (cs : List (RiderCl (Local W₀ Rc ProofFile.Inst Tr) TS))
  (Kp : Desc.Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)

local notation "PS" => Desc.First.flatPlacesOf linksFull true
set_option quotPrecheck false in
local notation "𝔐" => AtMg.𝔇 (AtMgA.toAtMg h) (AtMgA.𝔇 h)
set_option quotPrecheck false in
local notation "LH" => lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w
set_option quotPrecheck false in
local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf (At.X Zp).P.frame) false
set_option quotPrecheck false in
local notation "theD" => Desc.First.Look.P.ofPlace (Params.settingOf (At.X Zp).P.frame) true

include h in
/-- **Under the head the mask row's message has one seat at both lists.** -/
theorem maskSeatsAgreeAtHead : maskSeatsAgree (At.sentAt Zp) (At.pseats Zp) = true := by
  have e1 : At.pseats Zp = P5T.psFull := h.toAtMg.seats_written.1
  have e3 : (At.sentAt Zp).shape = P6T.sentShape.shape := h.toAtMg.shape_written
  rw [e1, maskSeatsAgreeReadsTheShapeAlone e3]
  exact maskSeatsAgreeWritten

include h in
/-- **The seat at the calls' list bears the plan's number of the link's own message.** -/
theorem maskSeatBearsPlanNumber {l m : ℕ} (hl : l < (At.sentAt Zp).shape.link.length)
    (hm : maskMsg (At.sentAt Zp) l = some (P6T.keptN (At.sentAt Zp) l + m)) :
    At.arr Zp (P6T.seatCallsT (At.pseats Zp) (At.sentAt Zp) l (P6T.keptN (At.sentAt Zp) l + m)).1
      (P6T.seatCallsT (At.pseats Zp) (At.sentAt Zp) l (P6T.keptN (At.sentAt Zp) l + m)).2 =
      At.num Zp l m := by
  obtain ⟨p, p₀, hc, hf, hk0⟩ := P6T.maskSeats_gives (ProofFile.Honest.K5.maskSeats_head h) hl hm
  have key := P6T.key_of_call hc (Nat.le_add_right _ _)
  rw [Nat.add_sub_cancel_left] at key
  have es : P6T.seatCallsT (At.pseats Zp) (At.sentAt Zp) l (P6T.keptN (At.sentAt Zp) l + m) =
      (p.j, p.t) := by
    unfold P6T.seatCallsT
    rw [hc]
    rfl
  rw [es]
  exact P5T.arrOf_is_num _ p.j p.t l m p₀ hf (hk0.trans key)

/-- **The member of the table's list that holds link l's mask row.** Its seat at both lists, its
number, and no pad below the place's number of slots. Conditional on the head. -/
theorem maskMemberAtLink {l : ℕ} (hl : l < 25) {y : Desc.First.Look.Place}
    (hlook : lookAt (At.X Zp) l false = some y) :
    ∃ (m : ℕ) (mem : Mem),
      ((messagesAt h.𝔇.sent l).findIdx? fun u => u.shape.maskRows != 0) = some m ∧
      (h.𝔇.ms.find? fun u => decide (Desc.Sound.seatOf u = h.𝔇.l3.seat l false
        ((Desc.First.Look.keptAt h.𝔇.sent l).length + m))) = some mem ∧
      h.𝔇.l3.seat l true m = h.𝔇.l3.seat l false ((Desc.First.Look.keptAt h.𝔇.sent l).length + m) ∧
      Desc.Sound.numOf h.𝔇.arr mem = maskRowMessageNumber Zp l ∧
      ∀ ν, ν < y.ns → Desc.padB h.𝔇.cs (mem.1.l.get mem.2).1 true 0 ν = false := by
  obtain rfl : y.link = l := ProofFile.Honest.K3.Law.lookAt_link hlook
  have hB : maskCallsB h.𝔇.sent (sigListCalls h.𝔇.sent h.𝔇.l3.rad y.link) y.link y.ns = true :=
    k03_hB_calls h _ hl y hlook
  obtain ⟨m, hfi, hk⟩ := maskMessageOfTest hB
  have hm : maskMsg h.𝔇.sent y.link =
      some ((Desc.First.Look.keptAt h.𝔇.sent y.link).length + m) := by
    unfold maskMsg
    rw [hfi]
    rfl
  have hM : VerifiableInference.Desc.First.Att.P.MemAt h.𝔇.ms
      (sigListCalls h.𝔇.sent h.𝔇.l3.rad y.link) (fun j => h.𝔇.l3.seat y.link false j.1)
      ⟨_, hk⟩ := memAt_of_some ((k03_calls_seats h hl hlook).1 _) h.toAtMg.h6_at_head
  obtain ⟨mem, hfind, hsh⟩ := hM
  have hseat : Desc.Sound.seatOf mem =
      h.𝔇.l3.seat y.link false ((Desc.First.Look.keptAt h.𝔇.sent y.link).length + m) := by
    simpa using List.find?_some hfind
  have hm' : maskMsg (At.sentAt Zp) y.link =
      some (P6T.keptN (At.sentAt Zp) y.link + m) := hm
  obtain ⟨Lk, mi, hLk, -, -⟩ := P6T.maskMsg_some hm'
  have hlen : y.link < (At.sentAt Zp).shape.link.length := (List.getElem?_eq_some_iff.1 hLk).1
  have hag := List.all_eq_true.1 (maskSeatsAgreeAtHead h) y.link (List.mem_range.2 hlen)
  simp only [hm', Nat.add_sub_cancel_left] at hag
  have eSeat : P6T.seatCallsT (At.pseats Zp) (At.sentAt Zp) y.link
      (P6T.keptN (At.sentAt Zp) y.link + m) = P6T.seatT (At.pseats Zp) y.link m := eq_of_beq hag
  refine ⟨m, mem, hfi, hfind, eSeat.symm, ?_, ?_⟩
  · show h.𝔇.arr (Desc.Sound.seatOf mem).1 (Desc.Sound.seatOf mem).2 = _
    rw [hseat]
    have hfi' : ((messagesAt (At.sentAt Zp) y.link).findIdx? fun u => u.shape.maskRows != 0) =
        some m := hfi
    unfold maskRowMessageNumber
    rw [hfi']
    exact maskSeatBearsPlanNumber h hlen hm'
  · obtain ⟨l₀, -, hbb⟩ := built_of_pub h.laid.pub
    obtain ⟨Xl, hX, e⟩ := Option.map_eq_some_iff.1 (k03_slots_all h hl hlook)
    have e2 : Xl.ns = y.ns := e
    have room := ProofFile.Honest.K5.room_of_built hbb (l := y.link) (X := Xl) hX h.𝔇.l3.rad hk hm
    rw [e2] at room
    intro ν hν
    refine ProofFile.Honest.noPad_one ?_ ν hν
    rw [hsh]
    exact room

set_option maxHeartbeats 4000000 in
/-- **Behind the member at a lookup on the digits: MaskOk and the number of slots.** Conditional on
the head, the pair in front and the member's step. -/
theorem maskFactsBehindDigitsAtLink {l : ℕ} (hl : l < 25) {sub : ModelPart}
    (hsub : linksFull[l]? = some sub) {x : Desc.First.Look.Place}
    (hlook : lookAt (At.X Zp) l true = some x) {blk : Block TS ProofFile.Cl}
    (hb : cF.blocksInOrder[k3K l true]? = some blk) {k : Coins Bk} {st st' : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X} {cols : List OpenedColumn}
    (hT : ThrS (LH).thread SaidOk (k3K l true) k st m E)
    (hSt : (LH).thread.Stepped blk k st m E ds y cols st') :
    VerifiableInference.Desc.K3.k3OnIn (theD x) st = true ∧
      ∃ F, st.fork? = some F ∧ F.ns = x.ns ∧ ∀ a, segAt? st' = some a →
        MaskOk x (𝔐).sent (𝔐).l3.rad (fun j => (𝔐).l3.seat x.link true j.1) (𝔐).ms
          ((𝔐).N.group l) a ∧ a.F.ns = x.ns := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨h0, hR, hx⟩ := factsInFrontOfMember h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w
    (Nat.le_of_lt (List.getElem?_eq_some_iff.1 hb).1) hT
  set z := m.st.input.x.pub
  have hy : IM.Yes 0 blk st st' := ⟨_, _, _, hSt.2⟩
  obtain ⟨b', rs, gs, hat, hOk, hd⟩ := digits_hd_of_yes h.scope h.reads O h.laid.planOk hl hb hy
  rw [O.W] at hat
  have hfront : ∀ p ∈ frontDig mgMore l, (mgAll (𝔐) mgBase).pub p (z, st) = true :=
    front_of_xk _ _ _ z (k3K l true) st hx
  have hbook : bookAt (𝔐).N PS[k3K l true]? st = true := by
    have h4 := (IM.xk_parts hx).2.2.2.1
    rw [IM.placesW_full] at h4
    exact h4
  obtain ⟨hpc, x', hlook', hIn, F, hF, hSz⟩ := dig_front h hl hsub hat z hfront
  obtain rfl : x' = x := Option.some.inj (hlook'.symm.trans hlook)
  obtain ⟨hs, hsh⟩ : ∃ hs, (theD x').shape = some hs := by
    cases e : (theD x').shape with
    | none =>
      unfold Desc.K3.k3OnIn at hIn
      rw [e] at hIn
      cases hIn
    | some hs => exact ⟨hs, rfl⟩
  have T := (k3_digits_step_turns K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp)
    Zp.first.codes Zp.first.shape (IM.k3Place l true) b' hat hOk l rfl hpc hlook hsh st st' rs gs
    hd).1
  have DL : DigLeft st st' := digits_left K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp)
    Zp.first.codes Zp.first.shape (IM.k3Place l true) b' b' hat hOk (narrows_self b') l rfl hpc st
    st' rs gs hd
  obtain ⟨-, hkept⟩ := digits_sorted hl hsub
  have hns : ((𝔐).built[l]?).map (·.ns) = some x'.ns := k03_slots_all h hl hlook
  have hLd : (mgAll (𝔐) mgBase).pub (.ledger l) (z, st) = true :=
    hfront _ (hkept _ (by cases sub <;> simp [keptDigits]))
  have hFr : (mgAll (𝔐) mgBase).pub (.freeAbove l) (z, st) = true :=
    hfront _ (hkept _ (by cases sub <;> simp [keptDigits]))
  have hfree0 := pubFree_mgAll (𝔐) mgBase hns z st hFr
  have hFv : (mgAll (𝔐) mgBase).pub (.freeAbove l) (z, st') = true := by
    rw [mgAll_pub, Desc.First.pubAll_ledger] at hLd
    rw [mgAll_pub, Desc.First.pubAll_freeAbove] at hFr ⊢
    have e : (𝔐).pubD.nsOf l = some x'.ns := hns
    rw [e] at hFr ⊢
    exact digLeft_freeAboveB DL hLd x'.ns hFr
  have hfree := pubFree_mgAll (𝔐) mgBase hns z st' hFv
  obtain ⟨L, R⟩ := atMgR_of_head h (Str := Unit)
    (fun k a => Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) k a.1) (fun _ _ ha => ha)
  have Fo := R.fold
  have elk : x'.link = l := ProofFile.Honest.K3.Law.lookAt_link hlook
  have hTests := h.toAtMg.hTests_digits R.listed hl
  obtain ⟨L', hL⟩ := link_some_of_fork hF
  have Tf := Fo.frameIs (k3K l true) ((z, st), ()) (IM.k3Place l true) l L' hR h0
    (K3Lot.k03_at_full l hl true) rfl hL
  have e : st.live = L'.check := by
    unfold Desc.First.S.live
    rw [hL]
  obtain ⟨m3, hp⟩ := k3DigMoment_at hl
  obtain ⟨-, hown, -, hrest⟩ := Tf
  have hbook' : bookAt (𝔐).N PS[k3K l true + 1]? st' = true :=
    Desc.First.bookAt_step (𝔐).N PS (At.told cF) (k03_book_at Zp cF) (k3K l true)
      (List.getElem?_eq_some_iff.1 (K3Lot.k03_at_full l hl true)).1
      (k03_tells_at h.toAtMg l hl true) st st' T.book (by rw [T.st]) hbook
  have eLive : st'.live = st.live := by
    unfold Desc.First.S.live
    rw [T.link]
    cases st.link? with
    | none => exact T.check
    | some C => rfl
  refine ⟨hIn, F, hF, ns_of_free hfree0 hF, fun a ha => ⟨?_, ?_⟩⟩
  · refine maskOk_at x' (𝔐).sent (𝔐).l3.rad (fun j => (𝔐).l3.seat x'.link true j.1) (𝔐).ms
      ((𝔐).N.group l) (nos := (At.foldD Zp cF L).ownAt l 3) ((𝔐).l3.seat x'.link true)
      (fun _ => rfl) ?_ ?_ ?_ ?_ ?_ hfree (k03_hnS x') hbook' ?_ ?_ (by rw [elk]; exact hTests)
      (k03_digits_seats h hl hlook).1 h.toAtMg.h6_at_head a ha
    · rw [eLive]
      exact Fo.liveShape (k3K l true) ((z, st), ()) hR h0
    · rw [eLive]
      exact Fo.liveGroups (k3K l true) ((z, st), ()) hR h0
    · rw [eLive, e, elk]
      exact (hrest hp).1
    · rw [eLive, e]
      exact (hrest hp).2
    · rw [eLive, e, hown]
      exact congrArg _ m3
    · have h1 := Fo.seatsCarried (k3K l true) ((z, st), ()) hR h0
      unfold Desc.K12.Door.atFirstSeats at h1 ⊢
      rw [T.book]
      exact h1
    · have h1 := Fo.msgShapes (k3K l true) ((z, st), ()) hR h0
      unfold Desc.K12.Door.atFirstShapes at h1 ⊢
      rw [T.st]
      exact h1
  · exact ns_of_free hfree (segAt_parts ha).2.1

set_option maxHeartbeats 4000000 in
/-- **Behind the member at a lookup on the calls, at its place y: MaskOkCalls and the number of
slots.** Conditional on the head, the pair in front and the member's step. -/
theorem maskFactsBehindCallsAtPlace {l : ℕ} (hl : l < 25) {sub : ModelPart}
    (hsub : linksFull[l]? = some sub) {y : Desc.First.Look.Place}
    (hlook : lookAt (At.X Zp) l false = some y) (hsP : (theP y).shape = some y.fs)
    {blk : Block TS ProofFile.Cl} (hb : cF.blocksInOrder[k3K l false]? = some blk) {k : Coins Bk} {st st' : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {yy : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X} {cols : List OpenedColumn}
    (hT : ThrS (LH).thread SaidOk (k3K l false) k st m E)
    (hSt : (LH).thread.Stepped blk k st m E ds yy cols st') :
    VerifiableInference.Desc.K3.k3OnIn (theP y) st = true ∧
      ∃ F, st.fork? = some F ∧ F.ns = y.ns ∧ ∀ a, segAt? st' = some a →
        MaskOkCalls y (𝔐).sent (𝔐).l3.rad (fun j => (𝔐).l3.seat y.link false j.1) (𝔐).ms
          ((𝔐).N.sent l 0) a ∧ a.F.ns = y.ns := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨h0, hR, hx⟩ := factsInFrontOfMember h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w
    (Nat.le_of_lt (List.getElem?_eq_some_iff.1 hb).1) hT
  set z := m.st.input.x.pub
  have hy : IM.Yes 0 blk st st' := ⟨_, _, _, hSt.2⟩
  obtain ⟨hpcW, P', sent, laid, rs, gs, hP, hd⟩ :=
    calls_hd_of_yes h.scope h.reads O h.laid.planOk hl hb hy
  rw [O.W] at hpcW hP
  have eP : P' = theP y := by
    have e0 : placeAt (At.X Zp) l false = some P' := hP
    unfold placeAt at e0
    rw [hlook] at e0
    exact (Option.some.inj e0).symm
  subst eP
  obtain ⟨sub', hs', hpc, -⟩ := K3Lot.k03_sub_full l hl
  obtain rfl : sub' = sub := Option.some.inj (hs'.symm.trans hsub)
  have ek : k3K l false = kOfCalls l := (kOfCalls_border l).symm
  have hfront : ∀ q ∈ frontAtK mgMore (kOfCalls l), (mgAll (𝔐) mgBase).pub q (z, st) = true := by
    rw [← ek]
    exact front_of_xk _ _ _ z (k3K l false) st hx
  have hbook : bookAt (𝔐).N PS[k3K l false]? st = true := by
    have h4 := (IM.xk_parts hx).2.2.2.1
    rw [IM.placesW_full] at h4
    exact h4
  obtain ⟨hIn, hFree, hFresh⟩ := front_three (𝔐) mgBase (a := IM.k3Place l false) st rfl hpcW hpc
    hl hsub (calls_tests hl).1 hlook rfl (hfit_mgAll (𝔐) mgBase rfl) z hfront
  have hns : ((𝔐).built[l]?).map (·.ns) = some y.ns := k03_slots_all h hl hlook
  have hFv := paid_state (𝔐) mgBase K3Lot.ofForm _ laid sent [] st st' rs gs hd hlook hsP hIn hns z
    hFree hFresh (.freeAbove l) (by simp [paidCallsR])
  have hfree0 := pubFree_mgAll (𝔐) mgBase hns z st hFree
  have hfree := pubFree_mgAll (𝔐) mgBase hns z st' hFv
  obtain ⟨F, hF, -, -, -⟩ := k3OnIn_free hsP hIn
  refine ⟨hIn, F, hF, ns_of_free hfree0 hF, fun a ha => ⟨?_, ns_of_free hfree (segAt_parts ha).2.1⟩⟩
  obtain ⟨L, R⟩ := atMgR_of_head h (Str := Unit)
    (fun k a => Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) k a.1) (fun _ _ ha => ha)
  have Fo := R.fold
  have hTm := k03_maskC_at h L R.listed l hl y hlook
  have hsb := k3_calls_sameBut K3Lot.ofForm _ laid sent _ [] st st' rs gs hd
  have ey : y.link = l := ProofFile.Honest.K3.Law.lookAt_link hlook
  obtain ⟨hLv, -, -, -⟩ := VerifiableInference.OnPublicFiles.segAt_parts ha
  have hLu : st.link? = some a.L := hsb.link.symm.trans hLv
  have eLive : st'.live = st.live := by
    rw [live_of_link hLv, live_of_link hLu]
  have hmem : moreItem (sentName l) ∈ (Desc.First.pubSets mgMore linksFull PS)[k3K l false]?.getD []
      := by
    have h1 := List.all_eq_true.1 callsSentFront l (List.mem_range.2 hl)
    unfold callsSentFrontB at h1
    simpa using h1
  have hsent := pubSent_mgAll (𝔐) mgBase l z st (hfront _ (by
    rw [kOfCalls_k3K l]
    exact List.mem_append_left _ hmem))
  obtain ⟨fnext, flink, -, fown, -⟩ := five_of_sentIs hLu hsent
  have hk : k3K l false < (PS).length :=
    (List.getElem?_eq_some_iff.1 (K3Lot.k03_at_full l hl false)).1
  have hbook' := Desc.First.bookAt_step (𝔐).N PS (At.told cF) (k03_book_at Zp cF) (k3K l false) hk
    (k03_tells_at h.toAtMg l hl false) st st' hsb.book (by rw [hsb.st]) hbook
  refine maskOkCalls_at y (𝔐).sent (𝔐).l3.rad (fun j => (𝔐).l3.seat y.link false j.1) (𝔐).ms
    ((𝔐).N.sent l 0) ((𝔐).seat3 y.link false) (fun _ => rfl) ?_ ?_ ?_ ?_ ?_ hfree (Nat.le_refl _)
    hbook' ?_ ?_ hTm (k03_calls_seats h hl hlook).1 h.toAtMg.h6_at_head a ha
  · rw [eLive]
    exact Fo.liveShape (k3K l false) ((z, st), ()) hR h0
  · rw [eLive]
    exact Fo.liveGroups (k3K l false) ((z, st), ()) hR h0
  · rw [live_of_link hLv, ey]
    exact flink
  · rw [live_of_link hLv]
    exact fnext
  · rw [live_of_link hLv, ey]
    exact fown
  · have h1 := Fo.seatsCarried (k3K l false) ((z, st), ()) hR h0
    unfold Desc.K12.Door.atFirstSeats at h1 ⊢
    rw [hsb.book]
    exact h1
  · have h1 := Fo.msgShapes (k3K l false) ((z, st), ()) hR h0
    unfold Desc.K12.Door.atFirstShapes at h1 ⊢
    rw [hsb.st]
    exact h1

include h in
/-- **The six facts on the reader, from MaskOk.** Conditional on the head. -/
theorem readerAtOfMaskOk {l : ℕ} (hl : l < 25) {x y : Desc.First.Look.Place}
    (hlookD : lookAt (At.X Zp) l true = some x) (hlook : lookAt (At.X Zp) l false = some y)
    {own : List (ℕ × ℕ)} {a : Desc.K9.Part}
    (M : MaskOk x h.𝔇.sent h.𝔇.l3.rad (fun j => h.𝔇.l3.seat x.link true j.1) h.𝔇.ms own a)
    {free : ℕ} (hfree : free ≤ y.ns) :
    ProofFile.Honest.ReaderAt h.𝔇.cs h.𝔇.arr h.𝔇.ms own a (maskRowMessageNumber Zp l) free := by
  obtain ⟨m, mem, hfi, hfind, hseat, hnum, hpad⟩ := maskMemberAtLink h hl hlook
  obtain rfl : x.link = l := ProofFile.Honest.K3.Law.lookAt_link hlookD
  have hB : maskB h.𝔇.sent (digList x h.𝔇.sent h.𝔇.l3.rad) x.link x.arrays.ns = true :=
    k03_hB_digits h _ hl x hlookD
  have h0 : 0 < x.arrays.ns := k03_ns_pos_dig h hl hlookD
  obtain ⟨z, hz, hk, -⟩ := mask_resolves hB h0
  obtain ⟨-, -, -, hw⟩ := maskOracle_own M.frame hz
  obtain ⟨o, ho, hs⟩ := M.seat 0 z h0 hz
  have hzm : z.msg = m := by
    have e0 : Desc.First.Look.seatOf h.𝔇.sent x.link (.mask 0) = some ⟨m, true, 0, 0⟩ := by
      show (((messagesAt h.𝔇.sent x.link).findIdx? fun u => u.shape.maskRows != 0).map fun n =>
        (⟨n, true, 0, 0⟩ : Desc.First.Look.Seat)) = _
      rw [hfi]
      rfl
    rw [e0] at hz
    obtain rfl := Option.some.inj hz
    rfl
  have hs' := hs hk
  have hso : Desc.K9.seatAt own a.d.book o = some (h.𝔇.l3.seat x.link true m) := by
    rw [← hzm]
    exact hs'
  exact ⟨o, _, mem, hw.trans ho, hseat ▸ hso, hfind, hnum, M.one o (hw.trans ho),
    fun ν hν => hpad ν (Nat.lt_of_lt_of_le hν hfree)⟩

include h in
/-- **The six facts on the reader, from MaskOkCalls.** Conditional on the head. -/
theorem readerAtOfMaskOkCalls {l : ℕ} (hl : l < 25) {y : Desc.First.Look.Place}
    (hlook : lookAt (At.X Zp) l false = some y) {own : List (ℕ × ℕ)} {a : Desc.K9.Part}
    (M : MaskOkCalls y h.𝔇.sent h.𝔇.l3.rad (fun j => h.𝔇.l3.seat y.link false j.1) h.𝔇.ms own a)
    {free : ℕ} (hfree : free ≤ y.ns) :
    ProofFile.Honest.ReaderAt h.𝔇.cs h.𝔇.arr h.𝔇.ms own a (maskRowMessageNumber Zp l) free := by
  obtain ⟨m, mem, hfi, hfind, -, hnum, hpad⟩ := maskMemberAtLink h hl hlook
  obtain rfl : y.link = l := ProofFile.Honest.K3.Law.lookAt_link hlook
  have hB : maskCallsB h.𝔇.sent (sigListCalls h.𝔇.sent h.𝔇.l3.rad y.link) y.link y.ns = true :=
    k03_hB_calls h _ hl y hlook
  obtain ⟨xd, tl, hxd⟩ := Q38.digAt_at_head h (Nat.le_of_lt_succ hl)
  have hlookD := k03_look_dig hxd
  have ens : xd.ns = y.ns := by
    have e1 := k03_slots_all h hl hlookD
    have e2 := k03_slots_all h hl hlook
    exact Option.some.inj (e1.symm.trans e2)
  have h0 : 0 < y.ns := ens ▸ k03_ns_pos_dig h hl hlookD
  obtain ⟨z, hz, hk, -⟩ := mask_seated hB h0
  obtain ⟨-, -, -, hw⟩ := VerifiableInference.Desc.First.Att.P.maskOracle_mask M.frame hz
  obtain ⟨o, ho, hs⟩ := M.seat 0 z h0 hz
  have hzm : z.msg = (Desc.First.Look.keptAt h.𝔇.sent y.link).length + m := by
    have e0 : seatCalls h.𝔇.sent y.link (.mask 0) =
        some ⟨(Desc.First.Look.keptAt h.𝔇.sent y.link).length + m, true, 0, 0⟩ := by
      show (((messagesAt h.𝔇.sent y.link).findIdx? fun u => u.shape.maskRows != 0).map fun n =>
        (⟨(Desc.First.Look.keptAt h.𝔇.sent y.link).length + n, true, 0, 0⟩ :
          Desc.First.Look.Seat)) = _
      rw [hfi]
      rfl
    rw [e0] at hz
    obtain rfl := Option.some.inj hz
    rfl
  have hs' := hs hk
  have hso : Desc.K9.seatAt own a.d.book o = some (h.𝔇.l3.seat y.link false
      ((Desc.First.Look.keptAt h.𝔇.sent y.link).length + m)) := by
    rw [← hzm]
    exact hs'
  exact ⟨o, _, mem, hw.trans ho, hso, hfind, hnum, M.one o (hw.trans ho),
    fun ν hν => hpad ν (Nat.lt_of_lt_of_le hν hfree)⟩

/-- The lookup's promise in front bounds what the site spends by the ledger's number of slots. -/
theorem slotsFitLedger {Z : Pub} {s : Site} (hs : s ∈ lookSites Z) {st : TS} {F : Fork}
    (hIn : VerifiableInference.Desc.K3.k3OnIn s.p st = true) (hF : st.fork? = some F) :
    s.p.first + s.at_.face.slots ≤ F.ns := by
  rw [siteFaceIsFaceOfShape hs]
  exact (ledger_onIn hs hIn hF).2.2.1

/-- A place on the calls of a published input has its shape. Conditional on the head's public
equation alone. -/
theorem callsPlaceHasItsShape (hpub : Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X) {l : ℕ}
    {pl : Desc.First.Look.Place} (h1 : lookAt Zp.p.X l false = some pl) :
    (Desc.First.Look.P.ofPlace (Params.settingOf Zp.p.X.P.frame) false pl).shape = some pl.fs := by
  by_cases hh : l = (if Zp.p.X.p4 then 2 else 1) * Zp.p.X.NGr
  · have e : lookAt Zp.p.X ((if Zp.p.X.p4 then 2 else 1) * Zp.p.X.NGr) false = some pl := hh ▸ h1
    exact head_shape _ hpub e
  · by_cases h0 : l % (if Zp.p.X.p4 then 2 else 1) = 0
    · exact lay_shape _ hpub h1 hh h0
    · exact att_shape _ hpub h1 hh h0

include h in
/-- Every link below 25 has its place on the calls. Conditional on the head. -/
theorem callsPlaceAtLink {l : ℕ} (hl : l < 25) :
    ∃ y, lookAt (At.X Zp) l false = some y := by
  rcases Nat.lt_or_ge l 24 with h24 | h24
  · rcases Nat.mod_two_eq_zero_or_one l with he | ho
    · obtain ⟨y, _, hy, -⟩ := layAt_scope h.scope h.reads h.pubOne h24 he
      exact ⟨y, k03_look_lay h hl hy⟩
    · obtain ⟨y, a, -, -, hy, -⟩ :=
        attAt_scope h.scope h.reads h.pubOne h24 ho (𝔐).sent (fun _ => 0)
      exact ⟨y, k03_look_att h hl hy⟩
  · obtain rfl : l = 24 := by omega
    exact ⟨_, k03_look_head h⟩

/-- **The state's debt behind a lookup on the digits, at a site, at every Said stronger than
SaidOk, with the room of what the site spends.** Conditional on the head and hSaid. -/
theorem maskOkBehindDigitsLookup (s : Site) (hsite : s ∈ lookSites Zp) (hd : s.digits = true)
    {sub : ModelPart} (hsub : (LH).links[s.link]? = some sub)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m) {x : Desc.First.Look.Place}
    (hx : lookAt Zp.p.X s.link true = some x) :
    HoldsBehindEveryStep (LH).thread Said (borderOf s.link s.digits) fun st' =>
      ∀ a, segAt? st' = some a →
        MaskOk x h.𝔇.sent h.𝔇.l3.rad (fun j => h.𝔇.l3.seat x.link true j.1) h.𝔇.ms
          (h.𝔇.N.group s.link) a ∧ s.p.first + s.at_.face.slots ≤ a.F.ns := by
  intro blk hb k st m En ds y cols st' hT _ hSt
  have hT' := thrS_mono _ hSaid hT
  have hl := link_lt_head h s hsite
  rw [hd] at hb hT'
  obtain ⟨hIn, F, hF, hns, hall⟩ := maskFactsBehindDigitsAtLink h H Q test carryX item n₁ n₂ b₀ Vd
    cs Kp w hl hsub hx hb hT' hSt
  obtain ⟨pl, h1, h2, -⟩ := ProofFile.Honest.K3.Law.Exchange.site_place Zp s hsite
  rw [hd] at h1 h2
  obtain rfl : pl = x := Option.some.inj (h1.symm.trans hx)
  intro a ha
  obtain ⟨M, e⟩ := hall a ha
  refine ⟨M, ?_⟩
  rw [e, ← hns]
  exact slotsFitLedger hsite (by rw [h2]; exact hIn) hF

/-- **The state's debt behind a lookup on the calls, at a site.** The like. -/
theorem maskOkCallsBehindCallsLookup (s : Site) (hsite : s ∈ lookSites Zp) (hd : s.digits = false)
    {sub : ModelPart} (hsub : (LH).links[s.link]? = some sub)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m) {x : Desc.First.Look.Place}
    (hx : lookAt Zp.p.X s.link false = some x) :
    HoldsBehindEveryStep (LH).thread Said (borderOf s.link s.digits) fun st' =>
      ∀ a, segAt? st' = some a →
        MaskOkCalls x h.𝔇.sent h.𝔇.l3.rad (fun j => h.𝔇.l3.seat x.link false j.1) h.𝔇.ms
          (h.𝔇.N.sent s.link 0) a ∧ s.p.first + s.at_.face.slots ≤ a.F.ns := by
  intro blk hb k st m En ds y cols st' hT _ hSt
  have hT' := thrS_mono _ hSaid hT
  have hl := link_lt_head h s hsite
  rw [hd] at hb hT'
  obtain ⟨hIn, F, hF, hns, hall⟩ := maskFactsBehindCallsAtPlace h H Q test carryX item n₁ n₂ b₀ Vd
    cs Kp w hl hsub hx (callsPlaceHasItsShape h.pubOne hx) hb hT' hSt
  obtain ⟨pl, h1, h2, -⟩ := ProofFile.Honest.K3.Law.Exchange.site_place Zp s hsite
  rw [hd] at h1 h2
  obtain rfl : pl = x := Option.some.inj (h1.symm.trans hx)
  intro a ha
  obtain ⟨M, e⟩ := hall a ha
  refine ⟨M, ?_⟩
  rw [e, ← hns]
  exact slotsFitLedger hsite (by rw [h2]; exact hIn) hF

/-- **The field masks at the digits, at every witness.** Conditional on the head and hSaid. -/
theorem digitsMaskEntriesAtEveryWitness (s : Site) (hsite : s ∈ lookSites Zp)
    (hd : s.digits = true) {sub : ModelPart} (hsub : (LH).links[s.link]? = some sub)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m) {x : Desc.First.Look.Place} {tl : HTailF2}
    (hx : digAt Zp.p.X s.link = some (x, tl)) :
    HoldsBehindEveryStep (LH).thread Said (borderOf s.link s.digits) fun st' =>
      ∀ a, segAt? st' = some a → ∀ (v : WtF) j, j < s.p.first + s.at_.face.slots →
        digNu x tl h.𝔇.sent h.𝔇.l3.rad (fun j => h.𝔇.l3.seat x.link true j.1) h.𝔇.l3.arr v
          (.mask j) = (dataQ (h.𝔇.N.group s.link) a (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms v)).mask j := by
  intro blk hb k st m En ds y cols st' hT hdr hSt a ha v j hj
  have hl := link_lt_head h s hsite
  have hlook := k03_look_dig hx
  obtain ⟨M, room⟩ := maskOkBehindDigitsLookup h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w s hsite hd
    hsub Said hSaid hlook blk hb k st m En ds y cols st' hT hdr hSt a ha
  exact (digits_maskRow x tl h.𝔇.sent h.𝔇.l3.rad _ h.𝔇.l3.arr h.𝔇.ms _ (k03_hB_digits h _ hl x hlook)
    a M v j (Nat.lt_of_lt_of_le hj room)).symm

/-- **The field masks at attention's calls, at every witness.** Conditional on the head and hSaid. -/
theorem attentionMaskEntriesAtEveryWitness (s : Site) (hsite : s ∈ lookSites Zp)
    (hd : s.digits = false) {sub : ModelPart} (hsub : (LH).links[s.link]? = some sub)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m) {x : Desc.First.Look.Place}
    {A : OnBytes.Attention.Shape} {tl : HTailF2} (hx : attAt Zp.p.X s.link = some (x, A, tl)) :
    HoldsBehindEveryStep (LH).thread Said (borderOf s.link s.digits) fun st' =>
      ∀ a, segAt? st' = some a → ∀ (v : WtF) j, j < s.p.first + s.at_.face.slots →
        attNu x A tl h.𝔇.sent h.𝔇.l3.rad (fun j => h.𝔇.l3.seat x.link false j.1) h.𝔇.l3.arr v
          (.mask j) = (dataQ (h.𝔇.N.sent s.link 0) a (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms v)).mask j := by
  intro blk hb k st m En ds y cols st' hT hdr hSt a ha v j hj
  have hl := link_lt_head h s hsite
  have hlook := k03_look_att h hl hx
  obtain ⟨M, room⟩ := maskOkCallsBehindCallsLookup h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w s hsite
    hd hsub Said hSaid hlook blk hb k st m En ds y cols st' hT hdr hSt a ha
  exact (att_maskRow x h.𝔇.sent h.𝔇.l3.rad _ h.𝔇.l3.arr h.𝔇.ms _ A tl (k03_hB_calls h _ hl x hlook)
    a M v j (Nat.lt_of_lt_of_le hj room)).symm

/-- **The field masks at the layers' calls, at every witness.** Conditional on the head and hSaid. -/
theorem layersMaskEntriesAtEveryWitness (s : Site) (hsite : s ∈ lookSites Zp)
    (hd : s.digits = false) {sub : ModelPart} (hsub : (LH).links[s.link]? = some sub)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m) {x : Desc.First.Look.Place} (q : LayPub)
    (tl : HTailF2) (hx : layAt Zp.p.X s.link = some x) :
    HoldsBehindEveryStep (LH).thread Said (borderOf s.link s.digits) fun st' =>
      ∀ a, segAt? st' = some a → ∀ (v : WtF) j, j < s.p.first + s.at_.face.slots →
        layNu x q tl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW h.𝔇.l3.wOf h.𝔇.l3.nr h.𝔇.l3.nc
          (fun j => h.𝔇.l3.seat x.link false j.1) h.𝔇.l3.arr h.𝔇.l3.msgW v (.mask j) =
          (dataQ (h.𝔇.N.sent s.link 0) a (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms v)).mask j := by
  intro blk hb k st m En ds y cols st' hT hdr hSt a ha v j hj
  have hl := link_lt_head h s hsite
  have hlook := k03_look_lay h hl hx
  obtain ⟨M, room⟩ := maskOkCallsBehindCallsLookup h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w s hsite
    hd hsub Said hSaid hlook blk hb k st m En ds y cols st' hT hdr hSt a ha
  exact (lay_maskRow x h.𝔇.sent h.𝔇.l3.rad _ h.𝔇.l3.arr h.𝔇.ms _ q tl h.𝔇.l3.oW h.𝔇.l3.wOf
    h.𝔇.l3.nr h.𝔇.l3.nc h.𝔇.l3.msgW (k03_hB_calls h _ hl x hlook) a M v j
    (Nat.lt_of_lt_of_le hj room)).symm

/-- **The field masks at the head's calls, at every witness.** Conditional on the head and hSaid. -/
theorem headMaskEntriesAtEveryWitness (s : Site) (hsite : s ∈ lookSites Zp)
    (hd : s.digits = false) {sub : ModelPart} (hsub : (LH).links[s.link]? = some sub)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m) (adr : VerifiableInference.Desc.Kinds.Head.Law.HeadAdr)
    (hHead : s.link = headLink Zp.p.X) (tl : HTailF2) :
    HoldsBehindEveryStep (LH).thread Said (borderOf s.link s.digits) fun st' =>
      ∀ a, segAt? st' = some a → ∀ (v : WtF) j, j < s.p.first + s.at_.face.slots →
        headNu adr x₀ tl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW h.𝔇.l3.wOf h.𝔇.l3.nr h.𝔇.l3.nc
          (fun j => h.𝔇.l3.seat x₀.link false j.1) h.𝔇.l3.arr h.𝔇.l3.msgW v (.mask j) =
          (dataQ (h.𝔇.N.sent s.link 0) a (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms v)).mask j := by
  intro blk hb k st m En ds y cols st' hT hdr hSt a ha v j hj
  have hl := link_lt_head h s hsite
  have hlook : lookAt Zp.p.X s.link false = some x₀ := by
    rw [hHead.trans (P1K8T.headLink_at h)]
    exact k03_look_head h
  obtain ⟨M, room⟩ := maskOkCallsBehindCallsLookup h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w s hsite
    hd hsub Said hSaid hlook blk hb k st m En ds y cols st' hT hdr hSt a ha
  exact (head_maskRow (x := x₀) (D := h.𝔇.sent) (rad := h.𝔇.l3.rad)
    (seatT := fun j => h.𝔇.l3.seat x₀.link false j.1) (arr := h.𝔇.l3.arr) (ms := h.𝔇.ms) (adr := adr) (tl := tl) (oW := h.𝔇.l3.oW) (wOf := h.𝔇.l3.wOf) (nr := h.𝔇.l3.nr)
    (nc := h.𝔇.l3.nc) (msgW := h.𝔇.l3.msgW) (k03_hB_calls h _ hl x₀ hlook) _ a M v j
    (Nat.lt_of_lt_of_le hj room)).symm

/-- **The six facts on the reader behind a lookup on the digits, up to what the site spends.**
Conditional on the head and hSaid. -/
theorem readerAtBehindDigitsLookup (s : Site) (hsite : s ∈ lookSites Zp) (hd : s.digits = true)
    {sub : ModelPart} (hsub : (LH).links[s.link]? = some sub)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m) :
    HoldsBehindEveryStep (LH).thread Said (borderOf s.link s.digits) fun st' =>
      ∀ a, segAt? st' = some a →
        ProofFile.Honest.ReaderAt h.𝔇.cs h.𝔇.arr h.𝔇.ms (h.𝔇.N.group s.link) a
          (maskRowMessageNumber Zp s.link) (s.p.first + s.at_.face.slots) := by
  intro blk hb k st m En ds y cols st' hT hdr hSt a ha
  have hl := link_lt_head h s hsite
  obtain ⟨x, h1, -, -⟩ := ProofFile.Honest.K3.Law.Exchange.site_place Zp s hsite
  rw [hd] at h1
  obtain ⟨yc, hyc⟩ := callsPlaceAtLink h hl
  obtain ⟨M, room⟩ := maskOkBehindDigitsLookup h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w s hsite hd
    hsub Said hSaid h1 blk hb k st m En ds y cols st' hT hdr hSt a ha
  have ens : x.ns = yc.ns :=
    Option.some.inj ((k03_slots_all h hl h1).symm.trans (k03_slots_all h hl hyc))
  exact readerAtOfMaskOk h hl h1 hyc M (by
    have := room.trans M.ns
    rw [k03_arrays_ns, ens] at this
    exact this)

/-- **The six facts on the reader behind a lookup on the calls, up to what the site spends.** At the
same number as on the digits. Conditional on the head and hSaid. -/
theorem readerAtBehindCallsLookup (s : Site) (hsite : s ∈ lookSites Zp) (hd : s.digits = false)
    {sub : ModelPart} (hsub : (LH).links[s.link]? = some sub)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m) :
    HoldsBehindEveryStep (LH).thread Said (borderOf s.link s.digits) fun st' =>
      ∀ a, segAt? st' = some a →
        ProofFile.Honest.ReaderAt h.𝔇.cs h.𝔇.arr h.𝔇.ms (h.𝔇.N.sent s.link 0) a
          (maskRowMessageNumber Zp s.link) (s.p.first + s.at_.face.slots) := by
  intro blk hb k st m En ds y cols st' hT hdr hSt a ha
  have hl := link_lt_head h s hsite
  obtain ⟨x, h1, -, -⟩ := ProofFile.Honest.K3.Law.Exchange.site_place Zp s hsite
  rw [hd] at h1
  obtain ⟨M, room⟩ := maskOkCallsBehindCallsLookup h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w s hsite
    hd hsub Said hSaid h1 blk hb k st m En ds y cols st' hT hdr hSt a ha
  exact readerAtOfMaskOkCalls h hl h1 M (room.trans M.ns)

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.maskSeatsAgreeReadsTheShapeAlone
#print axioms ProofFile.Honest.K3.Term.maskSeatsAgreeWritten
#print axioms ProofFile.Honest.K3.Term.maskMessageOfTest
#print axioms ProofFile.Honest.K3.Term.siteFaceIsFaceOfShape
#print axioms ProofFile.Honest.K3.Term.maskSeatsAgreeAtHead
#print axioms ProofFile.Honest.K3.Term.maskSeatBearsPlanNumber
#print axioms ProofFile.Honest.K3.Term.maskMemberAtLink
#print axioms ProofFile.Honest.K3.Term.maskFactsBehindDigitsAtLink
#print axioms ProofFile.Honest.K3.Term.maskFactsBehindCallsAtPlace
#print axioms ProofFile.Honest.K3.Term.readerAtOfMaskOk
#print axioms ProofFile.Honest.K3.Term.readerAtOfMaskOkCalls
#print axioms ProofFile.Honest.K3.Term.slotsFitLedger
#print axioms ProofFile.Honest.K3.Term.callsPlaceHasItsShape
#print axioms ProofFile.Honest.K3.Term.callsPlaceAtLink
#print axioms ProofFile.Honest.K3.Term.maskOkBehindDigitsLookup
#print axioms ProofFile.Honest.K3.Term.maskOkCallsBehindCallsLookup
#print axioms ProofFile.Honest.K3.Term.digitsMaskEntriesAtEveryWitness
#print axioms ProofFile.Honest.K3.Term.attentionMaskEntriesAtEveryWitness
#print axioms ProofFile.Honest.K3.Term.layersMaskEntriesAtEveryWitness
#print axioms ProofFile.Honest.K3.Term.headMaskEntriesAtEveryWitness
#print axioms ProofFile.Honest.K3.Term.readerAtBehindDigitsLookup
#print axioms ProofFile.Honest.K3.Term.readerAtBehindCallsLookup
