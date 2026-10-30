-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
NOT TRIED FOR EMPTINESS: no place of a stored set is known at which all premises hold together.
Johnson/Desc/Sound/MgAt/K3DigitsMaskLean.lean: the lookup on the digits of a segment's approximate
range proof: hmask («the mask row's message is sent and the book seats it among the segment's own»:
(maskSeat own c).isSome) BY THE LEANER ROAD: straight off what the test maskTestsB says
(maskTests_yes, K3MaskOkTools.lean), not through MaskOk. After another house's maskSeat_at at the
calls (Johnson/P5J/K03MaskLeanAt.lean): the same proof at the digits' two letters: the mask
message's number among THE LINK's OWN messages (maskOwnIx) and no kept message in front. Against
hmask_dig_mgAll (MgAt/K3DigitsMaskSeat.lean) it asks less: hpos, hB, hSome, h6, hShapes, hns, hnS
and hM fall. Joinings. NO RESULT ON THE PROTOCOL.

Main names.
  maskSeat_at_dig: ON ONE STATE: no border, no sub-protocol, no term.
  hmask_dig_lean: at the state behind an accept of the seated piece, under SameBut, the promise in
    front, «reached» and «no mark».
WHAT IS LEFT, BOOKED. FACTS ALONG THE FOLD AT THE BORDER IN FRONT (SIX): hLive, hGroups, hLink,
hNext, hOwn, hSeats. TESTS: hTests, hbf, hn.
OBJECT. A reader of the open segment's copy of the frame and of the book.
USER. Nobody yet. Meant: hForms at the new item, in hmask_dig_mgAll's place.
LETTERS. Those of hmask_dig_mgAll.
Limits. A rule over letters.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3DigitsMaskOk
import Johnson.Desc.First.Look.K3DigitsSeatedYes
import Johnson.Desc.Sound.MgAll
import Johnson.Desc.Sound.AtDriver
import Johnson.Desc.Sound.FormsQ
import Johnson.Desc.First.BookFit
import Johnson.Desc.First.Look.K3Base

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Numbers Meaning bookFit bookAt bookAt_step)
open VerifiableInference.Desc.K9 (segAt? maskSeat maskAt seatAt)
open VerifiableInference.Desc.First.Att.P (oracleOfMsg)

/-- **The mask row's seat is there: on one state, at the digits' letters.** -/
theorem maskSeat_at_dig (x : Desc.First.Look.Place) {s : Desc.First.S}
    {D : Desc.First.Look.Sent} {nos : Array ℕ} {N : Numbers} {p : Option Desc.Place}
    {Ld : Desc.K12.Door.Laid} {M : List OracleShape} {own : List (ℕ × ℕ)} (seatN : ℕ → ℕ × ℕ)
    (hshape : s.live.frame.shape = D.shape)
    (hgroups : s.live.frame.groups = reqGroups s.live.frame.shape)
    (hlink : s.live.frame.link = x.link) (hnext : s.live.frame.next = .laterOrClose)
    (hown : s.live.frame.own = nos) (hbook : bookAt N p s = true)
    (hseats : Desc.K12.Door.atFirstSeats Ld s = true)
    (hTests : maskTestsB (maskOwnIx D x.link) 0 nos N p Ld M own seatN = true) :
    ∀ a, segAt? s = some a → (maskSeat own a).isSome = true := by
  intro a ha
  obtain ⟨hL, -, -, ebk⟩ := segAt_parts ha
  obtain ⟨kM, o, hkM, -, hno, hlt, hpl, hin, -⟩ := maskTests_yes hTests
  rw [live_of_link hL] at hshape hgroups hlink hnext hown
  have hfr := frameIs_of hshape hgroups hlink hnext
  have horc : oracleOfMsg a.L.check.frame 0 kM = some o := by
    unfold oracleOfMsg
    rw [if_neg (Nat.not_lt_zero _), hown]
    exact hno
  obtain ⟨-, -, -, hw⟩ := maskOracle_own hfr (seatOf_mask hkM 0)
  have e1 : maskAt a.L.check.frame = some o := hw.trans horc
  have hs : seatAt own a.d.book o = some (seatN kM) := by
    rw [ebk]
    exact seatAt_of (book_place hbook hseats hlt hpl) hin
  unfold maskSeat
  rw [e1]
  show (seatAt own a.d.book o).isSome = true
  rw [hs]
  rfl

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop)

local notation "PS" => Desc.First.flatPlacesOf linksFull true

/-- **hmask, THE LEANER ROAD.** -/
theorem hmask_dig_lean {l : ℕ} (hl : l < 25) {x : Desc.First.Look.Place}
    (told : List (List Desc.Oracle)) (hbf : bookFit Dm.N PS told = true)
    (hn : told[(k3K l true)]? = some [])
    {nos : Array ℕ} {Ld : Desc.K12.Door.Laid} {M : List OracleShape}
    (hLive : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch (k3K l true) ((z, a.1), a.2) →
      a.1.failed = none → a.1.live.frame.shape = Dm.sent.shape)
    (hGroups : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch (k3K l true) ((z, a.1), a.2) →
      a.1.failed = none → a.1.live.frame.groups = reqGroups a.1.live.frame.shape)
    (hLink : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch (k3K l true) ((z, a.1), a.2) →
      a.1.failed = none → a.1.live.frame.link = x.link)
    (hNext : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch (k3K l true) ((z, a.1), a.2) →
      a.1.failed = none → a.1.live.frame.next = .laterOrClose)
    (hOwn : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch (k3K l true) ((z, a.1), a.2) →
      a.1.failed = none → a.1.live.frame.own = nos)
    (hSeats : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch (k3K l true) ((z, a.1), a.2) →
      a.1.failed = none → Desc.K12.Door.atFirstSeats Ld a.1 = true)
    (hTests : maskTestsB (maskOwnIx Dm.sent x.link) 0 nos Dm.N PS[k3K l true + 1]? Ld M
      (Dm.N.group l) (Dm.l3.seat x.link true) = true)
    (z : P) (u v : Desc.First.S × Fr.E.Str) (T : SameBut u.1 v.1)
    (hu : onQ (Fr := Fr) Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u)
    (hR : Rch (k3K l true) ((z, u.1), u.2)) (hun : u.1.failed = none) :
    ∀ c, segAt? v.1 = some c → (maskSeat (Dm.N.group l) c).isSome = true := by
  have hbook0 : bookAt Dm.N PS[k3K l true]? u.1 = true := by
    obtain ⟨-, hm | ⟨h1, -, -, -⟩⟩ := hu
    · exact absurd hun hm
    · simp only [Bool.and_eq_true] at h1
      exact h1.2
  have hbook : bookAt Dm.N PS[k3K l true + 1]? v.1 = true :=
    bookAt_step Dm.N PS told hbf (k3K l true)
      (List.getElem?_eq_some_iff.1 (K3Lot.k03_at_full l hl true)).1 hn u.1 v.1 T.book
      (by rw [T.st]) hbook0
  have eLive : v.1.live = u.1.live := by
    unfold Desc.First.S.live
    rw [T.link]
    cases u.1.link? with
    | none => exact T.check
    | some C => rfl
  refine maskSeat_at_dig x (Dm.l3.seat x.link true) ?_ ?_ ?_ ?_ ?_ hbook ?_ hTests
  · rw [eLive]
    exact hLive z u hR hun
  · rw [eLive]
    exact hGroups z u hR hun
  · rw [eLive]
    exact hLink z u hR hun
  · rw [eLive]
    exact hNext z u hR hun
  · rw [eLive]
    exact hOwn z u hR hun
  · have h0 := hSeats z u hR hun
    unfold Desc.K12.Door.atFirstSeats at h0 ⊢
    rw [T.book]
    exact h0

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.maskSeat_at_dig
#print axioms VerifiableInference.OnPublicFiles.hmask_dig_lean
