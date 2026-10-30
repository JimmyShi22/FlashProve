-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
No place of a stored set is known at which all premises hold together.
Johnson/Desc/Sound/MgAt/K3DigitsMaskSeat.lean: the lookup on the digits of a segment's approximate
range proof: THE PREMISE hmask OF objIn_dig (MgAt/K3DigitsObjIn.lean: «the mask row's message is
sent and the book seats it among the segment's own»: (maskSeat own c).isSome) AT THE STATE BEHIND AN
ACCEPT OF THE SEATED PIECE, UNDER THE FENCED PREMISES OF THE LEDGER's FIELD othersPub (the promise
in front · «reached» · «no mark»), FROM SEVEN FACTS ALONG THE FOLD AT THE BORDER IN FRONT. After
the like at the calls (MgAt/K3CallsPaid.lean). Joinings. NO RESULT ON THE PROTOCOL.

Main names.
  maskSeat_of_maskOk: where the part meets MaskOk (K3DigitsMask.lean) and the place has a slot, the
    mask row's message has a seat among own (mask_resolves, maskOracle_own; maskAt is maskOracle:
    maskAt_eq).
  maskOk_behind_dig: MaskOk at the state behind, WITHOUT the promise behind among the premises
    (digMaskR_of_facts, K3DigitsMaskAt.lean, has it, for fObj): the book-keeping one border on is
    bookAt_step (under hbf, hn), the test freeAbove behind is digLeft_freeAboveB.
  hmask_dig_mgAll: THE END.
WHAT IS LEFT, BOOKED. FACTS ALONG THE FOLD AT THE BORDER IN FRONT: hLive, hGroups, hLink, hNext,
hOwn, hSeats, hShapes. TESTS: hB, hpos (the place has a slot), hnS, hTests, h6, hbf, hn. ON THE LIST
OF ROUNDS: hSome. TERMS: hM, hns.
OBJECT. A reader of the open segment's copy of the frame and of the book.
Used by K3DigitsFormsJoin.lean (Johnson/Desc/Sound/MgAt/).
LETTERS. Those of digOwed_seven.


Compiled with the whole library.


Limits. A rule over letters. The premises are shown together at no term.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAt.K3DigitsOthers
import Johnson.Desc.Sound.MgAt.K3DigitsFree
import Johnson.Desc.First.Look.K3DigitsMaskAt
import Johnson.Desc.First.Look.K3DigitsSig
import Johnson.Desc.Sound.FormsQ
import Johnson.Desc.First.BookFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open Cb.Fo.Pin
open VerifiableInference.Desc.First (ModelPart Pub Meaning shift pubFit pubSets pubStep pubRowM pubOfItems
  stepOpen openSets start bookFit bookAt bookAt_step pubAll_ledger pubAll_freeAbove)
open VerifiableInference.Desc.K9 (segAt? maskSeat maskAt seatAt)

/-- **Where the part meets MaskOk, the mask row's message has a seat among own.** -/
theorem maskSeat_of_maskOk {x : Desc.First.Look.Place} {D : Desc.First.Look.Sent}
    {rad : OracleShape → ℕ} {seatT : Fin (digList x D rad).length → ℕ × ℕ} {ms : List Mem}
    {own : List (ℕ × ℕ)} {c : Desc.K9.Part}
    (hB : maskB D (digList x D rad) x.link x.arrays.ns = true)
    (M : MaskOk x D rad seatT ms own c) (h0 : 0 < x.arrays.ns) :
    (maskSeat own c).isSome = true := by
  obtain ⟨z, hz, hk, -⟩ := mask_resolves hB h0
  obtain ⟨-, -, -, hw⟩ := maskOracle_own M.frame hz
  obtain ⟨o, ho, hs⟩ := M.seat 0 z h0 hz
  have e : maskAt c.L.check.frame = some o := hw.trans ho
  unfold maskSeat
  rw [e]
  show (seatAt own c.d.book o).isSome = true
  rw [hs hk]
  rfl

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop)

local notation "WT" => Desc.Wit (CellsQ rows cols) Tok MsgT
local notation "PS" => Desc.First.flatPlacesOf linksFull true

/-- **MaskOk AT THE STATE BEHIND, FROM THE PROMISE IN FRONT.** -/
theorem maskOk_behind_dig (hM : Mg.more = {}) {l : ℕ} (hl : l < 25)
    {x : Desc.First.Look.Place} (told : List (List Desc.Oracle))
    (hbf : bookFit Dm.N PS told = true) (hn : told[(k3K l true)]? = some [])
    (hSome : ∀ i, ∃ y ∈ Dm.ms,
      Alike y ⟨digSending x Dm.sent Dm.l3.rad (fun j => Dm.l3.seat x.link true j.1), i⟩)
    {nos : Array ℕ} {n : ℕ} {Ld : Desc.K12.Door.Laid} {M : List OracleShape}
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
    (hShapes : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch (k3K l true) ((z, a.1), a.2) →
      a.1.failed = none → Desc.K12.Door.atFirstShapes M a.1 = true)
    (hns : (Dm.built[l]?).map (·.ns) = some n) (hnS : n ≤ x.arrays.ns)
    (hTests : maskTestsB (maskOwnIx Dm.sent x.link) 0 nos Dm.N PS[k3K l true + 1]? Ld M
      (Dm.N.group l) (Dm.l3.seat x.link true) = true)
    (h6 : oneShapeB Dm.ms = true) (z : P) (u v : Desc.First.S × Fr.E.Str)
    (T : SameBut u.1 v.1) (DL : DigLeft u.1 v.1)
    (hu : onQ (Fr := Fr) Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u)
    (hR : Rch (k3K l true) ((z, u.1), u.2)) (hun : u.1.failed = none) :
    ∀ c, segAt? v.1 = some c →
      MaskOk x Dm.sent Dm.l3.rad (fun j => Dm.l3.seat x.link true j.1) Dm.ms (Dm.N.group l) c := by
  obtain ⟨sub, hsub, -, -⟩ := K3Lot.k03_sub_full l hl
  have eM : (mgAll Dm Mg).more = mgMore := mgAll_more_closed Dm Mg hM
  obtain ⟨hsort, hkept⟩ := digits_sorted hl hsub
  obtain ⟨hfront, hbook0⟩ : (∀ p ∈ frontDig mgMore l, (mgAll Dm Mg).pub p (z, u.1) = true) ∧
      bookAt Dm.N PS[k3K l true]? u.1 = true := by
    obtain ⟨-, hm | ⟨h1, -, -, -⟩⟩ := hu
    · exact absurd hun hm
    · simp only [Bool.and_eq_true] at h1
      have hp := h1.1.2
      unfold Desc.First.pubHeld at hp
      rw [List.all_eq_true, eM] at hp
      exact ⟨hp, h1.2⟩
  have hLd : (mgAll Dm Mg).pub (.ledger l) (z, u.1) = true :=
    hfront _ (hkept _ (by cases sub <;> simp [keptDigits]))
  have hFr : (mgAll Dm Mg).pub (.freeAbove l) (z, u.1) = true :=
    hfront _ (hkept _ (by cases sub <;> simp [keptDigits]))
  have hFv : (mgAll Dm Mg).pub (.freeAbove l) (z, v.1) = true := by
    rw [mgAll_pub, pubAll_ledger] at hLd
    rw [mgAll_pub, pubAll_freeAbove] at hFr ⊢
    have e : Dm.pubD.nsOf l = some n := hns
    rw [e] at hFr ⊢
    exact digLeft_freeAboveB DL hLd n hFr
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
  refine maskOk_at x Dm.sent Dm.l3.rad (fun j => Dm.l3.seat x.link true j.1) Dm.ms (Dm.N.group l)
    (Dm.l3.seat x.link true) (fun _ => rfl) ?_ ?_ ?_ ?_ ?_ (pubFree_mgAll Dm Mg hns z _ hFv) hnS
    hbook ?_ ?_ hTests hSome h6
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
  · have h0 := hShapes z u hR hun
    unfold Desc.K12.Door.atFirstShapes at h0 ⊢
    rw [T.st]
    exact h0

/-- **hmask.** -/
theorem hmask_dig_mgAll (hM : Mg.more = {}) {l : ℕ} (hl : l < 25)
    {x : Desc.First.Look.Place}
    (hB : maskB Dm.sent (digList x Dm.sent Dm.l3.rad) x.link x.arrays.ns = true)
    (hpos : 0 < x.arrays.ns) (told : List (List Desc.Oracle))
    (hbf : bookFit Dm.N PS told = true) (hn : told[(k3K l true)]? = some [])
    (hSome : ∀ i, ∃ y ∈ Dm.ms,
      Alike y ⟨digSending x Dm.sent Dm.l3.rad (fun j => Dm.l3.seat x.link true j.1), i⟩)
    {nos : Array ℕ} {n : ℕ} {Ld : Desc.K12.Door.Laid} {M : List OracleShape}
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
    (hShapes : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch (k3K l true) ((z, a.1), a.2) →
      a.1.failed = none → Desc.K12.Door.atFirstShapes M a.1 = true)
    (hns : (Dm.built[l]?).map (·.ns) = some n) (hnS : n ≤ x.arrays.ns)
    (hTests : maskTestsB (maskOwnIx Dm.sent x.link) 0 nos Dm.N PS[k3K l true + 1]? Ld M
      (Dm.N.group l) (Dm.l3.seat x.link true) = true)
    (h6 : oneShapeB Dm.ms = true) (z : P) (u v : Desc.First.S × Fr.E.Str)
    (T : SameBut u.1 v.1) (DL : DigLeft u.1 v.1)
    (hu : onQ (Fr := Fr) Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u)
    (hR : Rch (k3K l true) ((z, u.1), u.2)) (hun : u.1.failed = none) :
    ∀ c, segAt? v.1 = some c → (maskSeat (Dm.N.group l) c).isSome = true := fun c hc =>
  maskSeat_of_maskOk hB
    (maskOk_behind_dig Dm Mg Rch hM hl told hbf hn hSome hLive hGroups hLink hNext hOwn hSeats
      hShapes hns hnS hTests h6 z u v T DL hu hR hun c hc) hpos

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.maskSeat_of_maskOk
#print axioms VerifiableInference.OnPublicFiles.maskOk_behind_dig
#print axioms VerifiableInference.OnPublicFiles.hmask_dig_mgAll
