-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
maskOkCalls_at: no state of the verifier and no list of rounds is shown at
which its premises hold together.
Johnson/Desc/First/Look/K3CallsMaskOk.lean: the lookup on a link's CALLS: WHO PAYS MaskOkCalls
(Johnson/Desc/First/Look/K3CallsMask.lean: what the mask row's dictionary asks of the part of the
verifier's state and of the table's list of members): A LEMMA ON ONE STATE s. Statements and proofs.
Ties of texts: no error term. NO SOUNDNESS IS CLAIMED.

THE PREMISES ON s, AND WHERE EACH IS SAID.
  hshape, hgroups: the live request's shape is D's; its groups are its shape's: FoldFacts.liveShape,
    liveGroups.
  hlink, hnext, hown: the live request stands in this link, in front of a later moment or the
    closing; the numbers of the link's own messages are the planned ones: the public test
    "frame.sentIs" (Johnson/Desc/First/FillSent.lean), or a fact along the fold by position.
  hfree: H2K5.Door.freeAboveB n s: the public test freeAbove; hn: n is at most the place's number of
    slots.
  hbook: bookAt N p s: a conjunct of the promise at every border (Johnson/Desc/First/Borders.lean).
  hseats, hshapes: K12.Door.atFirstSeats Ld s, atFirstShapes M s: FoldFacts.seatsCarried, msgShapes.
THE TEST ON THE LIST OF ROUNDS: maskTestsB (K3MaskOkTools.lean) at the calls' list.
ON THE TABLE's LIST OF MEMBERS: hsome: every member of the calls' list has an alike member in ms
  (ListSits.some's own sentence); h6: oneShapeB ms.

OBJECT: no sub-protocol's text: readers of the verifier's state; a function of the list of rounds.
USER: K3CallsMaskOkAt.lean, Johnson/Desc/Sound/MgAt/K3CallsPaid.lean (maskOkCalls_of_sentIs). Meant:
  the premise hOk of calls_objects_att | calls_objects_lay, K3CallsObjects.lean.
LETTERS: x, D, rad, seatT, seatN, ms, own, nos, n, N, p, Ld, M, s free.

Compiled with the whole library.



Main names: `maskOkCalls_at`; `maskOkCalls_of_sentIs`: the same from the public test.

Limits. At the calls alone. One way.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3MaskOkTools
import Johnson.Desc.First.Look.K3CallsMask
import Johnson.Desc.First.Att.K05MasksAtt
import Johnson.Desc.First.FillSent

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.Params
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.K9L (maskOracle)
open VerifiableInference.Desc.Sound (Mem Alike)
open VerifiableInference.Desc.First (Numbers bookAt)
open VerifiableInference.Desc.First.FillSent (SentData sentIsB five_of_sentIs)
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.First.Att.P (oracleOfMsg maskOracle_mask maskMsg seat_mask)

section
variable (x : Desc.First.Look.Place) (D : Sent) (rad : OracleShape → ℕ)
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (ms : List Mem) (own : List (ℕ × ℕ))

local notation "theL" => sigListCalls D rad x.link

/-- **WHO PAYS MaskOkCalls: ON ONE STATE.** -/
theorem maskOkCalls_at {s : Desc.First.S} {nos : Array ℕ} {n : ℕ} {N : Numbers}
    {p : Option Desc.Place} {Ld : Desc.K12.Door.Laid} {M : List OracleShape} (seatN : ℕ → ℕ × ℕ)
    (hT : ∀ i, seatT i = seatN i.val) (hshape : s.live.frame.shape = D.shape)
    (hgroups : s.live.frame.groups = reqGroups s.live.frame.shape)
    (hlink : s.live.frame.link = x.link) (hnext : s.live.frame.next = .laterOrClose)
    (hown : s.live.frame.own = nos) (hfree : H2K5.Door.freeAboveB n s = true) (hn : n ≤ x.ns)
    (hbook : bookAt N p s = true) (hseats : Desc.K12.Door.atFirstSeats Ld s = true)
    (hshapes : Desc.K12.Door.atFirstShapes M s = true)
    (hTests : maskTestsB (maskMsg D x.link) (keptAt D x.link).length nos N p Ld M own seatN = true)
    (hsome : ∀ i, ∃ y ∈ ms, Alike y ⟨⟨theL, seatT⟩, i⟩) (h6 : oneShapeB ms = true) :
    ∀ a, segAt? s = some a → MaskOkCalls x D rad seatT ms own a := by
  intro a ha
  obtain ⟨hL, hF, est, ebk⟩ := segAt_parts ha
  obtain ⟨kM, o, hkM, hle, hno, hlt, hpl, hin, h1r⟩ := maskTests_yes hTests
  rw [live_of_link hL] at hshape hgroups hlink hnext hown
  have hfr := frameIs_of hshape hgroups hlink hnext
  have horc : oracleOfMsg a.L.check.frame (keptAt D x.link).length kM = some o := by
    unfold oracleOfMsg
    rw [if_neg (by omega), hown]
    exact hno
  refine ⟨hfr, ?_, ?_, ?_, ?_⟩
  · exact fun k _ => memAt_of_some (hsome k) h6
  · intro j z _ hz
    rw [seat_mask hkM j] at hz
    obtain rfl := Option.some.inj hz
    refine ⟨o, horc, fun hk => ?_⟩
    rw [ebk, hT]
    exact seatAt_of (book_place hbook hseats hlt hpl) hin
  · intro o' ho'
    obtain ⟨-, -, -, hw⟩ := maskOracle_mask hfr (seat_mask hkM 0)
    rw [hw] at ho'
    obtain rfl : o = o' := Option.some.inj (horc.symm.trans ho')
    rw [est]
    exact rowBits_zero hbook hshapes hlt h1r
  · rw [ns_of_free hfree hF]
    exact hn

/-- The same from the public test "frame.sentIs". -/
theorem maskOkCalls_of_sentIs {s : Desc.First.S} {dS : SentData} {n : ℕ} {N : Numbers}
    {p : Option Desc.Place} {Ld : Desc.K12.Door.Laid} {M : List OracleShape} (seatN : ℕ → ℕ × ℕ)
    (hT : ∀ i, seatT i = seatN i.val) (hshape : s.live.frame.shape = D.shape)
    (hgroups : s.live.frame.groups = reqGroups s.live.frame.shape)
    (hsent : sentIsB dS x.link s = true) (hfree : H2K5.Door.freeAboveB n s = true)
    (hn : n ≤ x.ns) (hbook : bookAt N p s = true)
    (hseats : Desc.K12.Door.atFirstSeats Ld s = true)
    (hshapes : Desc.K12.Door.atFirstShapes M s = true)
    (hTests : maskTestsB (maskMsg D x.link) (keptAt D x.link).length (dS.own x.link) N p Ld M own
      seatN = true)
    (hsome : ∀ i, ∃ y ∈ ms, Alike y ⟨⟨theL, seatT⟩, i⟩) (h6 : oneShapeB ms = true) :
    ∀ a, segAt? s = some a → MaskOkCalls x D rad seatT ms own a := by
  intro a ha
  obtain ⟨hL, -, -, -⟩ := segAt_parts ha
  obtain ⟨fnext, flink, -, fown, -⟩ := five_of_sentIs hL hsent
  rw [← live_of_link hL] at fnext flink fown
  exact maskOkCalls_at x D rad seatT ms own seatN hT hshape hgroups flink fnext fown hfree hn hbook
    hseats hshapes hTests hsome h6 a ha

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.maskOkCalls_at
#print axioms VerifiableInference.OnPublicFiles.maskOkCalls_of_sentIs
