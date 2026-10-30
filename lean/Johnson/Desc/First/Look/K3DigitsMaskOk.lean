-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
maskOk_at: no state of the verifier and no list of rounds is shown at which
its premises hold together.
Johnson/Desc/First/Look/K3DigitsMaskOk.lean: the lookup on the DIGITS of a link's approximate range
proof: WHO PAYS MaskOk (Johnson/Desc/First/Look/K3DigitsMask.lean: what the mask row's dictionary
asks of the part of the verifier's state and of the table's list of members): A LEMMA ON ONE STATE
s: the twin of maskOkCalls_at (K3CallsMaskOk.lean), at the link's own list of all moments, the
seats' function seatOf and no kept message. Statements and proofs. Ties of texts: no error term. NO
SOUNDNESS IS CLAIMED.

THE PREMISES ON s: as at the calls. hlink, hnext, hown: at this border no public test says them: a
fact along the fold, by position. THE TEST ON THE LIST OF ROUNDS: maskTestsB (K3MaskOkTools.lean) at
the digits' list.

OBJECT: no sub-protocol's text: readers of the verifier's state; a function of the list of rounds.
USER: K3DigitsMaskAt.lean and Johnson/Desc/Sound/MgAt/K3DigitsMaskSeat.lean call maskOk_at.
LETTERS: x, D, rad, seatT, seatN, ms, own, nos, n, N, p, Ld, M, s free.

Compiled with the whole library.


Main names: `maskOwnIx`, `seatOf_mask`, `maskOk_at`.

Limits. At the digits alone. One way.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3MaskOkTools
import Johnson.Desc.First.Look.K3DigitsMask

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
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.First.Att.P (oracleOfMsg)

/-- The number, among the link's own, of the message that holds the link's mask row. -/
def maskOwnIx (D : Sent) (i : ℕ) : Option ℕ :=
  (messagesAt D i).findIdx? fun y => y.shape.maskRows != 0

/-- The seat of a mask entry. -/
theorem seatOf_mask {D : Sent} {i k : ℕ} (hm : maskOwnIx D i = some k) (j : ℕ) :
    seatOf D i (.mask j) = some ⟨k, true, 0, j⟩ := by
  unfold maskOwnIx at hm
  show (((messagesAt D i).findIdx? fun y => y.shape.maskRows != 0).map fun m =>
    (⟨m, true, 0, j⟩ : Seat)) = _
  rw [hm]
  rfl

section
variable (x : Desc.First.Look.Place) (D : Sent) (rad : OracleShape → ℕ)
  (seatT : Fin (digList x D rad).length → ℕ × ℕ) (ms : List Mem) (own : List (ℕ × ℕ))

/-- **WHO PAYS MaskOk: ON ONE STATE.** -/
theorem maskOk_at {s : Desc.First.S} {nos : Array ℕ} {n : ℕ} {N : Numbers}
    {p : Option Desc.Place} {Ld : Desc.K12.Door.Laid} {M : List OracleShape} (seatN : ℕ → ℕ × ℕ)
    (hT : ∀ i, seatT i = seatN i.val) (hshape : s.live.frame.shape = D.shape)
    (hgroups : s.live.frame.groups = reqGroups s.live.frame.shape)
    (hlink : s.live.frame.link = x.link) (hnext : s.live.frame.next = .laterOrClose)
    (hown : s.live.frame.own = nos) (hfree : H2K5.Door.freeAboveB n s = true)
    (hn : n ≤ x.arrays.ns) (hbook : bookAt N p s = true)
    (hseats : Desc.K12.Door.atFirstSeats Ld s = true)
    (hshapes : Desc.K12.Door.atFirstShapes M s = true)
    (hTests : maskTestsB (maskOwnIx D x.link) 0 nos N p Ld M own seatN = true)
    (hsome : ∀ i, ∃ y ∈ ms, Alike y ⟨⟨digList x D rad, seatT⟩, i⟩) (h6 : oneShapeB ms = true) :
    ∀ a, segAt? s = some a → MaskOk x D rad seatT ms own a := by
  intro a ha
  obtain ⟨hL, hF, est, ebk⟩ := segAt_parts ha
  obtain ⟨kM, o, hkM, -, hno, hlt, hpl, hin, h1r⟩ := maskTests_yes hTests
  rw [live_of_link hL] at hshape hgroups hlink hnext hown
  have hfr := frameIs_of hshape hgroups hlink hnext
  have horc : oracleOfMsg a.L.check.frame 0 kM = some o := by
    unfold oracleOfMsg
    rw [if_neg (Nat.not_lt_zero _), hown]
    exact hno
  refine ⟨hfr, ?_, ?_, ?_, ?_⟩
  · exact fun k _ => memAt_of_some (hsome k) h6
  · intro j z _ hz
    rw [seatOf_mask hkM j] at hz
    obtain rfl := Option.some.inj hz
    refine ⟨o, horc, fun hk => ?_⟩
    rw [ebk, hT]
    exact seatAt_of (book_place hbook hseats hlt hpl) hin
  · intro o' ho'
    obtain ⟨-, -, -, hw⟩ := maskOracle_own hfr (seatOf_mask hkM 0)
    rw [hw] at ho'
    obtain rfl : o = o' := Option.some.inj (horc.symm.trans ho')
    rw [est]
    exact rowBits_zero hbook hshapes hlt h1r
  · rw [ns_of_free hfree hF]
    exact hn

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.maskOk_at
