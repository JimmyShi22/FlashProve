-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFE1R/MaskAtFront.lean: LeftRest's FIELD mask (Johnson/Desc/First/Link/Law/LeftOfRest.lean:
what is left of K9's hLeft): MaskOkR (Johnson/Desc/First/Look/K3DigitsMask.lean)
AT THE PART IN FRONT OF A LINK's BATCHING, UNDER THE TABLE's CONDITION THERE, AT THE CLOSED
CONSTANT. Statements and proofs.

  maskOkR_at      ON ONE STATE: a sister of maskOk_at (Look/K3DigitsMaskOk.lean), by
                  its own proof's lines and tools: for MaskOkR, which lacks MaskOk's field mem: SO
                  WITHOUT ITS PREMISES hsome (every place of the list alike to a member) AND h6
                  (oneShapeB ms); and with "the ledger's number of slots is at most the place's" as
                  a premise of its own in the place of freeAboveB
  mask_at_front   at the constant: from FoldFacts (liveShape · liveGroups · frameIs · seatsCarried
                  · msgShapes), the promise's book-keeping (bookAt: onT_bools) and two things left:
                  hTests (the public test maskTestsB at the batching's place) · hns (the
                  slots)

THE CAUTION ("it asks next = .laterOrClose: may not hold at your border: not looked at"):
IT HOLDS THERE: FoldFacts.frameIs' last clause gives link and next at every piece up to 11 + 2
shift; the batching's piece is 8 + 2 shift.
Limits. AN IMPLICATION: FoldFacts, hTests and hns are premises. No soundness statement.

-/
import Johnson.Desc.First.Look.K3DigitsMaskOk
import Johnson.Desc.First.FoldFacts
import Johnson.Desc.First.Link.Law.FromPromise
import Johnson.Desc.First.Link.Law.RbRuns
import Johnson.P5J.FoldAt
import Johnson.P5J.K09List

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.Params
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.K9L (maskOracle)
open VerifiableInference.Desc.First (Numbers bookAt)
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.First.Att.P (oracleOfMsg)

/-- **WHO PAYS MaskOkR: ON ONE STATE.** -/
theorem maskOkR_at (x : Desc.First.Look.Place) (D : Sent) (rad : OracleShape → ℕ)
    (seatT : Fin (digList x D rad).length → ℕ × ℕ) (own : List (ℕ × ℕ)) {s : Desc.First.S}
    {nos : Array ℕ} {N : Numbers} {p : Option Desc.Place} {Ld : Desc.K12.Door.Laid}
    {M : List OracleShape} (seatN : ℕ → ℕ × ℕ) (hT : ∀ i, seatT i = seatN i.val)
    (hshape : s.live.frame.shape = D.shape)
    (hgroups : s.live.frame.groups = reqGroups s.live.frame.shape)
    (hlink : s.live.frame.link = x.link) (hnext : s.live.frame.next = .laterOrClose)
    (hown : s.live.frame.own = nos) (hbook : bookAt N p s = true)
    (hseats : Desc.K12.Door.atFirstSeats Ld s = true)
    (hshapes : Desc.K12.Door.atFirstShapes M s = true)
    (hTests : maskTestsB (maskOwnIx D x.link) 0 nos N p Ld M own seatN = true) :
    ∀ a, segAt? s = some a → a.F.ns ≤ x.arrays.ns → MaskOkR x D rad seatT own a := by
  intro a ha hns
  obtain ⟨hL, hF, est, ebk⟩ := segAt_parts ha
  obtain ⟨kM, o, hkM, -, hno, hlt, hpl, hin, h1r⟩ := maskTests_yes hTests
  rw [live_of_link hL] at hshape hgroups hlink hnext hown
  have hfr := frameIs_of hshape hgroups hlink hnext
  have horc : oracleOfMsg a.L.check.frame 0 kM = some o := by
    unfold oracleOfMsg
    rw [if_neg (Nat.not_lt_zero _), hown]
    exact hno
  refine ⟨hfr, ?_, ?_, hns⟩
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

end VerifiableInference.OnPublicFiles

namespace P5J
open OnBytes OnBytes.Maker OnBytes.Slice OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S FoldFacts shiftAt momentAt)
open VerifiableInference.Desc.First.Look (digList)
open VerifiableInference.Desc.LinkJoin (onTR onT_bools part_reads batchAt)
open VerifiableInference.Desc.K12.Door (Laid msgsOfChain)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : First.Look.Place}

set_option quotPrecheck false in
local notation "FrK" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

/-- **mask.** -/
theorem AtMgA.mask_at_front (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Ld : Laid}
    (F : FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF Ld) At.reqW At.links At.ps)
    {m : ℕ} {xx : First.Look.Place} (el : xx.link = m) {p : Place}
    (hp : At.ps[batchAt fullLinks At.ps m]? = some p) (hpl : p.link = some m)
    (h11 : p.piece ≤ 11 + 2 * shiftAt At.links m)
    (hTests : maskTestsB (maskOwnIx h.𝔇.sent xx.link) 0
      ((At.foldD Zp cF Ld).ownAt m (momentAt (shiftAt At.links m) p.piece)) h.𝔇.N (some p) Ld
      (msgsOfChain Zp.made.proof.1) (h.𝔇.N.group m)
      (fun i => h.𝔇.l3.seat xx.link true i) = true)
    (z : ProofFile.InstPub) :
    ∀ a pa, onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
        (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
        (batchAt fullLinks At.ps m) a → atS.get? a.1 = some pa → pa.F.ns ≤ xx.arrays.ns →
      MaskOkR xx h.𝔇.sent h.𝔇.l3.rad (fun j => h.𝔇.l3.seat xx.link true j.1)
        (h.𝔇.N.group m) pa := by
  intro a pa ho hpa hns
  have hu : a.1.failed = none := Classical.not_not.1 ho.1.2
  have hrch : h.toAtMg.rch (batchAt fullLinks At.ps m) ((z, a.1), a.2) := ho.2
  have hL := (part_reads a.1 pa hpa).1
  obtain ⟨-, hown, -, h4⟩ := F.frameIs _ ((z, a.1), a.2) p m pa.L hrch hu hp hpl hL
  obtain ⟨hlink, hnext⟩ := h4 h11
  have hbook := (onT_bools _ _ _ _ z _ a ho.1).2.2.2.2.2
  rw [hp] at hbook
  have hlive := live_of_link hL
  exact maskOkR_at xx h.𝔇.sent h.𝔇.l3.rad _ _ (fun i => h.𝔇.l3.seat xx.link true i)
    (fun _ => rfl) (F.liveShape _ _ hrch hu) (F.liveGroups _ _ hrch hu)
    (by rw [hlive, el]; exact hlink) (by rw [hlive]; exact hnext) (by rw [hlive]; exact hown)
    hbook (F.seatsCarried _ _ hrch hu) (F.msgShapes _ _ hrch hu) hTests pa
    (K9.segAt_of_atS a.1 pa hpa) hns

end P5J

#print axioms VerifiableInference.OnPublicFiles.maskOkR_at
#print axioms P5J.AtMgA.mask_at_front
