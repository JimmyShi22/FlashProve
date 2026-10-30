-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFE1R/MaskLeftAt.lean: THE TWO THINGS THAT mask_at_front
(Johnson/LPFE1R/MaskAtFront.lean) LEFT: hTests (the public test maskTestsB at the batching's place)
AND hns (the part's ledger has at most the place's number of slots): AT THE CLOSED CONSTANT; SO
LeftRest's FIELD mask FROM THE HEAD, FoldFacts AND "the plan's laying returns". Statements and
proofs: joins.

  maskTests_mono    the test reads of the place the number of messages sent there alone: it passes
                    to a place at which no fewer are sent
  msgs_le_full      BY THE KERNEL, at the written numbers: at each of the 25 links no fewer messages
                    are sent at the batching's place than at the place behind the digits' lookup ·
                    msgs_le_no: a control: at the links' first places 14 m not all 25 pass
  hTests_at_batch   hTests at the batching's place: AtMg.hTests_digits
                    (P2LawR/MasksAtHead.lean), carried on
  hns_at            hns, with equality: AtMgA.slots_at | ns_is
                    (P5J/SlotsAtHead.lean) · k03_slots_all (P5J/K03MaskBAt.lean) · the
                    promise's Bool on where the chain stands (link_of_shape)
  left_mask         LeftRest's field mask's text

Limits. FoldFacts and At.laid? Zp = some Ld are premises (both have payers at the constant by
report). The head is a premise. No soundness statement.

-/
import Johnson.LPFE1R.MaskAtFront
import Johnson.P2LawR.MasksAtHead
import Johnson.P5J.SlotsAtHead
import Johnson.P5J.K03MaskBAt
import Johnson.Desc.First.Link.Law.K09Places
import Johnson.Desc.First.Link.Law.InsideAtTied
import Johnson.LPFK9R.HtinAtConstant
import Johnson.LPFE1R.In8OfFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.OnPublicFiles
open OnBytes
open VerifiableInference.Desc.First (Numbers)

/-- The test passes to a place at which no fewer messages are sent. -/
theorem maskTests_mono {kM? : Option ℕ} {kept : ℕ} {nos : Array ℕ} {N : Numbers}
    {p p' : Option Desc.Place} {Ld : Desc.K12.Door.Laid} {M : List OracleShape}
    {own : List (ℕ × ℕ)} {seatN : ℕ → ℕ × ℕ} (hle : N.msgsAt p ≤ N.msgsAt p')
    (h : maskTestsB kM? kept nos N p Ld M own seatN = true) :
    maskTestsB kM? kept nos N p' Ld M own seatN = true := by
  unfold maskTestsB at h ⊢
  cases kM? with
  | none => exact h
  | some kM =>
    simp only [Option.any_some] at h ⊢
    cases hn : nos[kM - kept]? with
    | none =>
      rw [hn] at h
      exact absurd h (by simp)
    | some o =>
      rw [hn] at h
      simp only [Option.any_some, Bool.and_eq_true, bookedB, decide_eq_true_eq] at h ⊢
      exact ⟨⟨⟨h.1.1.1, by omega⟩, h.1.2⟩, h.2⟩

end VerifiableInference.OnPublicFiles

namespace P5J
open OnBytes OnBytes.Maker OnBytes.Slice OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S FoldFacts shiftAt momentAt flatPlacesOf)
open VerifiableInference.Desc.First.Look (digList lookAt)
open VerifiableInference.Desc.LinkJoin (onTR onT_bools part_reads batchAt link_of_shape
  place_batch placesFit_links slotsAre_iff)
open VerifiableInference.Desc.K12.Door (Laid msgsOfChain)

/-- No fewer messages are sent at place number f m than at the place behind the digits' lookup. -/
def msgsLeB (f : ℕ → ℕ) (m : ℕ) : Bool :=
  decide (P2Law.K3M.numsW.msgsAt (flatPlacesOf linksFull true)[k3K m true + 1]? ≤
    P2Law.K3M.numsW.msgsAt At.ps[f m]?)

set_option maxRecDepth 1000000 in
theorem msgs_le_full : (List.range 25).all (msgsLeB (batchAt fullLinks At.ps)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: against the link's first place the test says no. -/
theorem msgs_le_no : (List.range 25).all (msgsLeB fun m => 14 * m) = false := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : First.Look.Place}

set_option quotPrecheck false in
local notation "FrK" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

/-- **hTests at the batching's place.** -/
theorem AtMgA.hTests_at_batch (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Ld : Laid}
    (hL : At.laid? Zp = some Ld) {m : ℕ} (hm : m < 25) {xx : First.Look.Place}
    (el : xx.link = m) {p : Place} (hp : At.ps[batchAt fullLinks At.ps m]? = some p)
    (h7 : 7 + shiftAt At.links m ≤ p.piece) :
    maskTestsB (maskOwnIx h.𝔇.sent xx.link) 0
      ((At.foldD Zp cF Ld).ownAt m (momentAt (shiftAt At.links m) p.piece)) h.𝔇.N (some p) Ld
      (msgsOfChain Zp.made.proof.1) (h.𝔇.N.group m)
      (fun i => h.𝔇.l3.seat xx.link true i) = true := by
  have hm3 : momentAt (shiftAt At.links m) p.piece = 3 := by
    unfold momentAt
    rw [if_neg (by omega), if_neg (by omega)]
  rw [hm3, el, ← hp]
  refine maskTests_mono ?_ (h.toAtMg.hTests_digits hL hm)
  show (At.N Zp cF).msgsAt _ ≤ (At.N Zp cF).msgsAt _
  rw [h.toAtMg.msgs_fn]
  exact of_decide_eq_true (List.all_eq_true.1 msgs_le_full m (List.mem_range.2 hm))

/-- **hns, with equality.** -/
theorem AtMgA.hns_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : ℕ} (hm : m < 25)
    {xx : First.Look.Place} (hx : lookAt (At.X Zp) m true = some xx) {p : Place}
    (hp : At.ps[batchAt fullLinks At.ps m]? = some p) (hpl : p.link = some m) (z : ProofFile.InstPub) :
    ∀ a pa, onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
        (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
        (batchAt fullLinks At.ps m) a → atS.get? a.1 = some pa → pa.F.ns = xx.arrays.ns := by
  intro a pa ho hpa
  have hb := (onT_bools _ _ _ _ z _ a ho.1).1
  rw [hp] at hb
  have hL := (part_reads a.1 pa hpa).1
  have hlk : pa.L.link = m := link_of_shape hb hpl hL
  have hk : batchAt fullLinks At.ps m ≤ 353 := by
    rw [LPFK9.batch_nAt m hm]
    unfold IM.nAt
    split <;> omega
  have hs := h.slots_at hk ((z, a.1), a.2) ho.2 pa.F pa.L (K9.get_fork a.1 pa hpa) hL
  rw [hlk, h.ns_is hm] at hs
  have e1 := ((slotsAre_iff _ _).1 hs).1
  have e2 := k03_slots_all h hm hx
  have e3 : At.nsAt Zp m = xx.ns := by
    unfold At.nsAt At.nsOf
    have e2' : (Zp.made.p.built.links[m]?).map (·.ns) = some xx.ns := e2
    rw [e2']
    rfl
  rw [e1, e3]
  rfl

/-- **LeftRest's FIELD mask.** -/
theorem AtMgA.left_mask (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Ld : Laid}
    (hL : At.laid? Zp = some Ld)
    (F : FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF Ld) At.reqW At.links At.ps)
    {m : ℕ} (hm : m < 25) {xx : First.Look.Place} (hx : lookAt (At.X Zp) m true = some xx)
    (z : ProofFile.InstPub) :
    ∀ a pa, onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
        (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
        (batchAt fullLinks At.ps m) a → atS.get? a.1 = some pa →
      MaskOkR xx h.𝔇.sent h.𝔇.l3.rad (fun j => h.𝔇.l3.seat xx.link true j.1)
        (h.𝔇.N.group m) pa := by
  intro a pa ho hpa
  have el : xx.link = m := IM.lookAt_link hx
  obtain ⟨p, hp, hpl, h7, h11⟩ := place_batch fullLinks At.ps placesFit_links m
    (by rw [VerifiableInference.Desc.LinkJoin.fullLinks_25]; exact hm)
  exact h.mask_at_front F el hp hpl h11 (h.hTests_at_batch hL hm el hp h7) z a pa ho hpa
    (Nat.le_of_eq (h.hns_at hm hx hp hpl z a pa ho hpa))

end P5J

#print axioms VerifiableInference.OnPublicFiles.maskTests_mono
#print axioms P5J.msgs_le_full
#print axioms P5J.msgs_le_no
#print axioms P5J.AtMgA.hTests_at_batch
#print axioms P5J.AtMgA.hns_at
#print axioms P5J.AtMgA.left_mask
