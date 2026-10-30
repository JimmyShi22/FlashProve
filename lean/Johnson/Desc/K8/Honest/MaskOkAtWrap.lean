-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/MaskOkAtWrap.lean: THE SMALLNESS TEST: THE DICTIONARY ON THE MASK ROW
(`MaskOkR`, Johnson/Desc/First/Look/K3DigitsMask.lean) AT EVERY STATE WITHOUT A MARK THAT THE FIRST
CHAIN's BLOCKS, EACH WITH THE TEST ON WORDS IN FRONT, REACH IN FRONT OF A SEGMENT's BATCHING: UNDER
THE LIBRARY's HEAD ALONE, AT ALL 25. The library has the sentence at the states of the verifier's
side's frame that are on the table and reached (`P5J.AtMgA.left_mask`,
Johnson/LPFE1R/MaskLeftAt.lean). Here the table's promise is not asked. It stands over the library
and CellOkAtWrap.lean beside it alone. Three theorems; none of the library's goals.

  `link_at_wrap`   the part's link has the segment's number: `Meaning.K2.group_all`
                   (Johnson/IMR/GroupHead.lean: all 25 links, by the cut), off the fold that the
                   reach yields
  `ns_at_wrap`   the part's ledger has as many slots as the digits' lookup's place says: the proof
                   of `AtMgA.hns_at` with the link by the lemma above and the slots' invariant at
                   the blocks' own steps (`slots_at_reached`, Johnson/LPFK9R/SlotsSeat.lean, as
                   `AtMgA.slots_at`' own proof calls it)
  **`maskOkR_at_wrap`**   the head · m < 25 · the digits' lookup's place at m · a state reached so
                   in front of the batching, without a mark · its part pa ⊢ MaskOkR at the data's
                   list of what is sent, radii and seats, at own := h.𝔇.N.group m
HOW. The proofs of `AtMgA.mask_at_front` (Johnson/LPFE1R/MaskAtFront.lean) and `left_mask`, with
what they draw out of "on the table and reached" had otherwise: no mark: a premise here · the facts
on reached states and `bookAt`: as in CellOkAtWrap.lean beside this file · the number of slots: the
lemma above.
ONE LINE TAKES AN INSTANCE AWAY (attribute [-instance] Inst.Model.Scl.ref), as the files beneath do.
TACTICS THAT SEARCH: omega, at numbers of cuts.
Limits. THE LIBRARY's HEAD IS A PREMISE. That any such state is reached is not said. The full size
and the format's second hash function alone.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.K8.Honest.CellOkAtWrap
import Johnson.LPFE1R.MaskLeftAt
import Johnson.P5J.SlotsAtHead
import Johnson.IMR.GroupHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Params
open OnBytes.Maker (WholeD)
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (digList lookAt)
open VerifiableInference.Desc.LinkJoin (batchAt part_reads place_batch placesFit_links slotsAre_iff
  SlotsInv nsZ slots_at_reached)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw RchAt)
open P5J (AtMgA TS F0T fullLinks)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Desc.First.Look.Place}

/-- The part's link has the segment's number. -/
theorem link_at_wrap (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : ℕ} (hm : m < 25)
    {z : ProofFile.InstPub} {s : S}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (batchAt fullLinks P5J.At.ps m) (z, s))
    {pa : K9.Part} (hpa : Desc.K9.atS.get? s = some pa) : pa.L.link = m := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, rs, cols, f⟩ := hr.fold
  have hk := LPFK9.batch_nAt m hm
  obtain ⟨L, hL, hl, -⟩ := Meaning.K2.group_all h.scope h.reads O hm
    (k := batchAt fullLinks P5J.At.ps m)
    (by rw [hk]; unfold IM.nAt; split <;> omega) (by rw [hk]; unfold IM.nAt; split <;> omega) f
  have hL' := (part_reads s pa hpa).1
  obtain rfl : L = pa.L := Option.some.inj (hL.symm.trans hL')
  exact hl

/-- The part's ledger has as many slots as the digits' lookup's place says. -/
theorem ns_at_wrap (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : ℕ} (hm : m < 25)
    {xx : First.Look.Place} (hx : lookAt (P5J.At.X Zp) m true = some xx)
    {z : ProofFile.InstPub} {s : S}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (batchAt fullLinks P5J.At.ps m) (z, s))
    {pa : K9.Part} (hpa : Desc.K9.atS.get? s = some pa) : pa.F.ns = xx.arrays.ns := by
  have hL := (part_reads s pa hpa).1
  have hlk := link_at_wrap h hm hr hpa
  have hk : batchAt fullLinks P5J.At.ps m ≤ 353 := by
    rw [LPFK9.batch_nAt m hm]
    unfold IM.nAt
    split <;> omega
  have hs : SlotsInv (nsZ Zp Zp.p.X.H.ns) s := by
    obtain ⟨Bs, base, O⟩ := h.laid.opened
    obtain ⟨A, B, c, e, _, hs⟩ := slots_at_reached _ h.laid.pub h.headSpots h.laid.value
    have he : HEq cF c :=
      congr_arg_heq (fun X : VerifiableInference.Desc.FileDescription ProofFile.Inst => X.first) e
    obtain rfl : cF = c := eq_of_heq he
    exact hs _ (z, s) hr (by rw [Meaning.Carry.front_len h.scope h.reads O]; exact hk)
  have hs' := hs pa.F pa.L (K9.get_fork s pa hpa) hL
  rw [hlk, h.ns_is hm] at hs'
  have e1 := ((slotsAre_iff _ _).1 hs').1
  have e2 := P5J.k03_slots_all h hm hx
  have e3 : P5J.At.nsAt Zp m = xx.ns := by
    unfold P5J.At.nsAt P5J.At.nsOf
    have e2' : (Zp.made.p.built.links[m]?).map (·.ns) = some xx.ns := e2
    rw [e2']
    rfl
  rw [e1, e3]
  rfl

/-- **THE DICTIONARY ON THE MASK ROW, WITHOUT THE TABLE's PROMISE.** -/
theorem maskOkR_at_wrap (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : ℕ} (hm : m < 25)
    {xx : First.Look.Place} (hx : lookAt (P5J.At.X Zp) m true = some xx)
    {z : ProofFile.InstPub} {s : S}
    (hw : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (batchAt fullLinks P5J.At.ps m) (z, s))
    (hu : s.failed = none) {pa : K9.Part} (hpa : Desc.K9.atS.get? s = some pa) :
    MaskOkR xx h.𝔇.sent h.𝔇.l3.rad (fun j => h.𝔇.l3.seat xx.link true j.1)
      (h.𝔇.N.group m) pa := by
  have el : xx.link = m := IM.lookAt_link hx
  obtain ⟨p, hp, hpl, h7, h11⟩ := place_batch fullLinks P5J.At.ps placesFit_links m
    (by rw [VerifiableInference.Desc.LinkJoin.fullLinks_25]; exact hm)
  have hL0 := P5J.laid_at_head h.toAtMg
  have F := P5J.foldFacts_at_head' h.toAtMg
    (fun k (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) × Unit) =>
      RchAt (F0T OnBytes.secondHashFunction Zp Np cF) k a) (fun _ _ ha => ha) hL0
    (P5J.startB_at_head h.toAtMg)
    (P5J.sendsB_of_madeRow h.toAtMg (P5J.madeRow_at_head h.toAtMg))
  have hrch : RchAt (F0T OnBytes.secondHashFunction Zp Np cF) (batchAt fullLinks P5J.At.ps m) ((z, s), ()) := hw
  have hraw : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (batchAt fullLinks P5J.At.ps m) (z, s) := reach_raw hw
  have hL := (part_reads s pa hpa).1
  obtain ⟨-, hown, -, h4⟩ := F.frameIs _ ((z, s), ()) p m pa.L hrch hu hp hpl hL
  obtain ⟨hlink, hnext⟩ := h4 h11
  have hbook := book_at_wrap h hraw
  rw [hp] at hbook
  have hlive := live_of_link hL
  exact maskOkR_at xx h.𝔇.sent h.𝔇.l3.rad _ _ (fun i => h.𝔇.l3.seat xx.link true i)
    (fun _ => rfl) (F.liveShape _ _ hrch hu) (F.liveGroups _ _ hrch hu)
    (by rw [hlive, el]; exact hlink) (by rw [hlive]; exact hnext) (by rw [hlive]; exact hown)
    hbook (F.seatsCarried _ _ hrch hu) (F.msgShapes _ _ hrch hu)
    (h.hTests_at_batch hL0 hm el hp h7) pa (K9.segAt_of_atS s pa hpa)
    (Nat.le_of_eq (ns_at_wrap h hm hx hraw hpa))

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.link_at_wrap
#print axioms VerifiableInference.Desc.First.K8.Honest.ns_at_wrap
#print axioms VerifiableInference.Desc.First.K8.Honest.maskOkR_at_wrap
