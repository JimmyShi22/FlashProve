-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/Top/H0/K2Ties/AtHead.lean: the code switch's law at the closed constant
(P5J.mgAtAll): THE TIES OF THIS LINE, EACH FROM THE HEAD (WITH THE FOURTEEN ENTRY TESTS): one-line
corollaries, so that a caller hands in the head (P5J.AtMg, Johnson/P5J/AtMg.lean) and no pin.
WHAT «FROM THE HEAD (WITH THE FOURTEEN ENTRY TESTS)» MEANS. The head's field «laid» holds, in its
part «asks», that every entry test of the proof file accepts (LPFD.lawsAsk,
Johnson/Desc/Laid/ProofAsks.lean: fourteen rows, of which rows 9 and 10 are the two pins). The
verifier asks these fourteen. P5J.pins_of_laid
(Johnson/Goal/Skeleton/PinsOfLaid.lean) reads the two pins off that field. That a value is laid
under fourteen rows is proved at storedPublicFiles and zGap alone (a field of the head's member: at secondHashFunction, with
fixedConfigurationDigest in the digest's place; side library AtFullSide/Top/). A verifier whose entry tests lack these
two rows gives no such head.
  pin_head · cut_head  the two pins, from the head
  atWritten_head · atTold_head · sends_head  WrittenAt.lean's and ToldAt.lean's structures; the
                     first chain's sendings are the written ones
  offC_ofHead        the named test offC (Johnson/P5J/HidBearsAtMg.lean) accepts
  sentFit_ofHead · sentPlace_ofHead  sentFitB and sentPlaceB accept at all 25
                     switches
  membersPlan_head   membersPlanB (MembersAtPlan.lean): the head, «live» and «the made table is the
                     written one» (these two stay premises here; AtHead3.lean's membersPlan_ofHead
                     asks neither)
  headBears_head     K2Owes' field headBears, at a place whose switch leads out of one of the 25
                     groups
LIMITS. Each file's own. The full size alone. A member of the head is proved at storedPublicFiles and zGap alone
(at secondHashFunction; side library AtFullSide/Top/). No soundness is claimed.
-/
import Johnson.Top.H0.K2Ties.OffHead
import Johnson.Top.H0.K2Ties.SentPlaceAt
import Johnson.Top.H0.K2Ties.RadiiOfTable
import Johnson.Top.H0.K2Ties.HeadAtConst
import Johnson.Goal.Skeleton.PinsOfLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.K2Ties
open VerifiableInference.Desc (Chain Place)
open VerifiableInference.PlanWritten (madePinnedAt cutFirstFull)
open VerifiableInference.Desc.First.K2 (sentFitB switchSpots)
open VerifiableInference.Desc.First.K2Caller (SwRow tableFullLit tableOf membersPlanB sentPlaceB)
open VerifiableInference.Desc.First.K2Hands (sentW)
open Johnson.G (proofSends0)
open OnBytes.Maker (WholeD)
open P5J (AtMg AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Under the head (with the fourteen entry tests) the pin has accepted**: it is one
of the entry tests whose accept the head's field «laid» holds. -/
theorem pin_head (h : AtMg OnBytes.secondHashFunction Z D r₀ Zp Np cF) :
    madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true :=
  (P5J.pins_of_laid h.scope h.laid).1

/-- **Under the head (with the fourteen entry tests) the first chain has the written
cut.** -/
theorem cut_head (h : AtMg OnBytes.secondHashFunction Z D r₀ Zp Np cF) :
    PlanWritten.cutOf cF.blocksInOrder = cutFirstFull :=
  (P5J.pins_of_laid h.scope h.laid).2

theorem atWritten_head (h : AtMg OnBytes.secondHashFunction Z D r₀ Zp Np cF) : AtWritten Zp cF :=
  at_written h.scope h.laid (pin_head h)

theorem atTold_head (h : AtMg OnBytes.secondHashFunction Z D r₀ Zp Np cF) : AtTold Zp cF :=
  at_told (cut_head h) (atWritten_head h)

theorem sends_head (h : AtMg OnBytes.secondHashFunction Z D r₀ Zp Np cF) : Zp.made.proof.1 = proofSends0 :=
  sends_at h.scope h.laid (pin_head h)

/-- **offC, from the head (with the fourteen entry tests).** -/
theorem offC_ofHead (h : AtMg OnBytes.secondHashFunction Z D r₀ Zp Np cF) : h.offC = true :=
  offC_head h (pin_head h)

/-- **sentFitB, from the head (with the fourteen entry tests)**, at all 25 switches. -/
theorem sentFit_ofHead (h : AtMg OnBytes.secondHashFunction Z D r₀ Zp Np cF) : ∀ t ∈ switchSpots,
    sentFitB (P5J.At.N Zp cF) t.1 P5J.At.ps[t.2.2]? Zp.first.codes (sentW t.1).toArray = true :=
  sentFit_at (atWritten_head h) (atTold_head h)

/-- **sentPlaceB, from the head (with the fourteen entry tests)**, at all 25
switches. -/
theorem sentPlace_ofHead (h : AtMg OnBytes.secondHashFunction Z D r₀ Zp Np cF) : ∀ t ∈ switchSpots,
    sentPlaceB (P5J.At.N Zp cF) t.1 P5J.At.ps[t.2.2]? Zp.first.codes (sentW t.1).toArray =
      true :=
  sentPlace_at (atWritten_head h) (atTold_head h)

/-- **membersPlanB, under the head, «live» and «the made table is the written one».** -/
theorem membersPlan_head (h : AtMg OnBytes.secondHashFunction Z D r₀ Zp Np cF)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (hT : tableOf Z.pol Z.lay Z.KL = .ok tableFullLit) {m : ℕ} (hm : m < 25) {r : SwRow}
    (hr : tableFullLit[m]? = some r) :
    membersPlanB Zp (P5J.At.rad Zp Z.lay) (P5J.At.N Zp cF) (m + 1) r = true :=
  membersPlan_const hl h.scope h.laid (pin_head h) hT hm hr

/-- **headBears, from the head (with the fourteen entry tests).** -/
theorem headBears_head (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x) (pl : Place)
    (hm : pl.link.getD P5J.fullLinks.length - 1 < 25) :
    HeadBears h.𝔇.headPart (laysPads h.𝔇.N P5J.fullLinks pl) :=
  headBears_at h (atWritten_head h.toAtMg) pl hm

end VerifiableInference.Desc.First.K2Ties

#print axioms VerifiableInference.Desc.First.K2Ties.pin_head
#print axioms VerifiableInference.Desc.First.K2Ties.cut_head
#print axioms VerifiableInference.Desc.First.K2Ties.atWritten_head
#print axioms VerifiableInference.Desc.First.K2Ties.atTold_head
#print axioms VerifiableInference.Desc.First.K2Ties.sends_head
#print axioms VerifiableInference.Desc.First.K2Ties.offC_ofHead
#print axioms VerifiableInference.Desc.First.K2Ties.sentFit_ofHead
#print axioms VerifiableInference.Desc.First.K2Ties.sentPlace_ofHead
#print axioms VerifiableInference.Desc.First.K2Ties.membersPlan_head
#print axioms VerifiableInference.Desc.First.K2Ties.headBears_head
