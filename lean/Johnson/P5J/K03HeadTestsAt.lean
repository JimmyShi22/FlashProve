-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03HeadTestsAt.lean: THE FIVE TESTS OF THE LOOKUPS' LEDGER AT THE OUTPUT HEAD's CALLS (structure HeadRestR: hs · hbase · hsome · hsent · hfits), AT THE CLOSED CONSTANT, IN ITS OWN TEXTS.
Under h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x (its field headAt : headAt (At.X Zp) = some x), 𝔇 := h.toAtMg.𝔇 h.𝔇:
  k03_head_link: x.link = 24 (headAt_link; the tower's headLink_in_scope).
  k03_head_hs: hs: the kind's own parameters make the place's shape: BY headAt's OWN MAKE (the lookups' headAt_shape): no test is left.
  k03_head_seats: hsome ∧ hsent ∧ hfits, from the head's fields k3 and plan.fit. NOT THROUGH k03_calls_seats: that one speaks at lookAt's place; headAt's place is lookAt's WITH ITS SHAPE LAID ANEW: the three sentences read the place's link alone, so they are had at the link 24 directly.
  k03_head_base: hbase, for q with (h.toAtMg.row 𝔏)[k3K 24 false]? = some q: from k03_base_at with the two premises that P5J/K03BookAt.lean pays; ITS THIRD, hg : fenceFit (At.N Zp cF) linksFull PS = true, STAYS A PREMISE (a named test).
(Where this and lean/THEOREM.md differ, the page
holds.)
NOT HERE: «slots» (AttShortR | LayShortR: (𝔇.built[l]?).map (·.ns) = some (P.ofPlace … false x).ns): no debt of the head's calls: a file of its own is to try it as a theorem (for the layers' links built_ns_plain lies; for attention's none is named here). (Where this and lean/THEOREM.md differ, the page holds.)

Limits. It pays four of the five outright and the fifth under one named test. The head is a premise; a member of it is proved at the second hash function OnBytes.secondHashFunction, at two written sets of public files VerifierAndGoals.storedPublicFiles and VerifierAndGoals.zGap, in the side library (AtFullSide/Top/: headMember_zFull, headMember_zGap); at other files or hashes none is shown. At OnBytes.secondHashFunction.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.K03BookAt
import Johnson.P5J.SeatsFitAt
import Johnson.P5J.K03Terms
import Johnson.Desc.Sound.MgAt.K3HeadR
import Johnson.Desc.Sound.MgAt.K3Pins
import Johnson.Desc.First.Look.K3AsksHeadLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (sigListCalls)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- The head's place bears the link 24. -/
theorem k03_head_link (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) : x.link = 24 :=
  (headAt_link h.headAt).trans (headLink_in_scope h.scope h.reads h.pubOne)

/-- **hs.** -/
theorem k03_head_hs (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    (VerifiableInference.Desc.First.Look.P.ofPlace (Params.settingOf (At.X Zp).P.frame) false x).shape =
      some x.fs :=
  VerifiableInference.Desc.K3Asks.headAt_shape
    ((VerifiableInference.Desc.K3Asks.headAt_up (At.X Zp)).symm.trans h.headAt)

/-- **hsome · hsent · hfits.** -/
theorem k03_head_seats (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    (∀ i, ∃ y ∈ (h.toAtMg.𝔇 h.𝔇).ms, Alike y
      ⟨callsSending x (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).l3.rad
        (fun j => (h.toAtMg.𝔇 h.𝔇).l3.seat x.link false j.1), i⟩) ∧
    (∀ i : Fin (sigListCalls (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).l3.rad x.link).length,
      (h.toAtMg.𝔇 h.𝔇).l3.seat x.link false i.1 ∈ (h.toAtMg.𝔇 h.𝔇).N.sent 24 0) ∧
    VerifiableInference.Desc.Sound.SeatFits (h.toAtMg.𝔇 h.𝔇).G (h.toAtMg.𝔇 h.𝔇).sent.codes
      (sigListCalls (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).l3.rad x.link)
      (fun j => (h.toAtMg.𝔇 h.𝔇).l3.seat x.link false j.1) := by
  have e := k03_head_link h
  obtain ⟨-, -, hs, ht, -, -⟩ := At.k3SeatsB_at Zp cF Z.lay h.k3 24 (by omega : (24 : ℕ) < 25)
  have hs' : At.callsSomeB Zp Z.lay x.link = true := by rw [e]; exact hs
  have ht' : At.callsSentB Zp cF Z.lay x.link 24 = true := by rw [e]; exact ht
  exact ⟨At.calls_some Zp Z.lay x hs', At.calls_sent Zp cF Z.lay x 24 ht',
    At.calls_fits Zp Z.lay (F0T OnBytes.secondHashFunction Zp Np cF) x (At.PlanOk.seatsFit h.plan) hs'⟩

/-- **hbase, under the one named test on the fence.** -/
theorem k03_head_base (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (hg : VerifiableInference.Desc.First.fenceFit (At.N Zp cF) linksFull
      (VerifiableInference.Desc.First.flatPlacesOf linksFull true) = true) :
    ∀ q, (h.toAtMg.row 𝔏)[k3K 24 false]? = some q →
      ∀ t ∈ (h.toAtMg.𝔇 h.𝔇).N.sent 24 0, t.1 < q.base :=
  fun q hq t ht =>
    k03_base_at h.toAtMg 𝔏 q₁ q₂ q₃ (k03_blocks_at h.toAtMg) (k03_bookHeld_at Zp Np cF) hg 24
      (by omega) false q hq t (MgAt.sampled_calls _ (by omega) t ht)

end P5J

#print axioms P5J.k03_head_link
#print axioms P5J.k03_head_hs
#print axioms P5J.k03_head_seats
#print axioms P5J.k03_head_base
