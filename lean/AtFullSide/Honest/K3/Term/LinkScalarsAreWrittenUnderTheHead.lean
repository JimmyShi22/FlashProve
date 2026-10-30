-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT NO FILLING: ON PUBLIC DATA ALONE, UNDER THE HEAD `P5J.AtMgA`: no prover and no filling is read.
AtFullSide/Honest/K3/Term/LinkScalarsAreWrittenUnderTheHead.lean: the kind "lookup" (K3): under the
head each of the twelve layers' links and each of the twelve attention links sends the library's
written number of scalars: the form `LinkScalarsAreWritten`
(Johnson/Desc/ProofFile/Honest/K3/Term/LinkScalarsAreWritten.lean) holds at the head's public
record. Three closed facts on numerals, one of them a control; theorems; no definition.

What is shown.
  `writtenLookupsAndOwnRoundsAddUp`: by Lean's kernel: at the three sorts of link off the head: the
    scalars of the written face on the calls, the written number of the link's own rounds (766,
    1072, 765) and the scalars of the written face on the digits add up to `nsW`.
  `writtenLookupsAndOwnRoundsCanFail`: a control: with 765 for 766 at the first link they do not.
  `sortOfALayersLink`, `sortOfAnAttentionLink`: the sorts of the links 2 g and 2 g + 1, g < 12.
  `lookupScalarsAreWrittenAtASite`: under the head a site's shape sends the scalars of the written
    face at the site's link and sort.
  `siteWithItsParameters`: under the head, l < 25, both sorts: a site there, with the public
    record's parameters of the place and their shape.
  `linkScalarsAreWrittenUnderTheHead`: **the head ⊢ `LinkScalarsAreWritten Zp.p.X`.**

How the proof goes. In scope a link's number of scalars is its lookup on the calls, a written
number, and its lookup on the digits
(Johnson/Desc/ProofFile/Honest/K3/Term/LinkScalarsInScope.lean). Under the head the two lookups'
shapes have the written levels (`lookupLevelsAreWrittenUnderTheHead`, LookupLevelsUnderTheHead.lean
beside this file), and a face's scalars read these alone.

Hypotheses that remain. `h`: `P5J.AtMgA`.

Limits. The head's link is not spoken of. The full size alone. That the head has a member:
AtFullSide/Top/HeadMemberAtFull.lean; it is not called here.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import AtFullSide.Honest.K3.Term.LookupThreeTestsUnderTheHead
import Johnson.Desc.ProofFile.Honest.K3.Term.LinkScalarsInScope
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.RngWrittenHolds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open OnBytes.Model (Forest.elems)
open ProofFile.Honest.K3.Law (site_facts)
open VerifiableInference.Desc.First.Look (placeAt place_lay place_att)
open VerifiableInference.Desc.First.Att.P (planIs_tiles planIs_public)
open VerifiableInference.Desc.Kinds.Head.Law.InScope (head_24)
open Johnson.AtFull.Lots.K3 (sortOf nsW)
open AtFullSide.Honest.K3 (vdW)
open AtFullSide.Honest.K3.Term (lookupLevelsAreWrittenUnderTheHead slotsOfFiveNumbers)
open AtFullSide.K14 (k3Face)

/-! ## 1 Closed facts -/

/-- **At the three sorts of link off the head the three written numbers add up to the link's.** -/
theorem writtenLookupsAndOwnRoundsAddUp :
    (k3Face (vdW 0 false).1 (vdW 0 false).2).slots + 766 +
        (k3Face (vdW 0 true).1 (vdW 0 true).2).slots = nsW 0 ∧
      (k3Face (vdW 1 false).1 (vdW 1 false).2).slots + 1072 +
        (k3Face (vdW 1 true).1 (vdW 1 true).2).slots = nsW 1 ∧
      (k3Face (vdW 2 false).1 (vdW 2 false).2).slots + 765 +
        (k3Face (vdW 2 true).1 (vdW 2 true).2).slots = nsW 2 := by
  decide +kernel

/-- A control: with 765 for 766 at the first link the sum is another. -/
theorem writtenLookupsAndOwnRoundsCanFail :
    (k3Face (vdW 0 false).1 (vdW 0 false).2).slots + 765 +
        (k3Face (vdW 0 true).1 (vdW 0 true).2).slots ≠ nsW 0 := by
  decide +kernel

theorem sortOfALayersLink : ∀ g, g < 12 → sortOf (2 * g) = if g = 0 then 0 else 2 := by decide

theorem sortOfAnAttentionLink : ∀ g, g < 12 → sortOf (2 * g + 1) = 1 := by decide

/-! ## 2 Under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- Under the head a site's shape sends the scalars of the written face at its link and sort. -/
theorem lookupScalarsAreWrittenAtASite (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) :
    Forest.elems s.shape =
      (k3Face (vdW (sortOf s.link) s.digits).1 (vdW (sortOf s.link) s.digits).2).slots := by
  obtain ⟨keyLevels, tableLevels⟩ := lookupLevelsAreWrittenUnderTheHead h s hs
  rw [← ProofFile.Honest.K3.Law.Spec.slots_elems]
  exact slotsOfFiveNumbers rfl rfl rfl (by rw [← keyLevels]; rfl) (by rw [← tableLevels]; rfl)

/-- Under the head, at a link below 25 and either sort: a site, with the public record's parameters
of the place and their shape. -/
theorem siteWithItsParameters (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat}
    (linkBelow : l < 25) (d : Bool) :
    ∃ s ∈ lookSites Zp, s.link = l ∧ s.digits = d ∧ placeAt Zp.p.X l d = some s.p ∧
      s.p.shape = some s.shape := by
  obtain ⟨s, hs, link, sort, -, -⟩ := ProofFile.Honest.K3.Law.AtThr.site_digits_paid h l linkBelow d
  have listed := hs
  unfold lookSites at listed
  obtain ⟨address, -, made⟩ := List.mem_filterMap.1 listed
  obtain ⟨parameters, shape, atLink, atSort, -⟩ := site_facts _ _ address s made
  rw [← atLink, ← atSort, link, sort] at parameters
  exact ⟨s, hs, link, sort, parameters, shape⟩

/-- **UNDER THE HEAD THE 24 LINKS OFF THE HEAD SEND THE WRITTEN NUMBERS OF SCALARS.** -/
theorem linkScalarsAreWrittenUnderTheHead (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    LinkScalarsAreWritten Zp.p.X := by
  have publicRecord : OnBytes.Model.Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X :=
    h.toAtMg.pubOne
  obtain ⟨withAttention, groups⟩ := head_24 h.scope publicRecord
  have headsLink : (if Zp.p.X.p4 then 2 else 1) * Zp.p.X.NGr = 24 := by
    rw [withAttention, groups]
    rfl
  have step : (if Zp.p.X.p4 then 2 else 1) = 2 := by
    rw [withAttention]
    rfl
  obtain ⟨firstLink, attentionLink, laterLink⟩ := writtenLookupsAndOwnRoundsAddUp
  intro g groupBelow
  constructor
  · intro hp groupPlan
    obtain ⟨calls, callsListed, callsLink, callsSort, callsParameters, callsShape⟩ :=
      siteWithItsParameters h (l := 2 * g) (by omega) false
    obtain ⟨digits, digitsListed, digitsLink, digitsSort, digitsParameters, digitsShape⟩ :=
      siteWithItsParameters h (l := 2 * g) (by omega) true
    obtain ⟨-, -, layoutsShape, -⟩ := place_lay publicRecord callsParameters
      (by rw [headsLink]; omega) (by rw [step]; omega)
    obtain ⟨hp', groupPlan', tailsShape, -⟩ := ProofFile.Honest.K3.Good.Live.digits_lay publicRecord
      digitsParameters (by rw [headsLink]; omega) (by rw [step]; omega)
    rw [step, show 2 * g / 2 = g by omega] at groupPlan'
    obtain rfl : hp' = hp := Option.some.inj (groupPlan'.symm.trans groupPlan)
    have callsScalars := lookupScalarsAreWrittenAtASite h calls callsListed
    have digitsScalars := lookupScalarsAreWrittenAtASite h digits digitsListed
    rw [Option.some.inj (callsShape.symm.trans layoutsShape), callsLink, callsSort,
      sortOfALayersLink g groupBelow] at callsScalars
    rw [Option.some.inj (digitsShape.symm.trans tailsShape), digitsLink, digitsSort,
      sortOfALayersLink g groupBelow] at digitsScalars
    rw [layersLinkScalarsInScope h.scope h.reads publicRecord groupBelow groupPlan, callsScalars,
      digitsScalars, sortOfALayersLink g groupBelow]
    by_cases first : g = 0
    · rw [if_pos first, if_pos first]
      exact firstLink
    · rw [if_neg first, if_neg first]
      exact laterLink
  · intro a groupPlan
    obtain ⟨calls, callsListed, callsLink, callsSort, callsParameters, callsShape⟩ :=
      siteWithItsParameters h (l := 2 * g + 1) (by omega) false
    obtain ⟨digits, digitsListed, digitsLink, digitsSort, digitsParameters, digitsShape⟩ :=
      siteWithItsParameters h (l := 2 * g + 1) (by omega) true
    obtain ⟨a', groupPlan', plansShape, -⟩ := place_att publicRecord callsParameters
      (by rw [headsLink]; omega) (by rw [step]; omega)
    rw [step, show (2 * g + 1) / 2 = g by omega] at groupPlan'
    obtain rfl : a' = a := Option.some.inj (groupPlan'.symm.trans groupPlan)
    obtain ⟨tailsShape, firstIs, messages⟩ := ProofFile.Honest.K3.Good.Live.digits_att publicRecord
      withAttention groupPlan digitsParameters
    have tiles := planIs_tiles (planIs_public publicRecord) groupPlan
    have callsScalars := lookupScalarsAreWrittenAtASite h calls callsListed
    have digitsScalars := lookupScalarsAreWrittenAtASite h digits digitsListed
    rw [Option.some.inj (callsShape.symm.trans plansShape), callsLink, callsSort,
      sortOfAnAttentionLink g groupBelow] at callsScalars
    rw [Option.some.inj (digitsShape.symm.trans tailsShape), digitsLink, digitsSort,
      sortOfAnAttentionLink g groupBelow] at digitsScalars
    have scalars := attentionLinkScalarsInScope h.scope h.reads publicRecord groupBelow groupPlan
    rw [callsScalars, digitsScalars, attentionLink] at scalars
    -- a.nMsg = first + elems f9 (messages) = elems a.fs + the own rounds' scalars + elems f9 (firstIs) = a.ns (tiles)
    -- = nsW 1 (scalars): linear in these four equations, with nsW 1 an atom
    omega

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.writtenLookupsAndOwnRoundsAddUp
#print axioms ProofFile.Honest.K3.Term.writtenLookupsAndOwnRoundsCanFail
#print axioms ProofFile.Honest.K3.Term.sortOfALayersLink
#print axioms ProofFile.Honest.K3.Term.sortOfAnAttentionLink
#print axioms ProofFile.Honest.K3.Term.lookupScalarsAreWrittenAtASite
#print axioms ProofFile.Honest.K3.Term.siteWithItsParameters
#print axioms ProofFile.Honest.K3.Term.linkScalarsAreWrittenUnderTheHead
