-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/FormRestAtHead.lean: the kind "lookup" (K3): FIVE FIELDS
OF THE RECORDS OF PREMISES `FormRestDigits`, `FormRestDigitsS`, `FormRestCalls` (FormRest.lean) AS
THEOREMS AT THE FIRST CHAIN'S LETTERS `lettersAt` (Honest/Thread/FirstAt.lean), all of whose letters
are variables here. Theorems.

  field     theorem        how
  hHe       `hHe_at`       THE LIBRARY'S TOP CALLED: `heldReads_mgAll`
  hIO       `hIO_at`       THE LIBRARY'S TOP CALLED: `inOrderReads_mgAll`; the base meaning's: `rfl`
  hfit      `hfit_at`      THE LIBRARY'S TOP CALLED: `hfit_mgAll`
  hTab      `hTab_at`      THE LIBRARY'S TOP CALLED: `hTab_mgAll`; the site's place and the bound on
                           its link by `site_border` (SiteAtLetters.lean)
  othersP   `othersP_at`   THE LAWS BENEATH THE LIBRARY'S TOP CALLED (`digSaid_mgMore`,
                           `pubP_of_said`); the hands of `othersP_dig_mgAll` in the library's own
                           form of an accept are not met, nor wanted: IT HOLDS AT EVERY STATE

The laws lie in Johnson/Desc/Sound/MgAt/ (K3At.lean, K3Tests.lean, K3DigitsSaid.lean,
K3CallsSaid.lean).

CONDITIONAL ON the head (`AtMgA`: the one hypothesis under which `lettersAt` is laid); the two on a
site moreover on the site and on a sub-protocol of the lookups' lot at its place. No instance of the
hypotheses beside the head is exhibited in this file.

Conditional on the head `P5J.AtMgA`. That it holds at the goals' two named sets of public files is a
sealed theorem (`headMember_named`, AtFullSide/Top/HeadMemberAtGap.lean), with that file's own
limits; this file does not call it.

Limits. The full size alone, as `lettersAt`. Nothing on soundness, completeness or any other
property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SiteAtLetters
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.FormRest
import Johnson.Desc.Sound.MgAt.K3Tests
import Johnson.Desc.Sound.MgAt.K3DigitsSaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Block Chain Place Strs)
open VerifiableInference.Desc.First (ModelPart pubSets pubStep pubRowM pubFit shift)
open VerifiableInference.Desc.Sound (mgAll mgBase mgMore mgAll_more_closed linksFull MsgT)
open VerifiableInference.Desc.Sound.MgAt (borderOf pieceOf)
open VerifiableInference.OnPublicFiles (InOrderReads HeldReads digTableB heldReads_mgAll
        inOrderReads_mgAll hfit_mgAll hTab_mgAll digSaid_mgMore digSaidRowB isLeftB pubP_of_said)
open OnBytes.Maker (WholeD)
open P5J (AtMgA mgAtAll CellsM TS)
open ProofFile.Honest.FirstThread (lettersAt WtF Script)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr Xo : Type}
  (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Xo))
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
  (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
  (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (keeps : Nat → TS → TS → Prop)

set_option quotPrecheck false in
local notation "LA" => lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps

/-- **The field hHe.** CONDITIONAL ON the head. -/
theorem hHe_at : HeldReads (LA).MgP :=
  heldReads_mgAll h.𝔇 mgBase

/-- **The field hIO.** CONDITIONAL ON the head. -/
theorem hIO_at : InOrderReads (LA).MgP :=
  inOrderReads_mgAll h.𝔇 mgBase fun _ _ _ _ _ _ => rfl

/-- **The field hfit.** CONDITIONAL ON the head. -/
theorem hfit_at : pubFit (LA).MgP.more (LA).links (LA).ps = true :=
  hfit_mgAll h.𝔇 mgBase rfl

include h in
/-- A site's place is the library's written one. CONDITIONAL ON the head, the site, and a
sub-protocol of the lookups' lot at its place. No instance of the hypotheses beside the head is
exhibited in this file. -/
theorem place_at (s : Site) (hsite : s ∈ lookSites Zp) (lot : Block TS ProofFile.Cl)
    (hin : lot ∈ K3Lot.hear Zp) (hlp : lot.place = s.at_.place) :
    s.link < 25 ∧ s.at_.place = IM.k3Place s.link s.digits := by
  obtain ⟨hl, _, hpc⟩ := site_border h s hsite lot hin hlp
  refine ⟨hl, ?_⟩
  rw [site_place Zp s hsite, hpc]
  rfl

/-- **The field hTab.** CONDITIONAL ON the same, at a site on the digits, and on the link's sort. No
instance of the hypotheses beside the head is exhibited in this file. -/
theorem hTab_at (s : Site) (hsite : s ∈ lookSites Zp) (lot : Block TS ProofFile.Cl)
    (hin : lot ∈ K3Lot.hear Zp) (hlp : lot.place = s.at_.place) (hd : s.digits = true) (sub : ModelPart)
    (hsub : (LA).links[s.link]? = some sub) :
    digTableB (LA).MgP.more (LA).links (LA).ps (borderOf s.link s.digits) s.at_.place s.link
      (shift sub) = true := by
  obtain ⟨hl, hp⟩ := place_at h s hsite lot hin hlp
  rw [hp, hd]
  exact hTab_mgAll h.𝔇 mgBase rfl s.link hl sub hsub

/-- **The field othersP, AT EVERY STATE.** CONDITIONAL ON the head, the site on the digits, and a
sub-protocol of the lookups' lot at its place. No instance of the hypotheses beside the head is
exhibited in this file. -/
theorem othersP_at (s : Site) (hsite : s ∈ lookSites Zp) (lot : Block TS ProofFile.Cl)
    (hin : lot ∈ K3Lot.hear Zp) (hlp : lot.place = s.at_.place) (hd : s.digits = true)
    (z : ProofFile.InstPub) (t' : TS) :
    ∀ q ∈ pubStep
        ((pubSets (LA).mgP.more (LA).links (LA).ps)[borderOf s.link s.digits]?.getD [])
        (pubRowM (LA).mgP.more (LA).links s.at_.place),
      (∀ j, q ≠ .left j) → (∀ j, q ≠ .leftOn j) → (LA).mgP.pubP q (z, t') := by
  obtain ⟨hl, hp⟩ := place_at h s hsite lot hin hlp
  intro q hq h1 h2
  rw [hp, hd] at hq
  have hq' : q ∈ pubStep ((pubSets (mgAll h.𝔇 mgBase).more linksFull
      (VerifiableInference.Desc.First.flatPlacesOf linksFull true))[borderOf s.link true]?.getD [])
      (pubRowM (mgAll h.𝔇 mgBase).more linksFull (IM.k3Place s.link true)) := hq
  rw [mgAll_more_closed h.𝔇 mgBase rfl] at hq'
  have h0 := List.all_eq_true.1 digSaid_mgMore s.link (List.mem_range.2 hl)
  unfold digSaidRowB at h0
  have h3 := List.all_eq_true.1 h0 q hq'
  rw [Bool.or_eq_true] at h3
  rcases h3 with h3 | h3
  · cases q with
    | left m => exact absurd rfl (h1 m)
    | leftOn m => exact absurd rfl (h2 m)
    | _ => cases h3
  · exact pubP_of_said h.𝔇 mgBase (fun _ _ e => e) q h3 (z, t')

end

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.hHe_at
#print axioms ProofFile.Honest.K3.Law.AtThr.hIO_at
#print axioms ProofFile.Honest.K3.Law.AtThr.hfit_at
#print axioms ProofFile.Honest.K3.Law.AtThr.hTab_at
#print axioms ProofFile.Honest.K3.Law.AtThr.othersP_at
#print axioms ProofFile.Honest.K3.Law.AtThr.place_at
