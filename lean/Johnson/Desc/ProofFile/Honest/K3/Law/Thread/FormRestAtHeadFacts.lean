-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/FormRestAtHeadFacts.lean: the kind "lookup" (K3): THE
PUBLIC FACTS AMONG THE FIELDS OF THE RECORDS `FormRestDigits`, `FormRestDigitsS`, `FormRestCalls`
(FormRest.lean) AS THEOREMS AT THE FIRST CHAIN'S LETTERS `lettersAt`. One test with code; theorems.

  field          theorem         how
  hk             `hk_at`         `site_border` (SiteAtLetters.lean)
  hsub, hpcT     `hsub_at`       THE LIBRARY'S TOP CALLED: `K3Lot.k03_sub_full`; both sorts in one
  hbf            `hbf_at`        THE LIBRARY'S TOP CALLED: `P5J.k03_book_at`. ITS OWN HEAD SAYS:
                                 TRUE BY THE MAKE OF THE NUMBERS, AND SAYS NOTHING OF THE CHAIN: it
                                 is met, and weighs nothing
  hn             `hn_at`         THE LIBRARY'S TOP CALLED: `P5J.k03_tells_at`
  hlook          `hlook_at`      `site_facts` (Law/MemberSite.lean) and the text of `placeAt`
  hsx            `hsx_at`        UNDER THE PUBLIC TEST `shapeIsFs`, a conjunct of "fits"
                                 (`fits_gives`, Law/SeatFitsLaw.lean); `SiteAt` and its like do not
                                 carry it
  hled, hfree    `hled_at`, `hfree_at`   the composed meaning's own text: by `rfl`
  askFresh       `askFresh_at`   THE LIBRARY'S TOP CALLED: `MgAt.k3_open_calls`
  hk1, hfitS     `hk1_at`        A CLOSED TEST OF OURS BY LEAN'S KERNEL (`nextB`, `next_full`), with
                                 a negative one (`next_control`)

THE RECORDS' FREE LETTERS GET THEIR VALUES HERE: told := `P5J.At.told cF`; nsOf :=
`h.𝔇.pubD.nsOf`; sub, x, a': those that `hsub_at`, `hlook_at`, `hk1_at` yield.

CONDITIONAL ON the head (`AtMgA`); those on a site moreover on the site and on a sub-protocol of the
lookups' lot at its place. No instance of the hypotheses beside the head is exhibited in this file.

Conditional on the head `P5J.AtMgA`. That it holds at the goals' two named sets of public files is a
sealed theorem (`headMember_named`, AtFullSide/Top/HeadMemberAtGap.lean), with that file's own
limits; this file does not call it.

Limits. The full size alone. Of the records' public fields hns and hst have no theorem here, nor
anywhere in this folder: `formRestCalls_at` (FormRestAtHeadFill.lean
[not in this library]) takes both as hypotheses. Nothing on soundness, completeness or any other
property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.FormRestAtHead
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.K3Keeps
import Johnson.Desc.ProofFile.Honest.K3.LotPublic
import Johnson.P5J.K03BookAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Block Chain Place Strs)
open VerifiableInference.Desc.First (ModelPart Pub pubSets shift sameStand bookFit flatPlacesOf ledgerB
  freeAboveB)
open VerifiableInference.Desc.First.Look (P lookAt placeAt)
open VerifiableInference.Desc.Sound (mgAll mgBase mgMore mgAll_more_closed linksFull MsgT)
open VerifiableInference.Desc.Sound.MgAt (borderOf pieceOf openAt k3_open_calls)
open OnBytes.Maker (WholeD)
open P5J (AtMgA mgAtAll CellsM TS)
open ProofFile.Honest.FirstThread (lettersAt WtF Script)

/-! ## A closed test on the written list of places -/

/-- **A test with code**: behind the lookup of link l stands a place of the same link at which the
table says the same stand. -/
def nextB (l : Nat) (d : Bool) : Bool :=
  ((flatPlacesOf linksFull true)[borderOf l d + 1]?).any fun a' =>
    sameStand linksFull (IM.k3Place l d) a'

set_option maxRecDepth 1000000 in
/-- It accepts at all fifty. By Lean's kernel. No premise. -/
theorem next_full : (List.range 25).all (fun l => nextB l false && nextB l true) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **A negative test**: eight places on from link 0's lookup on the digits stands a place OF LINK
1; the like test against it rejects. No premise. -/
theorem next_control :
    ((flatPlacesOf linksFull true)[borderOf 0 true + 8]?).map (·.link) = some (some 1) ∧
      (((flatPlacesOf linksFull true)[borderOf 0 true + 8]?).any fun a' =>
        sameStand linksFull (IM.k3Place 0 true) a') = false := by
  decide +kernel

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {Bk : ProverCoinCounts} {W₀ Rc Tr Xo : Type}
  (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Xo))
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
  (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
  (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (keeps : Nat → TS → TS → Prop)

set_option quotPrecheck false in
local notation "LA" => lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps

/-- **The field hk.** CONDITIONAL ON the head, the site, and a sub-protocol of the lookups' lot at
its place. No instance of the hypotheses beside the head is exhibited in this file. -/
theorem hk_at (s : Site) (hsite : s ∈ lookSites Zp) (lot : Block TS ProofFile.Cl)
    (hin : lot ∈ K3Lot.hear Zp) (hlp : lot.place = s.at_.place) :
    (LA).ps[borderOf s.link s.digits]? = some s.at_.place :=
  (site_border h s hsite lot hin hlp).2.1

/-- **The fields hsub and hpcT**, at both sorts. CONDITIONAL ON the same. No instance of the
hypotheses beside the head is exhibited in this file. -/
theorem hsub_at (s : Site) (hsite : s ∈ lookSites Zp) (lot : Block TS ProofFile.Cl)
    (hin : lot ∈ K3Lot.hear Zp) (hlp : lot.place = s.at_.place) :
    ∃ sub, (LA).links[s.link]? = some sub ∧
      s.at_.place.piece = (if s.digits then 7 else 2) + shift sub := by
  obtain ⟨hl, hp⟩ := place_at h s hsite lot hin hlp
  obtain ⟨sub, h1, h2, h3⟩ := K3Lot.k03_sub_full s.link hl
  refine ⟨sub, h1, ?_⟩
  rw [hp]
  cases s.digits
  · exact h2
  · exact h3

/-- **The field hbf**, at the library's own list of what is told. CONDITIONAL ON the head, under
which the letters are laid; the law called has no premise. -/
theorem hbf_at : bookFit (LA).N (LA).ps (P5J.At.told cF) = true :=
  P5J.k03_book_at Zp cF

include h in
/-- **The field hn.** CONDITIONAL ON the head, the site, and a sub-protocol of the lookups' lot at
its place. No instance of the hypotheses beside the head is exhibited in this file. -/
theorem hn_at (s : Site) (hsite : s ∈ lookSites Zp) (lot : Block TS ProofFile.Cl)
    (hin : lot ∈ K3Lot.hear Zp) (hlp : lot.place = s.at_.place) :
    (P5J.At.told cF)[borderOf s.link s.digits]? = some [] :=
  P5J.k03_tells_at h.toAtMg s.link (place_at h s hsite lot hin hlp).1 s.digits

/-- **The field hlook**, with the site's parameters. CONDITIONAL ON the site; the head is none of
its hypotheses. No instance of these hypotheses is exhibited in this file. -/
theorem hlook_at (s : Site) (hsite : s ∈ lookSites Zp) :
    ∃ x, lookAt Zp.p.X s.link s.digits = some x ∧
      s.p = P.ofPlace (OnBytes.Params.settingOf Zp.p.X.P.frame) s.digits x := by
  unfold lookSites at hsite
  obtain ⟨y, _, hsy⟩ := List.mem_filterMap.1 hsite
  obtain ⟨f1, _, f3, f4, _⟩ := site_facts _ _ y s hsy
  rw [← f3, ← f4] at f1
  unfold placeAt at f1
  obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 f1
  exact ⟨x, hx, e.symm⟩

/-- **The field hsx**, at both sorts. CONDITIONAL ON the site, the lookup's place in the public
structure, and the public test with code "the shape is the plan's own, field by field"
(`shapeIsFs`, Honest/K3/LotPublic.lean): A CONJUNCT OF "FITS": `fits_gives`
(Law/SeatFitsLaw.lean) hands it wherever `k3Fits` accepts. The head is none of its hypotheses. No
instance of these hypotheses is exhibited in this file. -/
theorem hsx_at (s : Site) (hsite : s ∈ lookSites Zp) (hT : shapeIsFs Zp.p.X s = true)
    {x : VerifiableInference.Desc.First.Look.Place}
    (hlook : lookAt Zp.p.X s.link s.digits = some x) :
    (P.ofPlace (OnBytes.Params.settingOf Zp.p.X.P.frame) s.digits x).shape = some x.fs := by
  obtain ⟨x', hx', e⟩ := hlook_at s hsite
  obtain rfl : x' = x := Option.some.inj (hx'.symm.trans hlook)
  have h1 := site_shape hsite
  have h2 : fsOf Zp.p.X s = some s.shape := shapeIsFs_holds Zp.p.X s hT
  unfold fsOf at h2
  rw [hlook] at h2
  have h3 : x'.fs = s.shape := Option.some.inj h2
  rw [← e, h1, h3]

/-- **The field hled.** CONDITIONAL ON the head. -/
theorem hled_at : ∀ j u, (LA).MgP.pub (.ledger j) u = ledgerB u.2 := fun _ _ => rfl

/-- **The field hfree**, at the composed meaning's own numbers of slots. CONDITIONAL ON the head. -/
theorem hfree_at : ∀ j u, (LA).MgP.pub (.freeAbove j) u =
    (h.𝔇.pubD.nsOf j).any fun n => freeAboveB n u.2 := fun _ _ => rfl

/-- **The field askFresh.** CONDITIONAL ON the head, the site on the calls, and a sub-protocol of
the lookups' lot at its place. No instance of the hypotheses beside the head is exhibited in this
file. -/
theorem askFresh_at (s : Site) (hsite : s ∈ lookSites Zp) (lot : Block TS ProofFile.Cl)
    (hin : lot ∈ K3Lot.hear Zp) (hlp : lot.place = s.at_.place) (hd : s.digits = false) :
    Pub.linkFresh s.link ∈
      (pubSets (LA).MgP.more (LA).links (LA).ps)[borderOf s.link s.digits]?.getD [] := by
  have hl := (place_at h s hsite lot hin hlp).1
  have h3 := (k3_open_calls hl).2.2
  rw [hd]
  show Pub.linkFresh s.link ∈ (pubSets (mgAll h.𝔇 mgBase).more linksFull
    (flatPlacesOf linksFull true))[borderOf s.link false]?.getD []
  rw [mgAll_more_closed h.𝔇 mgBase rfl]
  exact h3

/-- **The fields hk1 and hfitS.** CONDITIONAL ON the head, the site, and a sub-protocol of the
lookups' lot at its place. No instance of the hypotheses beside the head is exhibited in this file.
-/
theorem hk1_at (s : Site) (hsite : s ∈ lookSites Zp) (lot : Block TS ProofFile.Cl)
    (hin : lot ∈ K3Lot.hear Zp) (hlp : lot.place = s.at_.place) :
    ∃ a', (LA).ps[borderOf s.link s.digits + 1]? = some a' ∧
      sameStand (LA).links s.at_.place a' = true := by
  obtain ⟨hl, hp⟩ := place_at h s hsite lot hin hlp
  have h0 := List.all_eq_true.1 next_full s.link (List.mem_range.2 hl)
  rw [Bool.and_eq_true] at h0
  have h1 : nextB s.link s.digits = true := by
    cases s.digits
    · exact h0.1
    · exact h0.2
  unfold nextB at h1
  cases e : (flatPlacesOf linksFull true)[borderOf s.link s.digits + 1]? with
  | none =>
    rw [e] at h1
    cases h1
  | some a' =>
    rw [e] at h1
    exact ⟨a', e, by rw [hp]; exact h1⟩

end

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.hk_at
#print axioms ProofFile.Honest.K3.Law.AtThr.hsub_at
#print axioms ProofFile.Honest.K3.Law.AtThr.hbf_at
#print axioms ProofFile.Honest.K3.Law.AtThr.hn_at
#print axioms ProofFile.Honest.K3.Law.AtThr.hlook_at
#print axioms ProofFile.Honest.K3.Law.AtThr.hsx_at
#print axioms ProofFile.Honest.K3.Law.AtThr.hled_at
#print axioms ProofFile.Honest.K3.Law.AtThr.hfree_at
#print axioms ProofFile.Honest.K3.Law.AtThr.askFresh_at
#print axioms ProofFile.Honest.K3.Law.AtThr.next_full
#print axioms ProofFile.Honest.K3.Law.AtThr.next_control
#print axioms ProofFile.Honest.K3.Law.AtThr.hk1_at
