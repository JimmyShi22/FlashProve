-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/K3/Term/LookupThreeTestsUnderTheHead.lean: the kind "lookup" (K3): under the head
(`P5J.AtMgA`, the library's one hypothesis at the full size), with no premise that the public files are one of
the two named sets: at the book of whatever `onlineProverFromPublicFiles` (Honest/AtPure.lean) returns, at any filling, ALL THREE
public tests on the book accept (`bookFits`, `placeFits`: Honest/K3/Law/RowLends.lean; `startsFit`:
Honest/K3/Law/MasksBook.lean), the third at the site's own first scalar: AT 26 OF THE FIFTY SITES WITH NO FURTHER
PREMISE; AT THE OTHER 24 UNDER ONE NAMED PREMISE, `LinkScalarsAreWritten`. No definition; two closed facts by Lean's
kernel on written data alone, one of them a negative test; eight theorems more.

WHICH 26 NEED NO PREMISE: the 25 lookups on the calls (their first scalar is 0: the link's ledger is fresh) and the
lookup on the digits of the head's link 24 (its first scalar is 2168 in the goals' scope). WHICH 24 DO: the lookups
on the digits of the links 0 to 23: there the first scalar is the link's number of scalars less the lookup's own, and
that the link's number is the written one is the premise.

What is shown.
  `writtenFirstAndSlotsAreTheLinksScalars`   [Lean's kernel] at the three sorts of link off the head: the written
                        first scalar of the digits' lookup and the scalars of the face with the written levels add up
                        to the written number of the link's scalars
  `writtenFirstAndSlots_notAtTheHead`   [Lean's kernel] A NEGATIVE TEST: at the head's sort they do not: other
                        scalars stand behind that lookup
  `slotsOfFiveNumbers`  a face's number of scalars reads its five numbers alone
  `sortOfLinkOffTheHead`, `sortOfOddLink`   a link's sort, off link 24
  `lookupFirstScalarIsWrittenAtASite`   the head, a site s, and `LinkScalarsAreWritten Zp.p.X` IF s is on the digits
                        of a link other than 24 ⊢ s.p.first = `firstW (sortOf s.link) s.digits`
  `lookupThreeTestsAtASite`   the head, hA at any filling, a site, the same conditional premise ⊢ the mask row's owner
                        is found and the three tests accept A.B at the site
  **`lookupThreeTestsUnderTheHead`**   the head, hA, `LinkScalarsAreWritten Zp.p.X` ⊢ that at every site: the text of
                        `k3Fits_at_atPure` (AtFullSide/Honest/K3/FitsAtPure.lean) without its premise on the named files
  `lookupThreeTestsAtTheCallsAndTheHeadsDigits`   the head, hA ⊢ that at every site on the calls or at link 24
  `bookLendsTheMaskRowAtEverySite`   the head, hA, the premise ⊢ owner, `bookFits`, `startsFit` at every site

How. The first scalar. On the calls: `place_lay`, `place_att`, `place_head` (Johnson/Desc/First/Look/K3PlaceLetters.lean).
On the head's digits: `digits_place` (Johnson/Desc/Kinds/Law/K6PubInScope.lean). On the other digits: `digits_lay`
(Honest/K3/Good/Live/WindowsLay.lean), `digits_att` (Honest/K3/Good/Live/Windows.lean), `slots_elems`
(Honest/K3/Law/SlotsElems.lean), the written levels (`lookupLevelsAreWrittenUnderTheHead`,
LookupLevelsUnderTheHead.lean beside this file), the premise and the closed fact. The tests: `k3Fits_written`
(AtFullSide/K14/RawK3Fits.lean) at the one book.

Hypotheses that remain. The head. hA: that `onlineProverFromPublicFiles` returns. `LinkScalarsAreWritten Zp.p.X`: 24 numbers of the public
record: paid under the head by `linkScalarsAreWrittenUnderTheHead` (LinkScalarsAreWrittenUnderTheHead.lean beside this file,
which stands over this one); LookupThreeTestsUnderTheHeadAlone.lean beside this file joins the two.

Limits. THE MASK ROW's OWNER r' IS WHAT `ownerOf` RETURNS AT THE WRITTEN DESCRIPTION AND THE WRITTEN SENDINGS, NOT AT A's OWN
DESCRIPTION. All limits of the files called hold here. The closed facts have been checked by Lean's own kernel alone. The
full size and the format's second hash function alone.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import AtFullSide.Honest.K3.Term.LookupLevelsUnderTheHead
import Johnson.Desc.ProofFile.Honest.K3.Term.LinkScalarsAreWritten
import Johnson.Desc.First.Look.K3PlaceLetters
import Johnson.Desc.Kinds.Law.K6PubInScope
import Johnson.Desc.ProofFile.Honest.K3.Good.Live.Windows
import Johnson.Desc.ProofFile.Honest.K3.Good.Live.WindowsLay
import Johnson.Desc.ProofFile.Honest.K3.Law.SlotsElems
import Johnson.Goal.Meaning.PlanShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.Honest.K3.Term
open ProofFile ProofFile.Honest ProofFile.Honest.K3 ProofFile.Honest.K3.Law ProofFile.Honest.K3.Term
open VerifiableInference.Desc.K3 (faceOf)
open VerifiableInference.Desc.First.Look (placeAt place_lay place_att place_head)
open VerifiableInference.Desc.Kinds.Head.Law.InScope (head_24 digits_place)
open Johnson.AtFull.Lots.K3 (sortOf firstW nsW)
open AtFullSide.K14 (k3Face k3SitesW)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-! ## 1 Closed facts and small laws -/

/-- At the three sorts of link off the head: first scalar and own scalars add up to the link's. -/
theorem writtenFirstAndSlotsAreTheLinksScalars : ∀ σ, σ < 3 →
    firstW σ true + (k3Face (vdW σ true).1 (vdW σ true).2).slots = nsW σ := by
  decide +kernel

/-- NOT AT THE HEAD: there other scalars stand behind the lookup on the digits. -/
theorem writtenFirstAndSlots_notAtTheHead :
    firstW 3 true + (k3Face (vdW 3 true).1 (vdW 3 true).2).slots ≠ nsW 3 := by
  decide +kernel

/-- A face's number of scalars reads its five numbers alone. -/
theorem slotsOfFiveNumbers {f : LFace} {v d : Nat} (h1 : f.shifted = true) (h2 : f.mu = 5)
    (h3 : f.planes = 32) (h4 : f.parts = [v]) (h5 : f.d = d) : f.slots = (k3Face v d).slots := by
  cases f
  simp only at h1 h2 h3 h4 h5
  subst h1 h2 h3 h4 h5
  rfl

theorem sortOfLinkOffTheHead {l : Nat} (h : l ≠ 24) : sortOf l < 3 := by
  unfold Johnson.AtFull.Lots.K3.sortOf
  rw [if_neg (by simpa using h)]
  split_ifs <;> omega

theorem sortOfOddLink {l : Nat} (h : l ≠ 24) (ho : l % 2 = 1) : sortOf l = 1 := by
  unfold Johnson.AtFull.Lots.K3.sortOf
  rw [if_neg (by simpa using h), if_pos (by simpa using ho)]

/-! ## 2 The first scalar -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **A site's first scalar is the written one.** Conditional: the head; the site; where the site is on the
digits of a link other than 24: the links' numbers of scalars are the written ones. -/
theorem lookupFirstScalarIsWrittenAtASite (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp)
    (hScalars : s.digits = true → s.link ≠ 24 → LinkScalarsAreWritten Zp.p.X) :
    s.p.first = firstW (sortOf s.link) s.digits := by
  have pub : OnBytes.Model.Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X := h.toAtMg.pubOne
  obtain ⟨h4, hN⟩ := head_24 h.scope pub
  have hl := AtThr.link_lt_head h s hs
  have hs' := hs
  unfold lookSites at hs'
  obtain ⟨y, -, hsy⟩ := List.mem_filterMap.1 hs'
  obtain ⟨f1, f2, f3, f4, -, f6, -, -⟩ := site_facts _ _ y s hsy
  rw [← f3, ← f4] at f1
  have e24 : (if Zp.p.X.p4 then 2 else 1) * Zp.p.X.NGr = 24 := by rw [h4, hN]; rfl
  have e2 : (if Zp.p.X.p4 then 2 else 1) = 2 := by rw [h4]; rfl
  obtain ⟨n2, n3⟩ := lookupLevelsAreWrittenUnderTheHead h s hs
  have hslots : (faceOf s.shape).slots =
      (k3Face (vdW (sortOf s.link) s.digits).1 (vdW (sortOf s.link) s.digits).2).slots :=
    slotsOfFiveNumbers rfl rfl rfl (by rw [← n2]; rfl) (by rw [← n3]; rfl)
  cases hd : s.digits with
  | false =>
    rw [hd] at f1
    show s.p.first = 0
    by_cases h24 : s.link = 24
    · rw [h24, ← e24] at f1
      exact (place_head pub f1).2.2.1
    · by_cases hev : s.link % 2 = 0
      · obtain ⟨_, _, _, _, e, _⟩ := place_lay pub f1 (by rw [e24]; exact h24) (by rw [e2]; exact hev)
        exact e
      · obtain ⟨_, _, _, _, e, _⟩ := place_att pub f1 (by rw [e24]; exact h24) (by rw [e2]; exact hev)
        exact e
  | true =>
    rw [hd] at f1 hslots
    by_cases h24 : s.link = 24
    · obtain ⟨p, hp, -, e⟩ := digits_place h.scope h.reads pub
      rw [h24] at f1
      rw [Option.some.inj (f1.symm.trans hp), e, h24]
      rfl
    · have hNs := hScalars hd h24
      have hw := writtenFirstAndSlotsAreTheLinksScalars (sortOf s.link) (sortOfLinkOffTheHead h24)
      by_cases hev : s.link % 2 = 0
      · obtain ⟨hp, hg, e1, e3⟩ := Good.Live.digits_lay pub f1 (by rw [e24]; exact h24)
          (by rw [e2]; exact hev)
        rw [e2] at hg
        rw [Option.some.inj (e1.symm.trans f2), ← Spec.slots_elems, hslots,
          (hNs (s.link / 2) (by omega)).1 hp hg,
          show 2 * (s.link / 2) = s.link by omega] at e3
        omega
      · have hodd : s.link % 2 = 1 := by omega
        obtain ⟨a, ha, -⟩ := (Meaning.scope_plans h.scope h.reads pub).2.2.2 (s.link / 2) (by omega)
        have f1' : placeAt Zp.p.X (2 * (s.link / 2) + 1) true = some s.p := by
          rw [show 2 * (s.link / 2) + 1 = s.link by omega]
          exact f1
        obtain ⟨e1, -, e3⟩ := Good.Live.digits_att pub h4 ha f1'
        rw [Option.some.inj (e1.symm.trans f2), ← Spec.slots_elems, hslots,
          (hNs (s.link / 2) (by omega)).2 a ha] at e3
        rw [sortOfOddLink h24 hodd] at hw e3 ⊢
        omega

end

/-! ## 3 The three tests -/

section
variable {W₀ Rc Tr X₀ X : Type} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place} {P : ProofFile.Honest.OnlineProverParts W₀ Rc Tr X₀ X}
  {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **The three tests at one site, at the book of whatever `onlineProverFromPublicFiles` returns.** Conditional: the head; hA, at any
filling; the site; where the site is on the digits of a link other than 24: the links' numbers of scalars are
the written ones. r' is what `ownerOf` returns at the WRITTEN description and the written sendings, not at A's own
description. -/
theorem lookupThreeTestsAtASite (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (s : Site) (hs : s ∈ lookSites Zp)
    (hScalars : s.digits = true → s.link ≠ 24 → LinkScalarsAreWritten Zp.p.X) :
    ∃ r' : MsgAt,
      ownerOf maskRowRun WP.first.blocksInOrder proofSendsFull.1 (WP.second.blocksInOrder.flatMap (·.rounds))
        s!"link {s.link}, moment 0" isMaskRowMsg = some r' ∧
      bookFits A.B (A.B.rowsOf 0) (dueAt A.B.first) s.at_ = true ∧
      startsFit A.B s.at_ s.p.first r'.owner r'.base = true ∧
      placeFits A.B (A.B.rowsOf 0) s.at_ = true := by
  obtain ⟨B, hB⟩ := AtFullSide.K14.bookWhole_returns_written
  have eB : A.B = B := Except.ok.inj
    ((ProofFile.Honest.K14.atPure_book_at_head h hA).symm.trans
      (ProofFile.Honest.K14.bookWhole_same_at_made hB h))
  rw [eB]
  have hl := AtThr.link_lt_head h s hs
  have hp := AtThr.site_place_head h s hs
  have n1 := lookupFirstScalarIsWrittenAtASite h s hs hScalars
  obtain ⟨n2, n3⟩ := lookupLevelsAreWrittenUnderTheHead h s hs
  obtain ⟨hf, -⟩ := FastLaw.sites_ok Zp s hs
  have hm : (IM.k3Place s.link s.digits, [(vdW (sortOf s.link) s.digits).1],
      (vdW (sortOf s.link) s.digits).2, firstW (sortOf s.link) s.digits) ∈
      k3SitesW.map (fun w => (w.at_.place, w.at_.face.parts, w.at_.face.d, w.first)) := by
    rw [k3SitesW_are]
    exact List.mem_flatMap.2 ⟨s.link, List.mem_range.2 hl,
      List.mem_map.2 ⟨s.digits, by cases s.digits <;> simp, rfl⟩⟩
  obtain ⟨w, hw, e⟩ := List.mem_map.1 hm
  have e1 : w.at_.place = IM.k3Place s.link s.digits := congrArg (·.1) e
  have e2 : w.at_.face.parts = [(vdW (sortOf s.link) s.digits).1] := congrArg (·.2.1) e
  have e3 : w.at_.face.d = (vdW (sortOf s.link) s.digits).2 := congrArg (·.2.2.1) e
  have e4 : w.first = firstW (sortOf s.link) s.digits := congrArg (·.2.2.2) e
  obtain ⟨l, r', hlk, hr, H⟩ := AtFullSide.K14.k3Fits_written hB w hw
  have hl' : l = s.link := by
    rw [e1] at hlk
    exact (Option.some.inj hlk).symm
  subst hl'
  obtain ⟨b1, b2, b3⟩ := H s.at_ (hp.trans e1.symm) (by rw [hf]; rfl) (by rw [hf]; rfl)
    (by rw [hf]; rfl) (by rw [hf, e2, ← n2]; rfl) (by rw [hf, e3, ← n3]; rfl)
  exact ⟨r', hr, b1, by rw [n1, ← e4]; exact b2, b3⟩

/-- **THE THREE TESTS AT EVERY SITE, UNDER THE HEAD AND ONE NAMED PREMISE.** Conditional: the head; hA, at any
filling; the 24 links off the head send the written numbers of scalars. r' is what `ownerOf` returns at the WRITTEN
description and the written sendings, not at A's own description. -/
theorem lookupThreeTestsUnderTheHead (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (hScalars : LinkScalarsAreWritten Zp.p.X) :
    ∀ s ∈ lookSites Zp, ∃ r' : MsgAt,
      ownerOf maskRowRun WP.first.blocksInOrder proofSendsFull.1 (WP.second.blocksInOrder.flatMap (·.rounds))
        s!"link {s.link}, moment 0" isMaskRowMsg = some r' ∧
      bookFits A.B (A.B.rowsOf 0) (dueAt A.B.first) s.at_ = true ∧
      startsFit A.B s.at_ s.p.first r'.owner r'.base = true ∧
      placeFits A.B (A.B.rowsOf 0) s.at_ = true :=
  fun s hs => lookupThreeTestsAtASite h hA s hs fun _ _ => hScalars

/-- **AT 26 OF THE FIFTY SITES: UNDER THE HEAD ALONE**: on the calls, and at link 24. Conditional: the head; hA. -/
theorem lookupThreeTestsAtTheCallsAndTheHeadsDigits (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    ∀ s ∈ lookSites Zp, s.digits = false ∨ s.link = 24 → ∃ r' : MsgAt,
      ownerOf maskRowRun WP.first.blocksInOrder proofSendsFull.1 (WP.second.blocksInOrder.flatMap (·.rounds))
        s!"link {s.link}, moment 0" isMaskRowMsg = some r' ∧
      bookFits A.B (A.B.rowsOf 0) (dueAt A.B.first) s.at_ = true ∧
      startsFit A.B s.at_ s.p.first r'.owner r'.base = true ∧
      placeFits A.B (A.B.rowsOf 0) s.at_ = true := by
  intro s hs hw
  refine lookupThreeTestsAtASite h hA s hs fun hd h24 => ?_
  rcases hw with hw | hw
  · rw [hd] at hw
    cases hw
  · exact absurd hw h24

/-- **The book lends the mask row at every site**: owner, `bookFits`, `startsFit`. Conditional: the head; hA; the
named premise. r' is what `ownerOf` returns at the WRITTEN description and the written sendings, not at A's own description.
-/
theorem bookLendsTheMaskRowAtEverySite (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (hScalars : LinkScalarsAreWritten Zp.p.X) :
    ∀ s ∈ lookSites Zp, ∃ r' : MsgAt,
      ProofFile.Honest.ownerOf maskRowRun WP.first.blocksInOrder proofSendsFull.1
        (WP.second.blocksInOrder.flatMap (·.rounds)) s!"link {s.link}, moment 0" isMaskRowMsg = some r' ∧
      bookFits A.B (A.B.rowsOf 0) (dueAt A.B.first) s.at_ = true ∧
      startsFit A.B s.at_ s.p.first r'.owner r'.base = true := by
  intro s hs
  obtain ⟨r', h1, h2, h3, -⟩ := lookupThreeTestsUnderTheHead h hA hScalars s hs
  exact ⟨r', h1, h2, h3⟩

end

end AtFullSide.Honest.K3.Term

#print axioms AtFullSide.Honest.K3.Term.writtenFirstAndSlotsAreTheLinksScalars
#print axioms AtFullSide.Honest.K3.Term.writtenFirstAndSlots_notAtTheHead
#print axioms AtFullSide.Honest.K3.Term.slotsOfFiveNumbers
#print axioms AtFullSide.Honest.K3.Term.sortOfLinkOffTheHead
#print axioms AtFullSide.Honest.K3.Term.sortOfOddLink
#print axioms AtFullSide.Honest.K3.Term.lookupFirstScalarIsWrittenAtASite
#print axioms AtFullSide.Honest.K3.Term.lookupThreeTestsAtASite
#print axioms AtFullSide.Honest.K3.Term.lookupThreeTestsUnderTheHead
#print axioms AtFullSide.Honest.K3.Term.lookupThreeTestsAtTheCallsAndTheHeadsDigits
#print axioms AtFullSide.Honest.K3.Term.bookLendsTheMaskRowAtEverySite
