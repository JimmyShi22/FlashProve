-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/SeatFitsLaw.lean: small theorems on "fits"
(Honest/K3/SeatFits.lean): what an acceptance gives; what the filtered lot lays. Theorems.

Terms. Honest/K3/GLOSSARY.md ("half", "lot", "site"). "Fits" is the Boolean test `k3Fits`; the
filtered lot is the lot that lays a half only where the tests accept (`theLotFit` and its like);
both are defined in SeatFits.lean.

What is shown.
  `rowReadsAt_eq`: where the site's number of rounds in front is the chain's own count, the test at
    the seat is the test on the face alone.
  `fits_gives`: an acceptance of `k3Fits` gives, by name: `siteFits`, `rowReadsAt`, the face's own
    test, the test on the plan's entries, `shapeIsFs`, the two tests on the shape and on the slots
    in use, the library's test on the shape's numbers, `planFits`.
  `plan_of_fits`: so the list's first member at the site's place passes its own test on the plan.
  `fit_only`: the filtered lot lays a half only where "fits" accepts.
  `fit_none`: it lays none where a test on the lot rejects.
  `fit_all`: where all tests accept, its halves are the lot's own: no theorem on the lot is affected
    there.
  `keeps_lotBy`, `lotFits_lotBy`: at a row's lot (`lotBy`): a half at a site is kept where all sites
    pass "fits"; the tests on the lot accept where the first two do and the fourth, the letter made,
    is laid as true: the third accepts by the lot's own text.
  `theLotFit_all`, `theLotSpecFit_all`: the last at the two lots of Honest/K3/LotFilled.lean.

Hypotheses that remain.
  `h`: (in `rowReadsAt_eq`) the chain's own count of rounds in front is the site's; (in
    `fits_gives`, `plan_of_fits`) `k3Fits` accepts; (in `fit_none`, `fit_all`) `lotFits` rejects, or
    accepts.
  `hh`: (in `fit_only`) h is a half of the filtered lot. `hk`: (in `fit_all`) every half is kept.
  `hs`: every site passes `k3Fits`. `h1`, `h2`: the table of places is there; no lookup is missed.
  `hm`: the letter made accepts at Z.

Users. This file is imported by Honest/K3/Law/Thread/HalfOfLot.lean and
Honest/K3/Law/Thread/RestOfFits.lean.

Limits. The statements are on the tests as Boolean functions and on lists of halves. No instance of
these hypotheses is exhibited in this file.
Honest/K3/SeatFitsAtZ7.lean
[not in this library] writes a synthetic public part as a literal and evaluates `k3Fits` there: it
accepts at all ten sites (by evaluation).
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.SeatFits
import Johnson.Desc.ProofFile.Honest.K3.Law.SiteFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open VerifiableInference.Desc (Block)

variable {S Cl V W X W₀ Rc Xi Tr : Type}

/-- Conditional on the number of rounds in front being the chain's own count: the test at the seat
is the test on the face alone. No instance of these hypotheses is exhibited in this file. -/
theorem rowReadsAt_eq (bs : List (Block S Cl)) (a : At)
    (h : roundsInFront bs a.place = some a.base) : rowReadsAt bs a = rowReads a.face := by
  unfold rowReadsAt rowReads rowReadsBy
  congr 1
  funext s
  congr 1
  funext x
  unfold readsInFront
  rw [h]
  exact decide_eq_decide.2 (by omega)

/-- **Conditional on an acceptance of `k3Fits`: nine tests accept, by name.** No instance of these
hypotheses is exhibited in this file. -/
theorem fits_gives (Z : Pub) (bs : List (Block S Cl)) (s : Site) (h : k3Fits Z bs s = true) :
    siteFits bs s = true ∧ rowReadsAt bs s.at_ = true ∧ s.at_.face.ok = true ∧
      VerifiableInference.Desc.K3.entriesFit s.at_.face (s.p.entries.getD []) = true ∧
      shapeIsFs Z.p.X s = true ∧
      (s.digits || s.caller != .layers ||
        VerifiableInference.Desc.First.Look.sameShape s.shape Z.p.X.y.fo) = true ∧
      (!s.digits || s.caller == .head ||
        usedAt Z.p.X s == some (s.p.first + s.at_.face.slots)) = true ∧
      FoNums.ok s.shape = true ∧ planFits bs s = true := by
  simp only [k3Fits, k3Tests, seatTests, seatTestsAt, planTests, planTestsAt, publicTests,
    shapeTests, List.all_append, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨a1, a2, _, _, a5, _, a7, a8⟩, _⟩, b1, b2, b3, _⟩, c1⟩, _, _, _, _, d5⟩, _⟩ := h
  refine ⟨?_, a5, a7, a8, b1, b2, b3, c1, d5⟩
  unfold siteFits
  rw [Bool.and_eq_true]
  exact ⟨a1, a2⟩

/-- **Where "fits" accepts, the first member of the list at the site's place passes its own test on
the plan.** Conditional on `k3Fits`. -/
theorem plan_of_fits (Z : Pub) (bs : List (Block S Cl)) (s : Site) (h : k3Fits Z bs s = true) :
    ∃ m, bs.find? (fun b => b.place == s.at_.place) = some m ∧ m.planOk = true := by
  have h9 := (fits_gives Z bs s h).2.2.2.2.2.2.2.2
  unfold planFits at h9
  cases hm : bs.find? (fun b => b.place == s.at_.place) with
  | none =>
    rw [hm] at h9
    exact nomatch h9
  | some m =>
    rw [hm] at h9
    exact ⟨m, rfl, h9⟩

/-- **The filtered lot lays a half only where "fits" accepts**: at each of its halves' places stands
a site at which all tests accept; the tests on the lot accept; and the half is one of the lot's
own. -/
theorem fit_only (bsOf : Pub → List (Block S Cl)) (made : Pub → Bool) (L : HLot V W X) (Z : Pub)
    (G : Ground) (h : Placed V W X) (hh : h ∈ (fitHalves bsOf made L).halves Z G) :
    h ∈ L.halves Z G ∧ lotFits Z (L.halves Z G).length (made Z) = true ∧
      ∃ s ∈ lookSites Z, s.at_.place = h.place ∧ k3Fits Z (bsOf Z) s = true := by
  have hh' : h ∈ (if lotFits Z (L.halves Z G).length (made Z) then
      (L.halves Z G).filter (keeps Z (bsOf Z)) else []) := hh
  split at hh'
  · rename_i hl
    obtain ⟨h1, h2⟩ := List.mem_filter.1 hh'
    unfold keeps at h2
    rw [Bool.and_eq_true] at h2
    obtain ⟨s, hs, e⟩ := List.any_eq_true.1 h2.1
    have e' : s.at_.place = h.place := beq_iff_eq.1 e
    have k := List.all_eq_true.1 h2.2 s hs
    rw [e', bne_self_eq_false, Bool.false_or] at k
    exact ⟨h1, hl, s, hs, e', k⟩
  · exact absurd hh' (List.not_mem_nil)

/-- Conditional on a test on the lot rejecting: the filtered lot lays no half. No instance of these
hypotheses is exhibited in this file. -/
theorem fit_none (bsOf : Pub → List (Block S Cl)) (made : Pub → Bool) (L : HLot V W X) (Z : Pub)
    (G : Ground) (h : lotFits Z (L.halves Z G).length (made Z) = false) :
    (fitHalves bsOf made L).halves Z G = [] := by
  show (if lotFits Z (L.halves Z G).length (made Z) then
    (L.halves Z G).filter (keeps Z (bsOf Z)) else []) = []
  rw [h]
  rfl

/-- **Conditional on the tests on the lot accepting and every half being kept: the filtered lot's
halves are the lot's own.** No instance of these hypotheses is exhibited in this file. -/
theorem fit_all (bsOf : Pub → List (Block S Cl)) (made : Pub → Bool) (L : HLot V W X) (Z : Pub)
    (G : Ground) (h : lotFits Z (L.halves Z G).length (made Z) = true)
    (hk : ∀ x ∈ L.halves Z G, keeps Z (bsOf Z) x = true) :
    (fitHalves bsOf made L).halves Z G = L.halves Z G := by
  show (if lotFits Z (L.halves Z G).length (made Z) then
    (L.halves Z G).filter (keeps Z (bsOf Z)) else []) = _
  rw [h, if_pos rfl]
  exact List.filter_eq_self.2 hk

/-- A half that a row's lot lays at a site at which all tests accept is kept. -/
theorem keeps_lotBy (Z : Pub) (bs : List (Block S Cl)) (row : Site → List (Part V W X))
    (G : Ground) (hs : ∀ s ∈ lookSites Z, k3Fits Z bs s = true) :
    ∀ x ∈ (lotBy row).halves Z G, keeps Z bs x = true := by
  intro x hx
  obtain ⟨s, h1, rfl⟩ := List.mem_map.1 (show x ∈ (lookSites Z).map _ from hx)
  unfold keeps
  rw [Bool.and_eq_true]
  refine ⟨List.any_eq_true.2 ⟨s, h1, beq_self_eq_true _⟩, List.all_eq_true.2 fun u hu => ?_⟩
  rw [hs u hu, Bool.or_true]

/-- The tests on the lot at a row's lot, the fourth (the letter made) laid as true: the third
accepts by the lot's own text. -/
theorem lotFits_lotBy (Z : Pub) (row : Site → List (Part V W X)) (G : Ground)
    (h1 : (spotsOf Z.cuts).isSome = true) (h2 : (lookMisses Z).isEmpty = true) :
    lotFits Z ((lotBy row).halves Z G).length true = true := by
  have e : ((lotBy row).halves Z G).length = (lookSites Z).length := by
    show ((lookSites Z).map _).length = _
    rw [List.length_map]
  simp only [lotFits, lotTestsFit, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    beq_iff_eq]
  exact ⟨h1, h2, e⟩

section
variable (bsOf : Pub → List (Block S Cl)) (made : Pub → Bool) (cells : Tr → Cells)
  (weights : W₀ → Weights)
  (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) (G : Ground)

/-- **Conditional on: the table of places can be read; a site for every address; the letter "made"
accepts; "fits" accepts at every site: the filtered lot's halves are those of `theLot`.**
No instance of these hypotheses is exhibited in this file. -/
theorem theLotFit_all (h1 : (spotsOf Z.cuts).isSome = true) (h2 : (lookMisses Z).isEmpty = true)
    (hm : made Z = true) (hs : ∀ s ∈ lookSites Z, k3Fits Z (bsOf Z) s = true) :
    (theLotFit (Rc := Rc) (X := X) bsOf made cells weights req).halves Z G =
      (theLot (Rc := Rc) (X := X) cells weights req).halves Z G :=
  fit_all bsOf made _ Z G (by rw [hm]; exact lotFits_lotBy Z _ G h1 h2)
    (keeps_lotBy Z (bsOf Z) _ G hs)

/-- The same at the specification's summands. No instance of these hypotheses is exhibited in this
file. -/
theorem theLotSpecFit_all (h1 : (spotsOf Z.cuts).isSome = true)
    (h2 : (lookMisses Z).isEmpty = true) (hm : made Z = true)
    (hs : ∀ s ∈ lookSites Z, k3Fits Z (bsOf Z) s = true) :
    (theLotSpecFit (Rc := Rc) (X := X) bsOf made cells weights req).halves Z G =
      (theLotSpec (Rc := Rc) (X := X) cells weights req).halves Z G :=
  fit_all bsOf made _ Z G (by rw [hm]; exact lotFits_lotBy Z _ G h1 h2)
    (keeps_lotBy Z (bsOf Z) _ G hs)

end

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.rowReadsAt_eq
#print axioms ProofFile.Honest.K3.Law.fits_gives
#print axioms ProofFile.Honest.K3.Law.plan_of_fits
#print axioms ProofFile.Honest.K3.Law.fit_only
#print axioms ProofFile.Honest.K3.Law.fit_none
#print axioms ProofFile.Honest.K3.Law.fit_all
#print axioms ProofFile.Honest.K3.Law.keeps_lotBy
#print axioms ProofFile.Honest.K3.Law.lotFits_lotBy
#print axioms ProofFile.Honest.K3.Law.theLotFit_all
#print axioms ProofFile.Honest.K3.Law.theLotSpecFit_all
