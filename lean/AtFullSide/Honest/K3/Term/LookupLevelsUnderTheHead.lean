-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/K3/Term/LookupLevelsUnderTheHead.lean: the kind "lookup" (K3): under the head
(`P5J.AtMgA`, the library's one hypothesis at the full size) ALONE, at every set of public files at
which the head holds: every site's shape has the written number of key levels and the written number
of table levels; so the book of whatever `onlineProverFromPublicFiles` (Honest/AtPure.lean) returns fits every lookup, and
the kind pays (`KindPays`, Honest/Law/ReadyOfSides.lean) wherever every side of the kind K3 is a
lookup's seated row. Four definitions; six closed facts by Lean's kernel on written data alone, three
of them negative tests; seven theorems more.

NO FILLING IS NAMED HERE: every statement with a filling is general in it, so it can be called at the honest
prover's own (`onlineFilling`, E2E/TheHonestProver.lean): LookupKindPaysAtTheTerm.lean beside this file does.

Terms. Honest/K3/GLOSSARY.md ("site", "stage", "face", "book, coins"). The key levels v and the table
levels d: the fields v and d of a site's shape; its face has parts = [v] and d.

What is defined.
  `stageRoundsAt v d`   the stages' numbers of rounds, in order, at the face with v key levels and d
                        table levels (`k3Face`, AtFullSide/K14/RawK3Sites.lean)
  `writtenLevels`       the eight pairs of the written table `vdW` (AtFullSide/Honest/K3/ViewNumbers.lean)
  `onlyTheWrittenSplitGivesTheWrittenRounds view`   a test with code: at each written pair (v, d), of
                        all pairs (v', d') with v' + d' = v + d none but (v, d) itself has, seen through
                        view, the list `stageRoundsAt v d`
  `numberOfWrittenCutsThatAreTheStageRoundsOf table`   a test with code: at how many of the fifty addresses the
                        written cut is `stageRoundsAt` at the table's pair for the link's sort

What is shown.
  `onlyTheWrittenSplit_holds`   [Lean's kernel] the test accepts where the whole list is seen
  `onlyTheWrittenSplit_blunt`   [Lean's kernel] A NEGATIVE TEST: where the list's length alone is seen it
                        refuses: the lengths do not tell the pairs of one sum apart; the lists do
  `writtenCuts_fifty`           [Lean's kernel] at `vdW` the written cut is that list at all fifty
  `writtenCuts_bent`, `writtenCuts_bentBack`   [Lean's kernel] NEGATIVE TESTS: at the table bent to
                        (v + 1, d - 1), and at (v - 1, d + 1), the same sum: at none of the fifty
  `writtenFacesHaveTheThreeNumbers`  [Lean's kernel] the fifty written members' faces are shifted, with
                        mu = 5 and 32 planes
  `stageRoundsOfFiveNumbers`    the stages' numbers of rounds read of a face its five numbers alone
  `length_flatMap_pair`, `stageRoundsAt_length`   that list has 37 + 2 (v + d) members
  `lookupCutIsTheStagesRounds`  the head, a site, a member b of the first chain at the site's place ⊢
                        the maker's cut `partsCut b` is the stages' numbers of rounds at the site's face
  **`lookupLevelsAreWrittenUnderTheHead`**  the head, a site s ⊢ s.shape.v and s.shape.d are the two
                        numbers of `vdW` at the site's link and sort
  `bookFitsEveryLookupUnderTheHead`  the head, hA at any filling ⊢ `BookFitsEveryLookup A.B A.Z`
  `lookupKindPaysUnderTheHead`  the head, hA, `SidesOfKindLookupAreSeats A.Z A.H.first` ⊢
                        `KindPays A.B 0 A.F.first.blocksInOrder A.H.first .K3`
The two forms are defined in Johnson/Desc/ProofFile/Honest/K3/Term/LookupKindPays.lean.

How the levels come. One book B is what `bookWhole` returns at the written description and at the
head's own (`bookWhole_returns_written`, AtFullSide/K14/BookWholeWritten.lean; `bookWhole_same_at_made`,
Honest/K14/BookForAtPure.lean). At the head's description its cut at the site's place is `partsCut` of
the member there (`bookWhole_cut_first`, Honest/Small/CutOfBook.lean), which is the stages' numbers of
rounds at the SITE's face: the member's rounds are the plan's entries, these are the hearing's but for
the work bits (`member_plan_site`, Honest/K3/Law/Thread/SitePays.lean), and the row is cut as the maker
cuts (`cut_stages`, Honest/K3/RowCut.lean). At the written description the same cut is the stages'
numbers of rounds at the WRITTEN face (`k3CutsAt`, AtFullSide/K14/RawK3Sites.lean). So the two lists are
one; their lengths give v + d; the closed fact gives v.

Hypotheses that remain. The head. hA: that `onlineProverFromPublicFiles` returns. The premise on the sides.

Limits. The site's FIRST SCALAR is not had on this road: the third public test on the book
(`startsFit`, Honest/K3/Law/MasksBook.lean) is not spoken of. The closed facts have been checked by
Lean's own kernel alone. The head has a member at `VerifierAndGoals.storedPublicFiles` (`headMember_zFull`,
AtFullSide/Top/HeadMemberAtFull.lean) and wherever the files are in scope, are read, and the verifier's
test on them says yes (`P5J.head_of_live`, Johnson/P5J/HeadOfLive.lean). The full size and the format's
second hash function alone. All limits of the files called hold here.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import AtFullSide.Honest.K3.FitsAtPure
import Johnson.Desc.ProofFile.Honest.Small.CutOfBook
import Johnson.Desc.ProofFile.Honest.K3.RowCut
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.CoverageAtHead
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupKindPays
import Johnson.RunOne.Sound.KeyListsAtFK

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.Honest.K3.Term
open ProofFile ProofFile.Honest ProofFile.Honest.K3 ProofFile.Honest.K3.Law ProofFile.Honest.K3.Term
open VerifiableInference.Desc (KindName Block)
open VerifiableInference.Desc.K3 (entriesV entriesFit)
open Johnson.AtFull.Lots.K3 (sortOf firstW)
open AtFullSide.K14 (k3Face k3SitesW)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-! ## 1 The stages' numbers of rounds, at two numbers -/

/-- **The stages' numbers of rounds**, in order, at the face with v key levels and d table levels. -/
def stageRoundsAt (v d : Nat) : List Nat :=
  (stages (k3Face v d)).map (Stage.rounds (k3Face v d))

/-- The stages' numbers of rounds read of a face its five numbers alone. -/
theorem stageRoundsOfFiveNumbers {f : LFace} {v d : Nat} (h1 : f.shifted = true) (h2 : f.mu = 5)
    (h3 : f.planes = 32) (h4 : f.parts = [v]) (h5 : f.d = d) :
    (stages f).map (Stage.rounds f) = stageRoundsAt v d := by
  cases f
  simp only at h1 h2 h3 h4 h5
  subst h1 h2 h3 h4 h5
  rfl

theorem length_flatMap_pair {α : Type} (f g : Nat → α) (n : Nat) :
    ((List.range n).flatMap fun m => [f m, g m]).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih]
    have e : ([n].flatMap fun m => [f m, g m]).length = 2 := rfl
    omega

/-- That list has 37 + 2 (v + d) members. -/
theorem stageRoundsAt_length (v d : Nat) : (stageRoundsAt v d).length = 37 + 2 * (v + d) := by
  have e : stages (k3Face v d) = [Stage.shift] ++ [Stage.alpha] ++ (List.range 31).map Stage.tie ++
      [Stage.join] ++ ((List.range v).flatMap fun m => [Stage.key 0 m, Stage.keyLine 0 m]) ++
      ((List.range d).flatMap fun l => [Stage.tab l, Stage.tabLine l]) ++
      [Stage.leaves, Stage.zero, Stage.bits] := by
    simp [stages, k3Face]
  unfold stageRoundsAt
  rw [List.length_map, e]
  simp only [List.length_append, List.length_map, List.length_range, length_flatMap_pair,
    List.length_cons, List.length_nil]
  omega

/-! ## 2 The closed facts -/

/-- The eight pairs of the written table. -/
def writtenLevels : List (Nat × Nat) :=
  (List.range 4).flatMap fun σ => [false, true].map fun d => vdW σ d

/-- **A test with code**: at each written pair, of all pairs with the same sum none but the written
one has, seen through view, the written pair's list. -/
def onlyTheWrittenSplitGivesTheWrittenRounds (view : List Nat → List Nat) : Bool :=
  writtenLevels.all fun w => (List.range (w.1 + w.2 + 1)).all fun v =>
    (view (stageRoundsAt v (w.1 + w.2 - v)) != view (stageRoundsAt w.1 w.2)) || v == w.1

set_option maxRecDepth 1000000 in
/-- The test accepts where the whole list is seen. -/
theorem onlyTheWrittenSplit_holds : onlyTheWrittenSplitGivesTheWrittenRounds id = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- BLUNT: where the list's length alone is seen the test refuses. -/
theorem onlyTheWrittenSplit_blunt :
    onlyTheWrittenSplitGivesTheWrittenRounds (fun l => [l.length]) = false := by
  decide +kernel

/-- **A test with code**: at how many of the fifty addresses the written cut is the list at the
table's pair for the link's sort. -/
def numberOfWrittenCutsThatAreTheStageRoundsOf (table : Nat → Bool → Nat × Nat) : Nat :=
  ((List.range 25).flatMap fun l => [false, true].map fun d =>
    (cutsFirstW ++ cutsSharedW ++ cutsSecondW).lookup (IM.k3Place l d) ==
      some (stageRoundsAt (table (sortOf l) d).1 (table (sortOf l) d).2)).count true

set_option maxRecDepth 1000000 in
/-- At the written table: at all fifty. -/
theorem writtenCuts_fifty : numberOfWrittenCutsThatAreTheStageRoundsOf vdW = 50 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- BENT: one key level more, one table level fewer: at none. -/
theorem writtenCuts_bent :
    numberOfWrittenCutsThatAreTheStageRoundsOf (fun σ d => ((vdW σ d).1 + 1, (vdW σ d).2 - 1)) = 0 := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- BENT BACK: one key level fewer, one table level more: at none. -/
theorem writtenCuts_bentBack :
    numberOfWrittenCutsThatAreTheStageRoundsOf (fun σ d => ((vdW σ d).1 - 1, (vdW σ d).2 + 1)) = 0 := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The fifty written members' faces: three of the five numbers. -/
theorem writtenFacesHaveTheThreeNumbers : ∀ w ∈ k3SitesW, w.at_.face.shifted = true ∧
    w.at_.face.mu = 5 ∧ w.at_.face.planes = 32 := by
  decide +kernel

/-! ## 3 Under the head -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **The maker's cut at a lookup's member is the stages' numbers of rounds at the site's face.**
Conditional: the head; the site; the member at the site's place. -/
theorem lookupCutIsTheStagesRounds (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {s : Site}
    (hs : s ∈ lookSites Zp) {b : Block P5J.TS ProofFile.Cl} (hb : b ∈ cF.blocksInOrder)
    (hbp : b.place = s.at_.place) :
    partsCut b = (stages s.at_.face).map (Stage.rounds s.at_.face) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨lot, hlot, hlp⟩ := lot_of_site _ _ _ _ _ Zp Bs base cF _ _ O s hs
  obtain ⟨hr, -, hfit⟩ := AtThr.member_plan_site _ _ _ _ _ Zp Bs base cF _ _ O s hs lot b hlot hlp
    hb (hbp.trans hlp.symm) (IM.plan_flat O h.laid.planOk b hb)
  have e : ((s.p.entries.getD []).map fun e => { e with work := 0 }) = entriesV s.at_.face :=
    eq_of_beq hfit
  have hn : b.rounds.map (·.entry.name) = (entriesV s.at_.face).map (·.name) := by
    rw [hr, ← e, List.map_map, List.map_map]
    rfl
  unfold partsCut
  rw [hbp, (spot_of_site Zp s hs).1, hn]
  exact cut_stages _ (two_le_planes_of_ok _ (Johnson.AtFull.Shape.face_ok_site Zp s hs))

/-- **UNDER THE HEAD ALONE EVERY SITE's KEY LEVELS AND TABLE LEVELS ARE THE WRITTEN ONES.** -/
theorem lookupLevelsAreWrittenUnderTheHead (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (s : Site) (hs : s ∈ lookSites Zp) :
    s.shape.v = (vdW (sortOf s.link) s.digits).1 ∧ s.shape.d = (vdW (sortOf s.link) s.digits).2 := by
  obtain ⟨B, hB⟩ := AtFullSide.K14.bookWhole_returns_written
  have hB' := ProofFile.Honest.K14.bookWhole_same_at_made hB h
  have hl := AtThr.link_lt_head h s hs
  have hp := AtThr.site_place_head h s hs
  obtain ⟨hf, -⟩ := FastLaw.sites_ok Zp s hs
  -- the member of the head's first chain at the site's place
  have hin := AtThr.site_in_written h s hs
  rw [← P5J.At.places_paid h.scope h.reads h.laid] at hin
  obtain ⟨b, hb, hbp⟩ := List.mem_map.1 hin
  -- the written member at that link and sort
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
  obtain ⟨w1, w2, w3⟩ := writtenFacesHaveTheThreeNumbers w hw
  -- the one book's cut there, read twice
  have hcW : B.cuts.lookup b.place =
      some ((stages w.at_.face).map (Stage.rounds w.at_.face)) := by
    rw [hbp, hp, ← e1]
    exact eq_of_beq (List.all_eq_true.1 (AtFullSide.K14.k3CutsAt (bookWhole_cuts hB)) w hw)
  have hpOk : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).placesOk = true :=
    Johnson.RunOne.Sound.placesOk_of_planOk _ h.laid.planOk
  have hbr : b.rounds ≠ [] := by
    intro e0
    have hnone := bookWhole_cut_first_roundless hB' hpOk (b := b) hb e0
    rw [hcW] at hnone
    cases hnone
  have hcB : B.cuts.lookup b.place = some (partsCut b) :=
    bookWhole_cut_first hB' hpOk (b := b) hb hbr
  rw [hcW, lookupCutIsTheStagesRounds h hs hb hbp] at hcB
  have hEq : stageRoundsAt (vdW (sortOf s.link) s.digits).1 (vdW (sortOf s.link) s.digits).2 =
      stageRoundsAt s.shape.v s.shape.d := by
    rw [← stageRoundsOfFiveNumbers w1 w2 w3 e2 e3,
      ← stageRoundsOfFiveNumbers (f := s.at_.face) (by rw [hf]; rfl) (by rw [hf]; rfl)
        (by rw [hf]; rfl) (by rw [hf]; rfl) (by rw [hf]; rfl)]
    exact Option.some.inj hcB
  have hlen := congrArg List.length hEq
  rw [stageRoundsAt_length, stageRoundsAt_length] at hlen
  have hmem : vdW (sortOf s.link) s.digits ∈ writtenLevels :=
    List.mem_flatMap.2 ⟨sortOf s.link, List.mem_range.2 (sortOf_lt _),
      List.mem_map.2 ⟨s.digits, by cases s.digits <;> simp, rfl⟩⟩
  have ht := List.all_eq_true.1 (List.all_eq_true.1 onlyTheWrittenSplit_holds _ hmem) s.shape.v
    (List.mem_range.2 (by omega))
  have hd : (vdW (sortOf s.link) s.digits).1 + (vdW (sortOf s.link) s.digits).2 - s.shape.v =
      s.shape.d := by omega
  rw [hd, ← hEq] at ht
  simp only [bne_self_eq_false, Bool.false_or, beq_iff_eq] at ht
  exact ⟨ht, by omega⟩

end

section
variable {W₀ Rc Tr X₀ X : Type} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place} {P : ProofFile.Honest.OnlineProverParts W₀ Rc Tr X₀ X}
  {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **THE BOOK OF WHATEVER `onlineProverFromPublicFiles` RETURNS FITS EVERY LOOKUP, UNDER THE HEAD ALONE.** Conditional: the
head; hA, at any filling. -/
theorem bookFitsEveryLookupUnderTheHead (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) : BookFitsEveryLookup A.B A.Z := by
  obtain ⟨B, hB⟩ := AtFullSide.K14.bookWhole_returns_written
  have eB : A.B = B := Except.ok.inj
    ((ProofFile.Honest.K14.atPure_book_at_head h hA).symm.trans
      (ProofFile.Honest.K14.bookWhole_same_at_made hB h))
  rw [(atPure_at_laid h.laid hA).1, eB]
  intro s hs
  have hl := AtThr.link_lt_head h s hs
  have hp := AtThr.site_place_head h s hs
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
  obtain ⟨_, _, -, -, H⟩ := AtFullSide.K14.k3Fits_written hB w hw
  obtain ⟨b1, -, b3⟩ := H s.at_ (hp.trans e1.symm) (by rw [hf]; rfl) (by rw [hf]; rfl)
    (by rw [hf]; rfl) (by rw [hf, e2, ← n2]; rfl) (by rw [hf, e3, ← n3]; rfl)
  exact ⟨b1, b3⟩

/-- **THE KIND "LOOKUP" PAYS AT WHATEVER `onlineProverFromPublicFiles` RETURNS, UNDER THE HEAD ALONE.** Conditional: the head;
hA; every side of the kind in A's first list is a seat. -/
theorem lookupKindPaysUnderTheHead (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (hSides : SidesOfKindLookupAreSeats A.Z A.H.first) :
    KindPays A.B 0 A.F.first.blocksInOrder A.H.first KindName.K3 :=
  lookupKindPays h hA (bookFitsEveryLookupUnderTheHead h hA) hSides

end

end AtFullSide.Honest.K3.Term

#print axioms AtFullSide.Honest.K3.Term.stageRoundsOfFiveNumbers
#print axioms AtFullSide.Honest.K3.Term.length_flatMap_pair
#print axioms AtFullSide.Honest.K3.Term.stageRoundsAt_length
#print axioms AtFullSide.Honest.K3.Term.onlyTheWrittenSplit_holds
#print axioms AtFullSide.Honest.K3.Term.onlyTheWrittenSplit_blunt
#print axioms AtFullSide.Honest.K3.Term.writtenCuts_fifty
#print axioms AtFullSide.Honest.K3.Term.writtenCuts_bent
#print axioms AtFullSide.Honest.K3.Term.writtenCuts_bentBack
#print axioms AtFullSide.Honest.K3.Term.writtenFacesHaveTheThreeNumbers
#print axioms AtFullSide.Honest.K3.Term.lookupCutIsTheStagesRounds
#print axioms AtFullSide.Honest.K3.Term.lookupLevelsAreWrittenUnderTheHead
#print axioms AtFullSide.Honest.K3.Term.bookFitsEveryLookupUnderTheHead
#print axioms AtFullSide.Honest.K3.Term.lookupKindPaysUnderTheHead
