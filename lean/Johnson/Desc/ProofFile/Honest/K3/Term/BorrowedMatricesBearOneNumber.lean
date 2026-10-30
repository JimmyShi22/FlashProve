-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/BorrowedMatricesBearOneNumber.lean: the honest side of the kind
"lookup" (K3): a matrix that a link borrows holds, in the reader of the honest trace, the entries that
its owner holds, and the honest trace is small and is 0 outside the plans' shapes.

What is borrowed. By the plans' marks (Johnson/HonestTrace/PlanMarks.lean) there are 24 borrowed
matrices, every one with first column 0: qa at each attention link 2 g + 1, owned by link 2 g under
the name qa; xbI at each link 2 g with 0 < g, owned by link 2 (g - 1) under the name xbO; xbL at link
24, owned by link 22 under the name xbO. everyBorrowedMatrixIsOneOfThree says that there are no others,
and theBorrowedEntriesStandInTheLists that these do stand there.

What is shown. X is what publicOf returns at files in the goals' scope. The index i and the request x
are any: the first three laws do not ask that the request be served.
  attentionReadsTheQaOfItsGroup, groupReadsTheStreamOfTheGroupBefore, headReadsTheStreamOfTheLastGroup:
    the reader cellOf X (theTrace X i x) answers the same under the borrower's link and label as under
    the owner's link and name, at every row and column.
  qaBearsOneNumberAtTheHonestCells: the first of these in the form that eSyms_of_laysCells asks as hqa
    (Honest/K5/Law/LaysCells.lean).
  borrowerReadsWhatItsOwnerHolds: at every entry of a link's list, borrowed or not, at a served request:
    the cell under the entry's own name is the cell under its owner's link and name, shifted by ttOff.
  traceCellsAreBelow129, traceCellsAreSmall: every entry of the trace, the planes' too, at a served
    request.
  traceIsZeroOutsideTheShapes: at every public part, index and request.

Not claimed: that a prover lays these cells; that a verifier's block accepts; anything on soundness,
completeness or zero knowledge.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.WitOwnerFull
import Johnson.HonestTrace.CellOfAt
import Johnson.HonestTrace.PlanLabelsOfMarks
import Johnson.HonestTrace.PlanOwnersInScope
import Johnson.Goal.HonestTrace.PlanMarksInScope
import Johnson.Goal.HonestTrace.FromCellsInScope
import Johnson.Goal.HonestTrace.FullPlanesInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open OnBytes.HonestTrace (cellOf theTrace ServesAt Tr NamesFit MeetsAll PartsFit PlanMarks Seg MatName
  InShape labelAt cellOf_label planMats)
open OnBytes.Model.Verify (publicOf)
open OnBytes.Model.Layer (matIx)
open Inst.Model (Instance ppref ScalesAndPolicy)

section General
variable {X : OnBytes.Model.Verify.Public} {i : Cm.Idx} {x : Instance ppref} {T : Tr}

/-- The reader answers, under the label of matrix number a of link k, the entry of T there. -/
theorem cellUnderItsOwnLabelIsTheEntry (N : NamesFit X T) {k a : ℕ} (hk : k < 25) {s : String}
    (hl : labelAt X k a = some s) (r c : ℕ) :
    cellOf X T k s r c = ((T k a r c : ℤ) : Cb.Gl.F) := by
  obtain ⟨σ, hσ⟩ := OnBytes.HonestTrace.seg_of_lt hk
  obtain ⟨hb, hno⟩ := Seg.of_ofNo hσ
  have p1 := (OnBytes.HonestTrace.parts_at N.parts hσ).1
  unfold labelAt at hl
  rw [hσ] at hl
  simp only [Option.bind_some, p1] at hl
  cases hμ : (MatName.all 3 1 1 4 σ)[a]? with
  | none =>
    rw [hμ] at hl
    exact absurd hl (by simp)
  | some μ =>
    rw [hμ] at hl
    obtain rfl : μ.label = s := by simpa using hl
    have e := cellOf_label N.parts T hb (OnBytes.HonestTrace.all_no_ref σ hμ) r c
    rwa [hno] at e

/-- **At every entry of a link's list the cell under the entry's own name is the cell under its
owner's link and name, shifted by the entry's first column.** An entry that is not borrowed is its
own owner. -/
theorem borrowerReadsWhatItsOwnerHoldsOfBundles (B : PlanLabels X) (O : PlanOwners X)
    (N : NamesFit X T) (M : MeetsAll X i x T) {k a : ℕ} (hk : k < 25) {E : OnBytes.Model.TMat}
    (hE : (tlOf X k).mats[a]? = some E) (r c : ℕ) :
    cellOf X T k E.name r c =
      cellOf X T (ownerOf X k E).1 (ownerOf X k E).2 r (E.ttOff + c) := by
  have hl : labelAt X k a = some E.name := by
    rw [← B.names k hk a]
    unfold nameAt
    rw [hE]
    rfl
  rw [cellUnderItsOwnLabelIsTheEntry N hk hl, cellOf_owner O N M hk hE]

/-- **Every borrowed entry is one of three**, by the plans' marks: its first column is 0, and it is
qa at an attention link, xbI at a later group's link, or xbL at the head. -/
theorem everyBorrowedMatrixIsOneOfThree (Mk : PlanMarks X) {k a : ℕ} (hk : k < 25)
    {E : OnBytes.Model.TMat} (hE : (tlOf X k).mats[a]? = some E) (hB : E.kind = 1) :
    E.ttOff = 0 ∧
      ((∃ g, g < 12 ∧ k = 2 * g + 1 ∧ a = 4 ∧ E.name = "qa" ∧ ownerOf X k E = (2 * g, "qa")) ∨
       (∃ g, 0 < g ∧ g < 12 ∧ k = 2 * g ∧ a = 8 ∧ E.name = "xbI" ∧
          ownerOf X k E = (2 * (g - 1), "xbO")) ∨
       (k = 24 ∧ a = 7 ∧ E.name = "xbL" ∧ ownerOf X k E = (22, "xbO"))) := by
  obtain ⟨σ, hσ⟩ := OnBytes.HonestTrace.seg_of_lt hk
  obtain ⟨hb, hno⟩ := Seg.of_ofNo hσ
  have hm := OnBytes.HonestTrace.mark_at Mk hσ a
  rw [← OnBytes.HonestTrace.tlOf_mats Mk.p4 Mk.groups hk, hE, ← List.getElem?_map] at hm
  cases σ with
  | ff g =>
    have hg : g < 12 := hb
    obtain rfl : 2 * g = k := hno
    rw [OnBytes.HonestTrace.marks_ff g] at hm
    have ha : a < 9 := by
      by_contra hn
      rw [List.getElem?_eq_none (by simpa using hn)] at hm
      exact absurd hm (by simp)
    interval_cases a <;> simp at hm
    all_goals first
      | (exfalso; have := hm.2.1; omega)
      | skip
    by_cases h0 : g = 0
    · rw [if_pos h0] at hm
      simp at hm
      exfalso
      have := hm.2.1
      omega
    · rw [if_neg h0] at hm
      simp at hm
      obtain ⟨e1, -, e3, e4⟩ := hm
      refine ⟨e4, Or.inr (Or.inl ⟨g, by omega, hg, rfl, rfl, e1, ?_⟩)⟩
      exact OnBytes.HonestTrace.ownerOf_borrowed (g := g - 1) (n := 7) (ν := .xbO) Mk (2 * g)
        (by omega) (by omega) rfl hB (by rw [e3, show 1 + (g - 1) = g by omega])
  | att g =>
    have hg : g < 12 := hb
    obtain rfl : 2 * g + 1 = k := hno
    rw [OnBytes.HonestTrace.marks_att g] at hm
    have ha : a < 5 := by
      by_contra hn
      rw [List.getElem?_eq_none (by simpa using hn)] at hm
      exact absurd hm (by simp)
    interval_cases a <;> simp at hm
    all_goals first
      | (exfalso; have := hm.2.1; omega)
      | skip
    obtain ⟨e1, -, e3, e4⟩ := hm
    refine ⟨e4, Or.inl ⟨g, hg, rfl, rfl, e1, ?_⟩⟩
    exact OnBytes.HonestTrace.ownerOf_borrowed (g := g) (n := 6) (ν := .qa) Mk (2 * g + 1) hg
      (by omega) rfl hB e3
  | head =>
    obtain rfl : 24 = k := hno
    rw [OnBytes.HonestTrace.marks_head] at hm
    have ha : a < 8 := by
      by_contra hn
      rw [List.getElem?_eq_none (by simpa using hn)] at hm
      exact absurd hm (by simp)
    interval_cases a <;> simp at hm
    all_goals first
      | (exfalso; have := hm.2.1; omega)
      | skip
    obtain ⟨e1, -, e3, e4⟩ := hm
    refine ⟨e4, Or.inr (Or.inr ⟨rfl, rfl, e1, ?_⟩)⟩
    exact OnBytes.HonestTrace.ownerOf_borrowed (g := 11) (n := 7) (ν := .xbO) Mk 24 (by omega)
      (by omega) rfl hB (by rw [e3])

/-- An entry of kind 1 stands where the marks of the link's list have kind 1. -/
theorem entryOfKindOneStandsWhereItsMarkDoes (Mk : PlanMarks X) {k a : ℕ} (hk : k < 25) {σ : Seg}
    (hσ : Seg.ofNo 12 k = some σ) {l : List (String × ℕ × ℕ × ℕ)}
    (hl : (MatName.all 3 1 1 4 σ).map (OnBytes.HonestTrace.markOf σ) = l) {s : String} {v w : ℕ}
    (hget : l[a]? = some (s, 1, v, w)) :
    ∃ E : OnBytes.Model.TMat, (tlOf X k).mats[a]? = some E ∧ E.kind = 1 := by
  have hm := OnBytes.HonestTrace.mark_at Mk hσ a
  rw [← OnBytes.HonestTrace.tlOf_mats Mk.p4 Mk.groups hk, ← List.getElem?_map, hl, hget] at hm
  cases hE : (tlOf X k).mats[a]? with
  | none =>
    rw [hE] at hm
    simp at hm
  | some E =>
    rw [hE] at hm
    simp at hm
    exact ⟨E, rfl, hm.2.1⟩

/-- **The three borrowed matrices do stand in the lists**: qa at every attention link, xbI at every
later group's link, xbL at the head, each of kind 1. With everyBorrowedMatrixIsOneOfThree this is the
whole list of the 24. -/
theorem theBorrowedEntriesStandInTheLists (Mk : PlanMarks X) :
    (∀ g < 12, ∃ E : OnBytes.Model.TMat, (tlOf X (2 * g + 1)).mats[4]? = some E ∧ E.kind = 1) ∧
    (∀ g, 0 < g → g < 12 →
      ∃ E : OnBytes.Model.TMat, (tlOf X (2 * g)).mats[8]? = some E ∧ E.kind = 1) ∧
    (∃ E : OnBytes.Model.TMat, (tlOf X 24).mats[7]? = some E ∧ E.kind = 1) := by
  refine ⟨fun g hg => ?_, fun g h0 hg => ?_, ?_⟩
  · exact entryOfKindOneStandsWhereItsMarkDoes Mk (by omega) (σ := .att g)
      (Seg.ofNo_no (σ := .att g) hg) (OnBytes.HonestTrace.marks_att g) rfl
  · exact entryOfKindOneStandsWhereItsMarkDoes Mk (by omega) (σ := .ff g)
      (Seg.ofNo_no (σ := .ff g) hg) (OnBytes.HonestTrace.marks_ff g)
      (s := "xbI") (v := g * 256 + 7) (w := 0) (by simp [show g ≠ 0 by omega])
  · exact entryOfKindOneStandsWhereItsMarkDoes Mk (by omega) (σ := .head) rfl
      OnBytes.HonestTrace.marks_head rfl

end General

section InScope
variable {Zl : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : OnBytes.Model.Verify.Public}

/-- **An attention link's qa is its group's.** At every index and every request, served or not. -/
theorem attentionReadsTheQaOfItsGroup (hZ : VerifierAndGoals.InScope Zl = true)
    (hR : VerifierAndGoals.readFiles Zl = .ok pp) (h : publicOf Zl.pol Zl.KL lay = .ok X) (i : Cm.Idx)
    (x : Instance ppref) {g : ℕ} (hg : g < 12) (r c : ℕ) :
    cellOf X (theTrace X i x) (2 * g) "qa" r c =
      cellOf X (theTrace X i x) (2 * g + 1) "qa" r c := by
  have P : PartsFit X := OnBytes.HonestTrace.partsFit_in_scope hZ hR h
  have e0 : cellOf X (theTrace X i x) (2 * g) "qa" r c =
      ((theTrace X i x (2 * g) 6 r c : ℤ) : Cb.Gl.F) :=
    cellOf_label (σ := .ff g) (μ := .qa) P _ hg rfl r c
  have e1 : cellOf X (theTrace X i x) (2 * g + 1) "qa" r c =
      ((theTrace X i x (2 * g + 1) 4 r c : ℤ) : Cb.Gl.F) :=
    cellOf_label (σ := .att g) (μ := .qa) P _ hg rfl r c
  have iQA : (matIx X.y).iQA = 6 := by
    show X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 2 = 6
    rw [P.af, P.ad]
  have s := (OnBytes.HonestTrace.borrowed_in_scope hZ hR h (OnBytes.HonestTrace.plOf X i x) i x).2.1
    g hg r c
  rw [iQA, P.as g hg] at s
  have s' : theTrace X i x (2 * g + 1) 4 r c = theTrace X i x (2 * g) 6 r c := s
  rw [e0, e1, s']

/-- **The stream that enters a later group is the stream that left the group before**: the label xbI
at link 2 g, the name xbO at link 2 (g - 1). -/
theorem groupReadsTheStreamOfTheGroupBefore (hZ : VerifierAndGoals.InScope Zl = true)
    (hR : VerifierAndGoals.readFiles Zl = .ok pp) (h : publicOf Zl.pol Zl.KL lay = .ok X) (i : Cm.Idx)
    (x : Instance ppref) {g : ℕ} (h0 : 0 < g) (hg : g < 12) (r c : ℕ) :
    cellOf X (theTrace X i x) (2 * g) "xbI" r c =
      cellOf X (theTrace X i x) (2 * (g - 1)) "xbO" r c := by
  have P : PartsFit X := OnBytes.HonestTrace.partsFit_in_scope hZ hR h
  have e0 : cellOf X (theTrace X i x) (2 * g) "xbI" r c =
      ((theTrace X i x (2 * g) 8 r c : ℤ) : Cb.Gl.F) :=
    cellOf_label (σ := .ff g) (μ := .xbI) P _ hg rfl r c
  have e1 : cellOf X (theTrace X i x) (2 * (g - 1)) "xbO" r c =
      ((theTrace X i x (2 * (g - 1)) 7 r c : ℤ) : Cb.Gl.F) :=
    cellOf_label (σ := .ff (g - 1)) (μ := .xbO) P _ (show g - 1 < 12 by omega) rfl r c
  have iXO : (matIx X.y).iXO = 7 := by
    show X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 3 = 7
    rw [P.af, P.ad]
  have iXI : (matIx X.y).iXI = 8 := by
    show X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 4 = 8
    rw [P.af, P.ad]
  have s := (OnBytes.HonestTrace.borrowed_in_scope hZ hR h (OnBytes.HonestTrace.plOf X i x) i x).1
    g h0 hg r c
  rw [iXO, iXI] at s
  have s' : theTrace X i x (2 * g) 8 r c = theTrace X i x (2 * (g - 1)) 7 r c := s
  rw [e0, e1, s']

/-- **The head's stream is the stream that left the last group**: the label xbL at link 24, the name
xbO at link 22. -/
theorem headReadsTheStreamOfTheLastGroup (hZ : VerifierAndGoals.InScope Zl = true)
    (hR : VerifierAndGoals.readFiles Zl = .ok pp) (h : publicOf Zl.pol Zl.KL lay = .ok X) (i : Cm.Idx)
    (x : Instance ppref) (r c : ℕ) :
    cellOf X (theTrace X i x) 24 "xbL" r c = cellOf X (theTrace X i x) 22 "xbO" r c := by
  have P : PartsFit X := OnBytes.HonestTrace.partsFit_in_scope hZ hR h
  have e0 : cellOf X (theTrace X i x) 24 "xbL" r c =
      ((theTrace X i x 24 7 r c : ℤ) : Cb.Gl.F) :=
    cellOf_label (σ := .head) (μ := .xbL) P _ trivial rfl r c
  have e1 : cellOf X (theTrace X i x) 22 "xbO" r c =
      ((theTrace X i x 22 7 r c : ℤ) : Cb.Gl.F) :=
    cellOf_label (σ := .ff 11) (μ := .xbO) P _ (show 11 < 12 by omega) rfl r c
  have iXO : (matIx X.y).iXO = 7 := by
    show X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 3 = 7
    rw [P.af, P.ad]
  have s := (OnBytes.HonestTrace.borrowed_in_scope hZ hR h (OnBytes.HonestTrace.plOf X i x) i x).2.2
    r c
  rw [iXO, P.hf] at s
  have s' : theTrace X i x 24 7 r c = theTrace X i x 22 7 r c := s
  rw [e0, e1, s']

/-- **The same as the premise hqa of eSyms_of_laysCells**: wherever a reader of cells is the reader
of the honest trace, it answers the same for qa under both segments' numbers. -/
theorem qaBearsOneNumberAtTheHonestCells (hZ : VerifierAndGoals.InScope Zl = true)
    (hR : VerifierAndGoals.readFiles Zl = .ok pp) (h : publicOf Zl.pol Zl.KL lay = .ok X) (i : Cm.Idx)
    (x : Instance ppref) {g : ℕ} (hg : g < 12) {C : Cells}
    (hC : C = ⟨cellOf X (theTrace X i x)⟩) (r c : ℕ) :
    C.cell (2 * g) "qa" r c = C.cell (2 * g + 1) "qa" r c := by
  subst hC
  exact attentionReadsTheQaOfItsGroup hZ hR h i x hg r c

/-- **Every borrowed entry of a link's list in scope is one of three.** -/
theorem everyBorrowedMatrixInScopeIsOneOfThree (hZ : VerifierAndGoals.InScope Zl = true)
    (hR : VerifierAndGoals.readFiles Zl = .ok pp) (h : publicOf Zl.pol Zl.KL lay = .ok X) {k a : ℕ}
    (hk : k < 25) {E : OnBytes.Model.TMat} (hE : (tlOf X k).mats[a]? = some E)
    (hB : E.kind = 1) :
    E.ttOff = 0 ∧
      ((∃ g, g < 12 ∧ k = 2 * g + 1 ∧ a = 4 ∧ E.name = "qa" ∧ ownerOf X k E = (2 * g, "qa")) ∨
       (∃ g, 0 < g ∧ g < 12 ∧ k = 2 * g ∧ a = 8 ∧ E.name = "xbI" ∧
          ownerOf X k E = (2 * (g - 1), "xbO")) ∨
       (k = 24 ∧ a = 7 ∧ E.name = "xbL" ∧ ownerOf X k E = (22, "xbO"))) :=
  everyBorrowedMatrixIsOneOfThree (OnBytes.HonestTrace.planMarks_in_scope hZ hR h) hk hE hB

/-- **The three borrowed matrices stand in the lists in scope.** -/
theorem theBorrowedEntriesStandInTheListsInScope (hZ : VerifierAndGoals.InScope Zl = true)
    (hR : VerifierAndGoals.readFiles Zl = .ok pp) (h : publicOf Zl.pol Zl.KL lay = .ok X) :
    (∀ g < 12, ∃ E : OnBytes.Model.TMat, (tlOf X (2 * g + 1)).mats[4]? = some E ∧ E.kind = 1) ∧
    (∀ g, 0 < g → g < 12 →
      ∃ E : OnBytes.Model.TMat, (tlOf X (2 * g)).mats[8]? = some E ∧ E.kind = 1) ∧
    (∃ E : OnBytes.Model.TMat, (tlOf X 24).mats[7]? = some E ∧ E.kind = 1) :=
  theBorrowedEntriesStandInTheLists (OnBytes.HonestTrace.planMarks_in_scope hZ hR h)

/-- **The general form, at the honest trace of a served request.** -/
theorem borrowerReadsWhatItsOwnerHolds (hZ : VerifierAndGoals.InScope Zl = true)
    (hR : VerifierAndGoals.readFiles Zl = .ok pp) (h : publicOf Zl.pol Zl.KL lay = .ok X) {i : Cm.Idx}
    {x : Instance ppref} (S : ServesAt X i x) {k a : ℕ} (hk : k < 25) {E : OnBytes.Model.TMat}
    (hE : (tlOf X k).mats[a]? = some E) (r c : ℕ) :
    cellOf X (theTrace X i x) k E.name r c =
      cellOf X (theTrace X i x) (ownerOf X k E).1 (ownerOf X k E).2 r (E.ttOff + c) :=
  borrowerReadsWhatItsOwnerHoldsOfBundles (OnBytes.HonestTrace.planLabels_in_scope hZ hR h)
    (OnBytes.HonestTrace.planOwners_in_scope hZ hR h)
    (OnBytes.HonestTrace.namesFit_theTrace hZ hR h S)
    (OnBytes.HonestTrace.meetsAll_theTrace hZ hR h S) hk hE r c

/-- **Every entry of the honest trace of a served request, the planes' too, is below 129.** -/
theorem traceCellsAreBelow129 (hZ : VerifierAndGoals.InScope Zl = true)
    (hR : VerifierAndGoals.readFiles Zl = .ok pp) (h : publicOf Zl.pol Zl.KL lay = .ok X) {i : Cm.Idx}
    {x : Instance ppref} (S : ServesAt X i x) (l a r c : ℕ) :
    |theTrace X i x l a r c| < 129 :=
  (OnBytes.HonestTrace.meetsAll_theTrace hZ hR h S).small l a r c

/-- **Every entry of the honest trace of a served request is below twice the packing's shift.** -/
theorem traceCellsAreSmall (hZ : VerifierAndGoals.InScope Zl = true)
    (hR : VerifierAndGoals.readFiles Zl = .ok pp) (h : publicOf Zl.pol Zl.KL lay = .ok X) {i : Cm.Idx}
    {x : Instance ppref} (S : ServesAt X i x) (l a r c : ℕ) :
    |theTrace X i x l a r c| < 2 * 2 ^ 17 :=
  lt_trans (traceCellsAreBelow129 hZ hR h S l a r c) (by norm_num)

end InScope

/-- **Outside the plans' shapes the honest trace is 0**, at every public part, index and request. -/
theorem traceIsZeroOutsideTheShapes (X : OnBytes.Model.Verify.Public) (i : Cm.Idx)
    (x : Instance ppref) {k a r c : ℕ} (hn : ¬ InShape X k a r c) :
    theTrace X i x k a r c = 0 :=
  OnBytes.HonestTrace.trFull_out X _ i x hn

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.cellUnderItsOwnLabelIsTheEntry
#print axioms ProofFile.Honest.K3.Term.borrowerReadsWhatItsOwnerHoldsOfBundles
#print axioms ProofFile.Honest.K3.Term.everyBorrowedMatrixIsOneOfThree
#print axioms ProofFile.Honest.K3.Term.attentionReadsTheQaOfItsGroup
#print axioms ProofFile.Honest.K3.Term.groupReadsTheStreamOfTheGroupBefore
#print axioms ProofFile.Honest.K3.Term.headReadsTheStreamOfTheLastGroup
#print axioms ProofFile.Honest.K3.Term.qaBearsOneNumberAtTheHonestCells
#print axioms ProofFile.Honest.K3.Term.everyBorrowedMatrixInScopeIsOneOfThree
#print axioms ProofFile.Honest.K3.Term.borrowerReadsWhatItsOwnerHolds
#print axioms ProofFile.Honest.K3.Term.entryOfKindOneStandsWhereItsMarkDoes
#print axioms ProofFile.Honest.K3.Term.theBorrowedEntriesStandInTheLists
#print axioms ProofFile.Honest.K3.Term.theBorrowedEntriesStandInTheListsInScope
#print axioms ProofFile.Honest.K3.Term.traceCellsAreBelow129
#print axioms ProofFile.Honest.K3.Term.traceCellsAreSmall
#print axioms ProofFile.Honest.K3.Term.traceIsZeroOutsideTheShapes
