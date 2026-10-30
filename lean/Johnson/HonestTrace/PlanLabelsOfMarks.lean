-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HonestTrace/PlanLabelsOfMarks.lean

From two conditions on a public part X, PlanMarks X (Johnson/HonestTrace/PlanMarks.lean) and
PartsFit X (Johnson/HonestTrace/FromCells.lean), to the public premise PlanLabels X of the lookup's
honest side (Johnson/Desc/ProofFile/Honest/K3/WitPlan.lean), and to the equation of two lists that
say where the matrices of a sub-proof's list are read: matsOwn
(Johnson/Desc/ProofFile/Honest/K3/WitOwner.lean), which goes by the kinds and identifiers in the
verifier's plan, and matsOf (Johnson/HonestTrace/DigitsAtTrace.lean), which goes by the matrices'
names.

Main theorems:
* "planLabels_of_marks": under PlanMarks X and PartsFit X: PlanLabels X.
* "matsOwn_of_marks": under PlanMarks X, PartsFit X and k < 25: matsOwn X k = matsOf X k.
  "planOwners_of_marks": the same in closed form: for every k < 25.
* "matsOf_length_plan": under the same: matsOf X k has as many members as the list of matrices of
  tlOf X k.
* "zzOwn_eq_zzFull": under the same, for all cells C and all sampled entries ts: zzOwn X k C ts =
  zzFull X k C ts (WitOwner.lean; Johnson/Desc/ProofFile/Honest/K3/WitDigits.lean).
* "partsFit_of_labels": under PlanMarks X and PlanLabels X: PartsFit X. "marks_without_labels":
  under PlanMarks X: X with X.hS.NHf set to 5 has PlanMarks and has not PlanLabels.

Beside them:
* "stepOf_two", "tlOf_mats": where X.p4 = true: stepOf X = 2; where besides X.NGr = 12, for k < 25:
  the list of matrices of tlOf X k is planMats X k (Johnson/HonestTrace/Full.lean).
* "mark_at", "nameAt_of_marks": under PlanMarks X, at a segment σ with the number k: entry a of the
  plan's list has the four marks markOf σ at name number a of MatName.all 3 1 1 4 σ; its name is
  that name's label. Both lists end together.
* "ownerOf_borrowed", "own_of_mark": what ownerOf yields at an entry with the marks of a borrowed
  matrix; at an entry with the marks markOf σ μ.
* "lt_of_ofNo": a number that Seg.ofNo 12 takes to a segment is below 25. "length_of_getElem?_map",
  "ff_parts": two steps of the proof of partsFit_of_labels.

On the closed form. The end of planOwners_of_marks, "for every k < 25, matsOwn X k = matsOf X k", is
the text of the public hypothesis PlanOwners X of the lookup's honest side
(Johnson/Desc/ProofFile/Honest/K3/Law/WitOwnerFull.lean). That file is not imported here, and no
file that this one imports takes the equation as a premise.
Johnson/HonestTrace/PlanOwnersInScope.lean states it under that name, for public files in the goals'
scope.

Why PartsFit. PlanLabels and matsOf go by labelAt and MatName.all at X's own numbers of parts;
PlanMarks speaks of the list at the numbers 3, 1, 1, 4. PartsFit X says that X's numbers are these.
nameAt_of_marks, which does not name X's numbers, stands without it. Where any X has PlanMarks,
PlanMarks alone does not give PlanLabels ("marks_without_labels"): PlanMarks does not look at X.hS,
where the count of the head's parts is kept, so an X with PlanMarks X keeps it when X.hS.NHf is set
to 5, and PlanLabels fails there. Of the three other counts no such example is given in this file.
By partsFit_of_labels PartsFit X is no more than PlanLabels X needs beside
PlanMarks X; whether the equation of the two lists needs it is not stated.

Limits. PlanMarks X and PartsFit X are premises: this file shows them of no X. All is at 12 groups
and the numbers of parts 3, 1, 1, 4. The theorems are equations between public data, and between two
terms that read cells through one list: nothing is said on what a reader of cells answers under an
owner's segment and name. Of the fillings ownSources (WitOwner.lean) and theSources (WitDigits.lean)
the two arrays of digits that their fields digits take (zzOwn, zzFull) are compared, for k < 25, and
nothing else: no equation between two fields is stated here, and the fields layers, attention and
head are not compared: by their texts ownSources asks for an entry of kind 1 under ownerOf's segment
and name, theSources for every entry under the sub-proof's own number and labelAt's label. NOT SHOWN
HERE EITHER: that the list at which the smallness test's own part, or a sender of the array ZZ,
reads the matrices is this list: the theorems join two texts of the lookup's side alone; any
equation with the third list matsAt or its array zzPlan (WitDigits.lean): matsAt names the sub-proof
itself at every entry; anything on the entries' other fields (rows, columns, foreign, wp), so that
an owner's and a borrower's matrix have one shape; that a verifier's run uses the identifier as
ownership: the marks are fields of plans; whether zzOwn or zzFull is an honest array of digits: the
equation holds at all cells and all sampled entries; anything from k = 25 on, so no equation between
the two fields digits as functions of every number. This file can be built only where the files
under Johnson/Desc/ProofFile/Honest/K3/ lie, WitOwner.lean, WitDigits.lean and what they import.

Not claimed: anything on a prover, on what a verifier accepts, or on a property of the protocol.
-/
import Johnson.HonestTrace.PlanMarks
import Johnson.HonestTrace.DigitsAtTrace
import Johnson.Desc.ProofFile.Honest.K3.WitOwner
import Johnson.Desc.ProofFile.Honest.K3.WitDigits

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open ProofFile.Honest (Cells)
open ProofFile.Honest.K3 (PlanLabels nameAt tlOf tlOf_eq matsOwn zzOwn zzFull ownerOf ownerOf_own stepOf
  linkG linkH)
open OnBytes.Model (TMat)

variable {X : Model.Verify.Public}

/-- Where attention sub-proofs stand between the groups' (X.p4 = true): stepOf X = 2. -/
theorem stepOf_two (h4 : X.p4 = true) : stepOf X = 2 := by
  unfold stepOf
  rw [h4]
  rfl

/-- Where X.p4 = true and X.NGr = 12, for k < 25: the list of matrices of tlOf X k, which goes by
stepOf X and X.NGr, is planMats X k, which goes by 2 and 24. -/
theorem tlOf_mats (h4 : X.p4 = true) (hG : X.NGr = 12) {k : ℕ} (hk : k < 25) :
    (tlOf X k).mats = planMats X k := by
  have hs := stepOf_two h4
  have hH : linkH X = 24 := by unfold linkH; rw [hs, hG]
  unfold tlOf planMats
  rw [hH, hs, if_neg (by omega : ¬ 24 < k)]
  by_cases h1 : k = 24
  · simp [h1]
  · by_cases h2 : k % 2 = 0 <;> simp [h1, h2]

/-- Under PlanMarks X, at a segment σ with the number k: the four marks of entry a of the plan's
list are markOf σ at name number a of the segment's list; where one list has no entry a, neither has
the other. -/
theorem mark_at (M : PlanMarks X) {k : ℕ} {σ : Seg} (hσ : Seg.ofNo 12 k = some σ) (a : ℕ) :
    ((planMats X k)[a]?).map (fun M => (M.name, M.kind, M.aId, M.ttOff)) =
      ((MatName.all 3 1 1 4 σ)[a]?).map (markOf σ) := by
  have h := congrArg (fun l => l[a]?) (M.marks k σ hσ)
  simpa only [List.getElem?_map, Array.getElem?_toList] using h

/-- A number that Seg.ofNo 12 takes to a segment is below 25. -/
theorem lt_of_ofNo {k : ℕ} {σ : Seg} (hσ : Seg.ofNo 12 k = some σ) : k < 25 := by
  unfold Seg.ofNo at hσ
  by_cases h1 : k = 2 * 12
  · omega
  · rw [if_neg h1] at hσ
    by_cases h2 : 2 * 12 < k
    · rw [if_pos h2] at hσ
      exact absurd hσ (by simp)
    · omega

/-- Under PlanMarks X, at a segment σ with the number k: the name of entry a of the list of tlOf X k
is the label of name number a of MatName.all 3 1 1 4 σ; none where that list has no such number. -/
theorem nameAt_of_marks (M : PlanMarks X) {k : ℕ} {σ : Seg} (hσ : Seg.ofNo 12 k = some σ) (a : ℕ) :
    nameAt (tlOf X k).mats a = ((MatName.all 3 1 1 4 σ)[a]?).map MatName.label := by
  rw [tlOf_mats M.p4 M.groups (lt_of_ofNo hσ)]
  have h := congrArg (Option.map fun q : String × ℕ × ℕ × ℕ => q.1) (mark_at M hσ a)
  rw [Option.map_map, Option.map_map] at h
  exact h

/-- **Under PlanMarks X and PartsFit X: PlanLabels X**: attention sub-proofs stand between the
groups', there are twelve groups, and at each k < 25 entry a of the plan's list bears the label that
labelAt X k gives the number a, none where labelAt gives none. -/
theorem planLabels_of_marks (M : PlanMarks X) (N : PartsFit X) : PlanLabels X := by
  refine ⟨M.p4, M.groups, fun k hk a => ?_⟩
  obtain ⟨σ, hσ⟩ := seg_of_lt hk
  have p1 := (parts_at N hσ).1
  rw [nameAt_of_marks M hσ a]
  unfold labelAt
  rw [hσ]
  simp only [Option.bind_some, p1]

/-- Under PlanMarks X: an entry M of kind 1 whose identifier is (1 + g) * 256 + n, with g < 12, n <
256 and ν the name number n of a group's list at the numbers of parts 3, 1, 1, 4, is read by
ownerOf at the segment number 2 g under ν's label, whatever the link k. That list has nine names, so
beside hν the premise n < 256 asks nothing more. -/
theorem ownerOf_borrowed (Mk : PlanMarks X) (k : ℕ) {M : TMat} {g n : ℕ} {ν : MatName}
    (hg : g < 12) (hn : n < 256) (hν : (MatName.all 3 1 1 4 (.ff g))[n]? = some ν)
    (hk : M.kind = 1) (hid : M.aId = (1 + g) * 256 + n) : ownerOf X k M = (2 * g, ν.label) := by
  have e1 : M.aId / 256 - 1 = g := by omega
  have e2 : M.aId % 256 = n := by omega
  have hl : linkG X g = 2 * g := by unfold linkG; rw [stepOf_two Mk.p4]
  have hσ : Seg.ofNo 12 (2 * g) = some (.ff g) := Seg.ofNo_no (σ := .ff g) hg
  unfold ownerOf
  rw [hk, if_pos (by rfl : ((1 : ℕ) == 1) = true), e1, e2, hl, nameAt_of_marks Mk hσ n, hν]
  rfl

/-- Under PlanMarks X, at a segment σ with the number k and a name μ of its list: at an entry M with
the four marks markOf σ μ, ownerOf X k M and M.ttOff are the number of the segment that owns μ
(Sz.ref.owner), the owner's label, and 0. -/
theorem own_of_mark (Mk : PlanMarks X) {k : ℕ} {σ : Seg} (hσ : Seg.ofNo 12 k = some σ)
    {μ : MatName} (hμ : μ ∈ MatName.all 3 1 1 4 σ) {M : TMat}
    (h : (M.name, M.kind, M.aId, M.ttOff) = markOf σ μ) :
    ((ownerOf X k M).1, (ownerOf X k M).2, M.ttOff) =
      ((Sz.ref.owner σ μ).1.no 12, (Sz.ref.owner σ μ).2.label, 0) := by
  obtain ⟨hb, hno⟩ := Seg.of_ofNo hσ
  have hn : M.name = μ.label := congrArg (fun q : String × ℕ × ℕ × ℕ => q.1) h
  have hkind : M.kind = if Sz.ref.owner σ μ = (σ, μ) then 0 else 1 :=
    congrArg (fun q : String × ℕ × ℕ × ℕ => q.2.1) h
  have hid : M.aId = idOf (Sz.ref.owner σ μ).1 * 256 +
      (MatName.no? 3 1 1 4 (Sz.ref.owner σ μ).1 (Sz.ref.owner σ μ).2).getD 0 :=
    congrArg (fun q : String × ℕ × ℕ × ℕ => q.2.2.1) h
  have ht : M.ttOff = 0 := congrArg (fun q : String × ℕ × ℕ × ℕ => q.2.2.2) h
  by_cases ho : Sz.ref.owner σ μ = (σ, μ)
  · rw [if_pos ho] at hkind
    rw [ownerOf_own X k M (by omega), ho, hn, ht, hno]
  · rw [if_neg ho] at hkind
    have key : ∃ g n ν, g < 12 ∧ n < 256 ∧ (MatName.all 3 1 1 4 (.ff g))[n]? = some ν ∧
        Sz.ref.owner σ μ = (.ff g, ν) ∧ MatName.no? 3 1 1 4 (.ff g) ν = some n := by
      cases σ with
      | ff g =>
        have hg : g < 12 := hb
        have e : MatName.all 3 1 1 4 (.ff g) =
            [.af 0, .af 1, .af 2, .ad 0, .ar, .b, .qa, .xbO, .xbI] := rfl
        rw [e] at hμ
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hμ
        rcases hμ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first
          | exact absurd rfl ho
          | skip
        by_cases h0 : g = 0
        · exact absurd (show (if g = 0 then _ else _) = _ by rw [if_pos h0]) ho
        · exact ⟨g - 1, 7, .xbO, by omega, by omega, rfl,
            (show (if g = 0 then _ else _) = _ by rw [if_neg h0]), rfl⟩
      | att g =>
        have hg : g < 12 := hb
        have e : MatName.all 3 1 1 4 (.att g) = [.as 0, .ah, .ao, .bA, .qa] := rfl
        rw [e] at hμ
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hμ
        rcases hμ with rfl | rfl | rfl | rfl | rfl
        all_goals first
          | exact absurd rfl ho
          | skip
        exact ⟨g, 6, .qa, hg, by omega, rfl, rfl, rfl⟩
      | head =>
        have e : MatName.all 3 1 1 4 .head =
            [.hf 0, .hf 1, .hf 2, .hf 3, .hd, .hr, .bH, .xbL] := rfl
        rw [e] at hμ
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hμ
        rcases hμ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first
          | exact absurd rfl ho
          | skip
        exact ⟨11, 7, .xbO, by omega, by omega, rfl, rfl, rfl⟩
    obtain ⟨g, n, ν, hg, hn', hν, hown, hno'⟩ := key
    rw [hown] at hid ⊢
    rw [hno'] at hid
    rw [ownerOf_borrowed Mk k hg hn' hν hkind hid, ht]
    rfl

/-- **Under PlanMarks X and PartsFit X, for k < 25: matsOwn X k = matsOf X k**: the list that goes
by the plan's kinds and identifiers is the list that goes by the names and Sz.ref.owner. -/
theorem matsOwn_of_marks (M : PlanMarks X) (N : PartsFit X) {k : ℕ} (hk : k < 25) :
    matsOwn X k = matsOf X k := by
  obtain ⟨σ, hσ⟩ := seg_of_lt hk
  have p1 := (parts_at N hσ).1
  unfold matsOwn matsOf
  rw [hσ, tlOf_mats M.p4 M.groups hk]
  simp only [p1]
  apply List.ext_getElem?
  intro a
  rw [List.getElem?_map, List.getElem?_map, Array.getElem?_toList]
  have h := mark_at M hσ a
  cases hM : (planMats X k)[a]? with
  | none =>
    rw [hM] at h
    cases hμ : (MatName.all 3 1 1 4 σ)[a]? with
    | none => rfl
    | some μ => rw [hμ] at h; exact absurd h (by simp)
  | some T =>
    rw [hM] at h
    cases hμ : (MatName.all 3 1 1 4 σ)[a]? with
    | none => rw [hμ] at h; exact absurd h (by simp)
    | some μ =>
      rw [hμ] at h
      exact congrArg some (own_of_mark M hσ (List.mem_of_getElem? hμ) (Option.some.inj h))

/-- **The same in closed form**: under PlanMarks X and PartsFit X: for every k < 25, matsOwn X k =
matsOf X k. -/
theorem planOwners_of_marks (M : PlanMarks X) (N : PartsFit X) :
    ∀ k < 25, matsOwn X k = matsOf X k := fun _ hk => matsOwn_of_marks M N hk

/-- Under PlanMarks X and PartsFit X, for k < 25: matsOf X k has as many members as the list of
matrices of tlOf X k. -/
theorem matsOf_length_plan (M : PlanMarks X) (N : PartsFit X) {k : ℕ} (hk : k < 25) :
    (matsOf X k).length = (tlOf X k).mats.size := by
  rw [← matsOwn_of_marks M N hk]
  simp [matsOwn]

/-- **Under PlanMarks X and PartsFit X, for k < 25: zzOwn X k C ts = zzFull X k C ts**, for all
cells and all sampled entries: both are zzOf, at one state (tlOf_eq) and one list. -/
theorem zzOwn_eq_zzFull (M : PlanMarks X) (N : PartsFit X) {k : ℕ} (hk : k < 25) (C : Cells)
    (ts : List Int) : zzOwn X k C ts = zzFull X k C ts := by
  unfold zzOwn zzFull
  rw [matsOwn_of_marks M N hk, tlOf_eq (planLabels_of_marks M N) k]

/-- Two lists, the first mapped by f and the second by g, whose images agree at every number have
one length. -/
theorem length_of_getElem?_map {α β γ : Type} {f : α → γ} {g : β → γ} {l : List α} {m : List β}
    (H : ∀ a : ℕ, (l[a]?).map f = (m[a]?).map g) : l.length = m.length := by
  have h : l.map f = m.map g := List.ext_getElem? fun a => by
    rw [List.getElem?_map, List.getElem?_map]
    exact H a
  simpa using congrArg List.length h

/-- If the labels of a group's list at the numbers of parts 3, 1 are those at p0, p1: p0 = 3 and p1
= 1. Stated at group 0. In the places of attention's and the head's numbers of parts, which do not
enter a group's list, the left list has 1 and 4 and the right list 0 and 0. -/
theorem ff_parts {p0 p1 : ℕ}
    (H : ∀ a : ℕ, ((MatName.all 3 1 1 4 (.ff 0))[a]?).map MatName.label =
      ((MatName.all p0 p1 0 0 (.ff 0))[a]?).map MatName.label) : p0 = 3 ∧ p1 = 1 := by
  have hl := length_of_getElem?_map H
  have e : (MatName.all p0 p1 0 0 (.ff 0)).length = p0 + p1 + 5 := by
    simp [MatName.all]
    omega
  have e3 : (MatName.all 3 1 1 4 (.ff 0)).length = 9 := rfl
  have hp : p1 = 4 - p0 ∧ p0 ≤ 4 := by omega
  obtain ⟨rfl, h4⟩ := hp
  have h2 := H 2
  have h3 := H 3
  interval_cases p0
  · exact absurd h2 (by decide)
  · exact absurd h2 (by decide)
  · exact absurd h2 (by decide)
  · exact ⟨rfl, rfl⟩
  · exact absurd h3 (by decide)

/-- **Under PlanMarks X, PlanLabels X gives PartsFit X back**: so beside PlanMarks X the premise
PartsFit X of planLabels_of_marks is just what PlanLabels X needs. -/
theorem partsFit_of_labels (M : PlanMarks X) (B : PlanLabels X) : PartsFit X := by
  have H : ∀ {k : ℕ} {σ : Seg}, Seg.ofNo 12 k = some σ → ∀ a : ℕ,
      ((MatName.all 3 1 1 4 σ)[a]?).map MatName.label =
        ((MatName.all (X.y.parts.getD 0 0) (X.y.parts.getD 1 0)
          (OnBytes.Road.Hd.shapeA X (k / 2)).cf.NAs X.hS.NHf σ)[a]?).map MatName.label := by
    intro k σ hσ a
    have h := B.names k (lt_of_ofNo hσ) a
    rw [nameAt_of_marks M hσ a] at h
    unfold labelAt at h
    rw [hσ] at h
    exact h
  obtain ⟨a0, a1⟩ := ff_parts (H (k := 0) (σ := .ff 0) rfl)
  refine ⟨a0, a1, fun g hg => ?_, ?_⟩
  · have hσ : Seg.ofNo 12 (2 * g + 1) = some (.att g) := Seg.ofNo_no (σ := .att g) hg
    have hl := length_of_getElem?_map (H hσ)
    have e : (2 * g + 1) / 2 = g := by omega
    rw [e] at hl
    simp [MatName.all] at hl
    omega
  · have hl := length_of_getElem?_map (H (k := 24) (σ := .head) rfl)
    simp [MatName.all] at hl
    omega

/-- **Where some X has PlanMarks, PlanMarks does not give PlanLabels**: the value X' that is X but
for the head's number of parts NHf, set to 5, has PlanMarks where X has, and has not PlanLabels.
This is why PartsFit X stands beside PlanMarks X as a premise of planLabels_of_marks. X' is made for
this statement: it is not said to be the public part of any files. -/
theorem marks_without_labels (M : PlanMarks X) :
    PlanMarks { X with hS := { X.hS with NHf := 5 } } ∧
      ¬ PlanLabels { X with hS := { X.hS with NHf := 5 } } := by
  have M' : PlanMarks { X with hS := { X.hS with NHf := 5 } } := ⟨M.p4, M.groups, M.marks⟩
  exact ⟨M', fun B => absurd (partsFit_of_labels M' B).hf (show (5 : ℕ) ≠ 4 by decide)⟩

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.stepOf_two
#print axioms OnBytes.HonestTrace.tlOf_mats
#print axioms OnBytes.HonestTrace.mark_at
#print axioms OnBytes.HonestTrace.lt_of_ofNo
#print axioms OnBytes.HonestTrace.nameAt_of_marks
#print axioms OnBytes.HonestTrace.planLabels_of_marks
#print axioms OnBytes.HonestTrace.ownerOf_borrowed
#print axioms OnBytes.HonestTrace.own_of_mark
#print axioms OnBytes.HonestTrace.matsOwn_of_marks
#print axioms OnBytes.HonestTrace.planOwners_of_marks
#print axioms OnBytes.HonestTrace.matsOf_length_plan
#print axioms OnBytes.HonestTrace.zzOwn_eq_zzFull
#print axioms OnBytes.HonestTrace.length_of_getElem?_map
#print axioms OnBytes.HonestTrace.ff_parts
#print axioms OnBytes.HonestTrace.partsFit_of_labels
#print axioms OnBytes.HonestTrace.marks_without_labels
