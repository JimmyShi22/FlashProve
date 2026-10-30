-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/RowLTest.lean: RowL (KeepAtLater.lean: what a later moment's sending asks of the table of joints) AS A TEST WITH CODE ON THE TABLE ALONE. (Members: RowLFull.lean.)
  rowLB links ps k m t T     the test: it reads the table's open sets at the borders k and k + 1, the two places, and the promise's table's own row at the place (pubRowOf: it makes nothing); no letter
                             of the plan's numbers, no filling of the door
  madeAt M links ps k        the named public items that the door's filling M makes at block k
  rowL_of_test               **where the test says yes RowL holds, AT T ++ madeAt M links ps k** (NO hM, «the filling makes nothing at this place»: it is false at the reads' places at a version of
                             mgAll), at every N and M with THREE PREMISES: the plan's numbers of the groups of the
                             segments with an open class of rows part from m's (hinj) · its numbers of trees and of messages grow by what the place sends (trees · msgs): RowL's fields inj · trees ·
                             msgs ARE these premises; the other nine come of the test
  rowsDue_filter · mem_pinsOf · mem_sampledIn: on the table's own functions
Nothing on soundness.
-/
import Johnson.Desc.K1.Law.KeepAtLater
import Johnson.Desc.First.BordersSucc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More)
open VerifiableInference.Desc.K13.Law (openAt)

def inListRow : Item → Bool
  | .row _ c => c.inList
  | _ => false

def isPin : Item → Bool
  | .pin _ _ => true
  | _ => false

def isSampled : Item → Bool
  | .pin _ _ => true
  | .pinKept _ => true
  | .pinI => true
  | .pinV => true
  | _ => false

/-- **The test.** -/
def rowLB (links : List ModelPart) (ps : List Place) (k m t : ℕ) (T : List Pub) : Bool :=
  (match ps[k]?, ps[k + 1]? with
    | some p, some p' =>
      decide (First.standAt links p' = First.standAt links p) && decide (p'.link = p.link) &&
        (First.pubRowOf links p).makes.isEmpty
    | _, _ => false) &&
  (First.rowSegs (openAt links ps (k + 1))).all
    (fun m' => (First.rowSegs (openAt links ps k)).contains m') &&
  decide ((openAt links ps (k + 1)).filter inListRow = (openAt links ps k).filter inListRow) &&
  decide ((openAt links ps (k + 1)).filter isPin = (openAt links ps k).filter isPin ++ [.pin m t]) &&
  decide (t < 3) &&
  (openAt links ps (k + 1)).all
    (fun i => !isSampled i || (openAt links ps k).contains i || i == .pin m t) &&
  (First.pubOfItems (openAt links ps (k + 1))).all
    (fun q => (First.pubOfItems (openAt links ps k)).contains q || T.contains q)

/-- The count reads the classes in a list alone. -/
theorem rowsDue_filter (N : Numbers) (m : Nat) (O : List Item) :
    First.rowsDue N O m = First.rowsDue N (O.filter inListRow) m := by
  have key : ∀ (O : List Item) (k : Nat),
      O.foldl (fun k i => match i with
        | .row m' c => if m' == m && c.inList then k + (N.rowsAt m c).2 else k
        | _ => k) k =
      (O.filter inListRow).foldl (fun k i => match i with
        | .row m' c => if m' == m && c.inList then k + (N.rowsAt m c).2 else k
        | _ => k) k := by
    intro O
    induction O with
    | nil => intro k; rfl
    | cons i O ih =>
      intro k
      by_cases hi : inListRow i = true
      · rw [List.filter_cons_of_pos hi, List.foldl_cons, List.foldl_cons]
        exact ih _
      · rw [List.filter_cons_of_neg hi, List.foldl_cons, ← ih k]
        congr 1
        cases i with
        | row m' c =>
          have hc : c.inList = false := by simpa [inListRow] using hi
          simp [hc]
        | _ => rfl
  exact key O 0

theorem mem_pinsOf (N : Numbers) (O : List Item) (m : Nat) (x : Nat × Nat) :
    x ∈ pinsOf N O m ↔ ∃ t, t < 3 ∧ Item.pin m t ∈ O ∧ x ∈ N.sent m t := by
  unfold pinsOf
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨t, ht, hx⟩
    by_cases hc : O.contains (Item.pin m t) = true
    · rw [if_pos hc] at hx
      exact ⟨t, List.mem_range.1 ht, List.contains_iff_mem.1 hc, hx⟩
    · rw [if_neg hc] at hx
      cases hx
  · rintro ⟨t, ht, hm, hx⟩
    exact ⟨t, List.mem_range.2 ht, by rw [if_pos (List.contains_iff_mem.2 hm)]; exact hx⟩

theorem mem_sampledIn (N : Numbers) (O : List Item) (x : Nat × Nat)
    (h : x ∈ First.sampledIn N O) : ∃ i ∈ O, isSampled i = true ∧ x ∈ First.sampledIn N [i] := by
  unfold First.sampledIn at h ⊢
  obtain ⟨i, hi, hx⟩ := List.mem_flatMap.1 h
  refine ⟨i, hi, ?_, List.mem_flatMap.2 ⟨i, List.mem_singleton.2 rfl, hx⟩⟩
  cases i <;> first | rfl | cases hx

theorem sampledIn_mem (N : Numbers) (O : List Item) (i : Item) (hi : i ∈ O) (x : Nat × Nat)
    (h : x ∈ First.sampledIn N [i]) : x ∈ First.sampledIn N O := by
  unfold First.sampledIn at h ⊢
  obtain ⟨j, hj, hx⟩ := List.mem_flatMap.1 h
  obtain rfl := List.mem_singleton.1 hj
  exact List.mem_flatMap.2 ⟨j, hi, hx⟩

/-- The named public items that the door's filling makes at block k. -/
def madeAt (M : More) (links : List ModelPart) (ps : List Place) (k : ℕ) : List Pub :=
  match ps[k]? with
  | some p => (M.rows links p).makes.map First.moreItem
  | none => []

/-- **WHERE THE TEST SAYS YES.** FOURTH FORM: no premise on the door's filling: what it makes at the place comes into the list of the public items that come. -/
theorem rowL_of_test (N : Numbers) (M : More) (links : List ModelPart) (ps : List Place)
    (k m t nT nM : ℕ) (T : List Pub) (h : rowLB links ps k m t T = true)
    (hinj : ∀ m' ∈ First.rowSegs (openAt links ps (k + 1)), N.groupAt m' = N.groupAt m → m' = m)
    (trees : N.treesAt ps[k + 1]? = N.treesAt ps[k]? + nT)
    (msgs : N.msgsAt ps[k + 1]? = N.msgsAt ps[k]? + nM) :
    RowL N M links ps k m t nT nM (T ++ madeAt M links ps k) := by
  unfold rowLB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  rw [List.all_eq_true] at h2 h6 h7
  have hpin : ∀ m' t', Item.pin m' t' ∈ openAt links ps (k + 1) ↔
      (Item.pin m' t' ∈ openAt links ps k ∨ (m' = m ∧ t' = t)) := by
    intro m' t'
    have a : Item.pin m' t' ∈ openAt links ps (k + 1) ↔
        Item.pin m' t' ∈ (openAt links ps (k + 1)).filter isPin := by
      rw [List.mem_filter]
      exact ⟨fun x => ⟨x, rfl⟩, fun x => x.1⟩
    have b : Item.pin m' t' ∈ openAt links ps k ↔
        Item.pin m' t' ∈ (openAt links ps k).filter isPin := by
      rw [List.mem_filter]
      exact ⟨fun x => ⟨x, rfl⟩, fun x => x.1⟩
    rw [a, h4, List.mem_append, ← b, List.mem_singleton]
    constructor
    · rintro (x | x)
      · exact Or.inl x
      · injection x with e1 e2
        exact Or.inr ⟨e1, e2⟩
    · rintro (x | ⟨rfl, rfl⟩)
      · exact Or.inl x
      · exact Or.inr rfl
  have hnext : ∃ p p', ps[k]? = some p ∧ ps[k + 1]? = some p' ∧
      First.standAt links p' = First.standAt links p ∧ p'.link = p.link ∧
      (First.pubRowOf links p).makes = [] := by
    cases hp : ps[k]? with
    | none => rw [hp] at h1; cases h1
    | some p =>
      cases hp' : ps[k + 1]? with
      | none => rw [hp, hp'] at h1; cases h1
      | some p' =>
        rw [hp, hp'] at h1
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at h1
        exact ⟨p, p', rfl, rfl, h1.1.1, h1.1.2, h1.2⟩
  obtain ⟨p, p', hp, hp', a1, a2, a3⟩ := hnext
  · · have hsub : ∀ q ∈ (First.pubSets M links ps)[k + 1]?.getD [],
          q ∈ (First.pubSets M links ps)[k]?.getD [] ∨ q ∈ madeAt M links ps k := by
        intro q hq
        rw [First.pubSets_succ M links ps k p hp] at hq
        unfold First.pubStep at hq
        have hmk : (First.pubRowM M links p).makes = madeAt M links ps k := by
          simp [First.pubRowM, First.PubRow.plus, a3, madeAt, hp]
        rw [hmk] at hq
        simp only [List.mem_append, List.mem_filter] at hq
        rcases hq with y | y
        · exact Or.inl y.1
        · exact Or.inr y.1
      refine ⟨⟨p, p', hp, hp', a1, a2⟩, fun m' hm' => List.contains_iff_mem.1 (h2 m' hm'), ?_, ?_,
        hinj, ?_, ?_, ?_, ?_, fun q hq => (hsub q hq).imp id (List.mem_append_right _), ?_, ?_⟩
      · intro m'
        rw [rowsDue_filter N m' (openAt links ps (k + 1)), h3, ← rowsDue_filter]
      · intro m' c hc hl
        have : Item.row m' c ∈ (openAt links ps (k + 1)).filter inListRow :=
          List.mem_filter.2 ⟨hc, hl⟩
        rw [h3] at this
        exact (List.mem_filter.1 this).1
      · intro m' hne
        unfold pinsOf
        refine List.flatMap_congr fun t' _ => ?_
        have e : (openAt links ps (k + 1)).contains (Item.pin m' t') =
            (openAt links ps k).contains (Item.pin m' t') := by
          rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem, hpin]
          exact ⟨fun x => x.elim id fun y => absurd y.1 hne, Or.inl⟩
        rw [e]
      · intro x
        rw [mem_pinsOf, mem_pinsOf]
        constructor
        · rintro ⟨t', ht', hm', hx⟩
          rcases (hpin m t').1 hm' with y | ⟨_, rfl⟩
          · exact Or.inl ⟨t', ht', y, hx⟩
          · exact Or.inr hx
        · rintro (⟨t', ht', hm', hx⟩ | hx)
          · exact ⟨t', ht', (hpin m t').2 (Or.inl hm'), hx⟩
          · exact ⟨t, h5, (hpin m t).2 (Or.inr ⟨rfl, rfl⟩), hx⟩
      · intro x hx
        obtain ⟨i, hi, hs, hxi⟩ := mem_sampledIn N _ x hx
        have h6i := h6 i hi
        rw [hs] at h6i
        simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at h6i
        rcases h6i with y | rfl
        · exact Or.inl (sampledIn_mem N _ i (List.contains_iff_mem.1 y) x hxi)
        · right
          simpa [First.sampledIn] using hxi
      · intro q hq
        rcases List.mem_append.1 hq with hq | hq
        · rcases hsub q hq with y | y
          · exact Or.inl (List.mem_append_left _ y)
          · exact Or.inr (List.mem_append_right _ y)
        · have := h7 q hq
          rw [Bool.or_eq_true] at this
          rcases this with y | y
          · exact Or.inl (List.mem_append_right _ (List.contains_iff_mem.1 y))
          · exact Or.inr (List.mem_append_left _ (List.contains_iff_mem.1 y))
      · exact trees
      · exact msgs

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.rowL_of_test
