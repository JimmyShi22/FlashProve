-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/HeldAtLater.lean: TWO CLAUSES OF THE PROMISE OF THE TABLE OF JOINTS (Johnson/Desc/First/Borders.lean: rowsHeld, membersHeld) BEHIND A LATER MOMENT's SENDING OF KIND K1
(commitAtS: a link's reads, its digits). The twin, for a later moment, of Johnson/Desc/K1/Law/HeldAtOpening.lean. Statements with their proofs.
  rowsHeld_joins     a joining leaves rowsHeld, at one open set
  rowsHeld_open      rowsHeld goes from an open set O to O' where O' has no segment with an open class that O lacks, counts as many rows in each list, and has no class in a list
                     that O lacks
  commitAtS_rowsHeld **the rows**
  laterSeatsB        a test with code on the plan: the tenants that the plan gives segment m at moment t are just the seats of this place's messages, behind nT trees
  commitAtS_membersHeld **the members**
WHAT THE PROMISE IN FRONT DOES NOT GIVE (by reading onAt): that the state's frame's group IS the plan's number of the segment's group (hg): a premise here.
Nothing on soundness.
-/
import Johnson.Desc.K1.Law.GroupAtLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S Item Numbers)

variable {Cl : Type}

/-- A joining leaves a group's rows and its mark: what rowsHeld reads of a group. -/
theorem joins_group {st st' : Statement} {g : Nat} {ids : List Nat} (hJ : Joins st st' g ids) (j : Nat) :
    (st.groups[j]? = none ∧ st'.groups[j]? = none) ∨
      ∃ G G', st.groups[j]? = some G ∧ st'.groups[j]? = some G' ∧ G'.inRun = G.inRun ∧
        G'.rows = G.rows := by
  by_cases e : j = g
  · subst e
    cases hG : st.groups[j]? with
    | none =>
      left
      refine ⟨rfl, ?_⟩
      rw [Array.getElem?_eq_none_iff] at hG ⊢
      rw [hJ.size]
      exact hG
    | some G =>
      obtain ⟨G', h1, h2, h3, _⟩ := hJ.here G hG
      exact Or.inr ⟨G, G', rfl, h1, h2, h3⟩
  · rw [hJ.other j e]
    cases hG : st.groups[j]? with
    | none => exact Or.inl ⟨rfl, rfl⟩
    | some G => exact Or.inr ⟨G, G, rfl, rfl, rfl, rfl⟩

theorem rowsHeld_joins (N : Numbers) (O : List Item) (s s' : S) {g : Nat} {ids : List Nat}
    (hJ : Joins s.st s'.st g ids) (h : First.rowsHeld N O s = true) : First.rowsHeld N O s' = true := by
  unfold First.rowsHeld at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro m hm
  have hm' := h m hm
  rcases joins_group hJ (N.groupAt m) with ⟨a, b⟩ | ⟨G, G', a, b, c, d⟩
  · rw [a] at hm'
    rw [b]
    exact hm'
  · rw [a] at hm'
    rw [b]
    dsimp only at hm' ⊢
    rw [c, d]
    exact hm'

theorem rowsHeld_open (N : Numbers) (O O' : List Item) (s : S)
    (hseg : ∀ m ∈ First.rowSegs O', m ∈ First.rowSegs O)
    (hdue : ∀ m, First.rowsDue N O' m = First.rowsDue N O m)
    (hin : ∀ m c, Item.row m c ∈ O' → c.inList = true → Item.row m c ∈ O)
    (h : First.rowsHeld N O s = true) : First.rowsHeld N O' s = true := by
  unfold First.rowsHeld at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro m hm
  have hm' := h m (hseg m hm)
  cases hG : s.st.groups[N.groupAt m]? with
  | none =>
    rw [hG] at hm'
    dsimp only at hm' ⊢
    rw [hdue]
    exact hm'
  | some G =>
    rw [hG] at hm'
    dsimp only at hm' ⊢
    rw [Bool.and_eq_true, Bool.and_eq_true] at hm' ⊢
    obtain ⟨⟨a, b⟩, c⟩ := hm'
    refine ⟨⟨a, by rw [hdue]; exact b⟩, List.all_eq_true.2 fun i hi => ?_⟩
    cases i with
    | row m' cl =>
      by_cases e : (m' == m && cl.inList) = true
      · have hl : cl.inList = true := (Bool.and_eq_true_iff.1 e).2
        exact List.all_eq_true.1 c _ (hin m' cl hi hl)
      · show (!(m' == m && cl.inList) || _) = true
        rw [Bool.not_eq_true] at e
        rw [e]
        rfl
    | _ => rfl

/-- **THE ROWS.** -/
theorem commitAtS_rowsHeld (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (s s' : S)
    (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s [r₁, r₂] gs = .ok s')
    (N : Numbers) (O O' : List Item)
    (hseg : ∀ m ∈ First.rowSegs O', m ∈ First.rowSegs O)
    (hdue : ∀ m, First.rowsDue N O' m = First.rowsDue N O m)
    (hin : ∀ m c, Item.row m c ∈ O' → c.inList = true → Item.row m c ∈ O)
    (hR : First.rowsHeld N O s = true) : First.rowsHeld N O' s' = true := by
  obtain ⟨L, _, hJ⟩ := commitAtS_group P link moment arrays s s' r₁ r₂ gs h
  exact rowsHeld_open N O O' s' hseg hdue hin (rowsHeld_joins N O s s' hJ hR)

/-- The plan's tenants of segment m whose pins are open. -/
def pinsOf (N : Numbers) (O : List Item) (m : Nat) : List (Nat × Nat) :=
  (List.range 3).flatMap fun t => if O.contains (.pin m t) then N.sent m t else []

/-- **The tenants that the plan gives segment m at moment t are just the seats of this place's messages**, behind nT trees: a test with code on the plan. -/
def laterSeatsB (N : Numbers) (P : Par) (m t nT : Nat) : Bool :=
  First.sameMembers
    ((List.range P.sent.size).map fun i => (nT + (layOf P).tree.getD i 0, (layOf P).part.getD i 0))
    (N.sent m t)

theorem mem_idsOf (P : Par) (n₀ o : Nat) :
    o ∈ (idsOf P n₀).toList ↔ ∃ i, i < P.sent.size ∧ o = n₀ + i := by
  unfold idsOf
  rw [Array.toList_map, Array.toList_range, List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, List.mem_range.1 hi, Nat.add_comm _ _⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, List.mem_range.2 hi, Nat.add_comm _ _⟩

/-- **THE MEMBERS**, of what a sending does to the groups and the book. m, t: the segment and the moment of this sending. -/
theorem membersHeld_joins (P : Par) (s s' : S) (N : Numbers) (O O' : List Item) (m t : Nat)
    (hJ : Joins s.st s'.st (N.groupAt m) (idsOf P s.st.oracles.size).toList)
    (hB : Booked P s.book s.st.oracles.size s'.book s'.st.oracles.size)
    (hseg : ∀ m' ∈ First.rowSegs O', m' ∈ First.rowSegs O)
    (hinj : ∀ m' ∈ First.rowSegs O', N.groupAt m' = N.groupAt m → m' = m)
    (hb : s.book.place.size = s.st.oracles.size)
    (hother : ∀ m', m' ≠ m → pinsOf N O' m' = pinsOf N O m')
    (hhere : ∀ x, x ∈ pinsOf N O' m ↔ (x ∈ pinsOf N O m ∨ x ∈ N.sent m t))
    (hP : laterSeatsB N P m t s.book.trees.size = true)
    (hM : First.membersHeld N O s = true) : First.membersHeld N O' s' = true := by
  have hold : ∀ o : Nat, (s.book.place[o]?).isSome = true → s'.book.place[o]? = s.book.place[o]? := by
    intro o ho
    refine hB.older ?_
    by_contra hx
    rw [Array.getElem?_eq_none (by omega)] at ho
    cases ho
  unfold First.membersHeld at hM ⊢
  rw [List.all_eq_true] at hM ⊢
  intro m' hm'
  have h0 := hM m' (hseg m' hm')
  by_cases e : N.groupAt m' = N.groupAt m
  · obtain rfl := hinj m' hm' e
    cases hG : s.st.groups[N.groupAt m']? with
    | none =>
      have : s'.st.groups[N.groupAt m']? = none := by
        rw [Array.getElem?_eq_none_iff] at hG ⊢
        rw [hJ.size]
        exact hG
      rw [this]
    | some G =>
      rw [hG] at h0
      obtain ⟨G', g1, _, _, g4⟩ := hJ.here G hG
      rw [g1]
      dsimp only at h0 ⊢
      rw [Bool.and_eq_true] at h0 ⊢
      obtain ⟨a, b⟩ := h0
      rw [List.all_eq_true] at a
      have b' := (sameMembers_iff _ _).1 b
      have hnew : ∀ i, i < P.sent.size → s'.book.place[s.st.oracles.size + i]? =
          some (s.book.trees.size + (layOf P).tree.getD i 0, (layOf P).part.getD i 0) :=
        fun i hi => hB.newer hb hi
      refine ⟨List.all_eq_true.2 fun o ho => ?_, (sameMembers_iff _ _).2 fun x => ?_⟩
      · rcases (g4 o).1 ho with ho | ho
        · rw [hold o (a o ho)]
          exact a o ho
        · obtain ⟨i, hi, rfl⟩ := (mem_idsOf P _ o).1 ho
          rw [hnew i hi]
          rfl
      · show x ∈ _ ↔ x ∈ pinsOf N O' m'
        rw [hhere x, ← (sameMembers_iff _ _).1 hP x, List.mem_filterMap, List.mem_map]
        constructor
        · rintro ⟨o, ho, hx⟩
          rcases (g4 o).1 ho with ho | ho
          · left
            rw [hold o (a o ho)] at hx
            exact (b' x).1 (List.mem_filterMap.2 ⟨o, ho, hx⟩)
          · right
            obtain ⟨i, hi, rfl⟩ := (mem_idsOf P _ o).1 ho
            rw [hnew i hi] at hx
            exact ⟨i, List.mem_range.2 hi, Option.some.inj hx⟩
        · rintro (hx | ⟨i, hi, rfl⟩)
          · obtain ⟨o, ho, hx⟩ := List.mem_filterMap.1 ((b' x).2 hx)
            exact ⟨o, (g4 o).2 (Or.inl ho), by rw [hold o (a o ho)]; exact hx⟩
          · have hi' := List.mem_range.1 hi
            exact ⟨s.st.oracles.size + i, (g4 _).2 (Or.inr ((mem_idsOf P _ _).2 ⟨i, hi', rfl⟩)),
              hnew i hi'⟩
  · rw [hJ.other _ e]
    have hne : m' ≠ m := fun x => e (by rw [x])
    cases hG : s.st.groups[N.groupAt m']? with
    | none => rfl
    | some G =>
      rw [hG] at h0
      dsimp only at h0 ⊢
      rw [Bool.and_eq_true] at h0 ⊢
      obtain ⟨a, b⟩ := h0
      rw [List.all_eq_true] at a
      have hsame : (G.members.toList.filterMap fun o => s'.book.place[o]?) =
          G.members.toList.filterMap fun o => s.book.place[o]? :=
        List.filterMap_congr fun o ho => hold o (a o ho)
      refine ⟨List.all_eq_true.2 fun o ho => by rw [hold o (a o ho)]; exact a o ho, ?_⟩
      rw [hsame]
      show First.sameMembers _ (pinsOf N O' m') = true
      rw [hother m' hne]
      exact b

/-- **THE MEMBERS, at the block.** -/
theorem commitAtS_membersHeld (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (s s' : S)
    (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s [r₁, r₂] gs = .ok s')
    (N : Numbers) (O O' : List Item) (m t : Nat)
    (hseg : ∀ m' ∈ First.rowSegs O', m' ∈ First.rowSegs O)
    (hg : ∀ L, s.link? = some L → L.check.frame.group = N.groupAt m)
    (hinj : ∀ m' ∈ First.rowSegs O', N.groupAt m' = N.groupAt m → m' = m)
    (hb : s.book.place.size = s.st.oracles.size)
    (hother : ∀ m', m' ≠ m → pinsOf N O' m' = pinsOf N O m')
    (hhere : ∀ x, x ∈ pinsOf N O' m ↔ (x ∈ pinsOf N O m ∨ x ∈ N.sent m t))
    (hP : laterSeatsB N P m t s.book.trees.size = true)
    (hM : First.membersHeld N O s = true) : First.membersHeld N O' s' = true := by
  obtain ⟨L, hL, hJ⟩ := commitAtS_group P link moment arrays s s' r₁ r₂ gs h
  rw [hg L hL] at hJ
  exact membersHeld_joins P s s' N O O' m t hJ
    (commitAtS_booked P link moment arrays s s' r₁ r₂ gs h) hseg hinj hb hother hhere hP hM

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.commitAtS_rowsHeld
#print axioms VerifiableInference.Desc.K1.commitAtS_membersHeld
