-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Coin/FirstOpensSets.lean: THE PAIRS THAT THE LAST CHAIN's TEST ON TAKEN SOURCES READS OFF THE
BOOK ARE, AS A SET, THE PLACES OF THE TREES AT `D.ts`: the proximity test's plain data against the
record in front of it.

Why. `firstOpens_of` (Johnson/Desc/K12/Coin/FirstOpensOf.lean) takes as a premise that the first switch's
openings' places and the places pl z, z in D.ts, are the same as sets. The last chain's test on taken
sources (`takenOf`) makes, of the record in front of the test, for each member of the
own group and then the mask: (1 for the message Omega, 0 for every other; the number of its tree in the
book). Here that list, said at the test's own record (`tkOf`), is tied to D.ts.
  `tkOf t ω`        `takenOf`'s list (Johnson/Desc/Third/TakenSources.lean) with the record's fields as the seat lays them (s.st ↦ t.st ·
                    s.book ↦ t.book · s.loc.own ↦ t.g · s.loc.mask ↦ t.mask) and s.loc.omega a letter ω.
                    THAT takenOf s IS tkOf AT THE SEAT's RECORD HAS NOT MET LEAN: the last chain's record
                    type does not lie on this ground
  `plOf B ω z`      the place of the tree at z of the book B: (1 if z is the place of Omega's tree,
                    else 0; the tree's number)
  `Sits`            the message i lies in the tree at z of the book, whose number is n
  `members_layout`  a group's layout has the group's members
  `sits_of_member`, `member_of_ts`   every member and the mask sit at a place of D.ts; every place of D.ts
                    holds one of them
  `tk_eq_places`    **x ∈ tk ↔ x ∈ D.ts.map (plOf t.book ω)**
THE NAMED PREMISE. `alone`: of the group's members and the mask, Omega alone lies in Omega's tree.
A pair may stand in tk twice (two messages in one tree): membership alone is spent.
Limits. The mask has come (t.mask is some). A fact on one record; nothing on which book a record that
runs holds. Nothing on soundness.

-/
import Johnson.Desc.K12.Coin.FirstOpensOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.First (Plain gpOf)

/-- The pair that the test on taken sources makes of the message i. -/
def pairAt (B : TreeBook) (ω i : ℕ) : Option (ℕ × ℕ) :=
  ((B.place[i]?).bind fun q => B.trees[q.1]?).map fun T => (if i == ω then 1 else 0, T.number)

/-- The list of the test on taken sources, at the proximity test's own record. -/
def tkOf (t : T12) (ω : ℕ) : Option (List (ℕ × ℕ)) :=
  (t.st.groups[t.g]?).bind fun G => (G.members.toList ++ t.mask.toList).mapM (pairAt t.book ω)

/-- The place of the tree at z of a book: the chain that sent it (1 if it is Omega's tree, else 0),
and its number. -/
def plOf (B : TreeBook) (ω z : ℕ) : ℕ × ℕ :=
  (if (B.place[ω]?).map (·.1) = some z then 1 else 0, ((B.trees[z]?).map (·.number)).getD 0)

/-- The message i lies in the tree at z of the book, whose number is n. -/
def Sits (B : TreeBook) (i z n : ℕ) : Prop :=
  ∃ p T, B.place[i]? = some (z, p) ∧ B.trees[z]? = some T ∧ T.number = n

theorem pairAt_of_sits {B : TreeBook} {ω i z n : ℕ} (h : Sits B i z n) :
    pairAt B ω i = some (if i == ω then 1 else 0, n) := by
  obtain ⟨p, T, hp, hT, rfl⟩ := h
  unfold pairAt
  rw [hp]
  show (B.trees[z]?).map _ = _
  rw [hT]
  rfl

/-- Under `alone` at i: the place by the tree is the pair by the message. -/
theorem plOf_of_sits {B : TreeBook} {ω i z n : ℕ} (h : Sits B i z n)
    (alone : ∀ q, B.place[ω]? = some q → q.1 = z → i = ω) :
    plOf B ω z = (if i == ω then 1 else 0, n) := by
  obtain ⟨p, T, hp, hT, rfl⟩ := h
  unfold plOf
  rw [hT]
  by_cases e : i = ω
  · subst e
    rw [hp]
    simp
  · have h1 : ¬ (B.place[ω]?).map (·.1) = some z := by
      intro hz
      obtain ⟨q, hq, hq1⟩ := Option.map_eq_some_iff.1 hz
      exact e (alone q hq hq1)
    rw [if_neg h1]
    simp [e]

/-- A group's layout has the group's members. -/
theorem members_layout {S : Statement} {g : ℕ} {G0 : Group} {Ly : GroupLayout}
    (hG : S.groups[g]? = some G0) (hL : S.layout g = some Ly) : Ly.members = G0.members := by
  unfold Statement.layout at hL
  rw [hG] at hL
  have e := Option.some.inj hL
  rw [← e]

section
variable {π : P12} {t : T12} {a : Fmt.M1.Stage} {rest : List Fmt.M1.Stage} {G0 : Group}
  {Ly : GroupLayout} {D : Plain}

/-- What the plain data hold where the mask has come: the record's book; the mask's number. -/
theorem book_fresh_of_fixes (hF : Fixes π t a rest G0 Ly D) {id : ℕ} (hm : t.mask = some id) :
    D.book = t.book ∧ D.fresh.id = id := by
  obtain ⟨cu, -, he⟩ := (H2K.First.made_of _ _ _ _ _ (hF.2.2.2 { group := 0 })).ent
  unfold H2K.First.entered at he
  dsimp only at he
  rw [hm] at he
  have e := Option.some.inj he
  exact ⟨(congrArg (fun x => x.2.2) e).symm, (congrArg (fun x => x.1) e).symm⟩

/-- Every member of the group, and the mask, sits at a place of D.ts. -/
theorem sits_of_member (hF : Fixes π t a rest G0 Ly D) {id : ℕ} (hm : t.mask = some id) (i : ℕ)
    (hi : i ∈ G0.members.toList ++ t.mask.toList) : ∃ z n, Sits t.book i z n ∧ z ∈ D.ts := by
  have M := H2K.First.made_of _ _ _ _ _ (hF.2.2.2 { group := 0 })
  obtain ⟨hb, hf⟩ := book_fresh_of_fixes hF hm
  have hmem := members_layout hF.2.1 hF.2.2.1
  rw [M.ts]
  rcases List.mem_append.1 hi with hi | hi
  · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hi
    have hj' : Ly.members[j]? = some i := by
      rw [hmem]
      simpa using hj
    have hlt : j < D.mems.length := by
      rw [← M.size]
      exact (Array.getElem?_eq_some_iff.1 hj').1
    obtain ⟨k1, k2⟩ := M.mem ⟨j, hlt⟩
    have e : (D.mems.get ⟨j, hlt⟩).id = i := Option.some.inj (k1.symm.trans hj')
    rw [e, hb] at k2
    obtain ⟨T, hT, -, hn⟩ := k2.tree
    refine ⟨_, _, ⟨_, T, k2.place, hT, hn⟩, (Fmt.listOf_mem _ _).2 (List.mem_append_left _ ?_)⟩
    exact List.mem_map.2 ⟨_, List.get_mem _ _, rfl⟩
  · rw [hm] at hi
    have e : i = id := by simpa using hi
    have k2 := M.fresh
    rw [hf, hb, ← e] at k2
    obtain ⟨T, hT, -, hn⟩ := k2.tree
    exact ⟨_, _, ⟨_, T, k2.place, hT, hn⟩,
      (Fmt.listOf_mem _ _).2 (List.mem_append_right _ (List.mem_singleton.2 rfl))⟩

/-- Every place of D.ts holds a member of the group, or the mask. -/
theorem member_of_ts (hF : Fixes π t a rest G0 Ly D) {id : ℕ} (hm : t.mask = some id) (z : ℕ)
    (hz : z ∈ D.ts) : ∃ i ∈ G0.members.toList ++ t.mask.toList, ∃ n, Sits t.book i z n := by
  have M := H2K.First.made_of _ _ _ _ _ (hF.2.2.2 { group := 0 })
  obtain ⟨hb, hf⟩ := book_fresh_of_fixes hF hm
  have hmem := members_layout hF.2.1 hF.2.2.1
  rw [M.ts] at hz
  rcases List.mem_append.1 ((Fmt.listOf_mem _ _).1 hz) with hz | hz
  · obtain ⟨m, hmm, rfl⟩ := List.mem_map.1 hz
    obtain ⟨j, rfl⟩ := List.get_of_mem hmm
    obtain ⟨k1, k2⟩ := M.mem j
    rw [hb] at k2
    obtain ⟨T, hT, -, hn⟩ := k2.tree
    refine ⟨_, List.mem_append_left _ ?_, _, ⟨_, T, k2.place, hT, hn⟩⟩
    rw [hmem] at k1
    exact List.mem_of_getElem? (i := j.val) (by simpa using k1)
  · obtain rfl := List.mem_singleton.1 hz
    have k2 := M.fresh
    rw [hf, hb] at k2
    obtain ⟨T, hT, -, hn⟩ := k2.tree
    refine ⟨id, List.mem_append_right _ ?_, _, ⟨_, T, k2.place, hT, hn⟩⟩
    rw [hm]
    simp

theorem forall₂_mem_l {α β : Type} {P : α → β → Prop} : ∀ {l : List α} {m : List β},
    List.Forall₂ P l m → ∀ x ∈ l, ∃ y ∈ m, P x y
  | _, _, .nil, _, h => nomatch h
  | _, _, .cons (b := b) h t, x, hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨b, List.mem_cons_self, h⟩
    · obtain ⟨y, hy, hp⟩ := forall₂_mem_l t x hx
      exact ⟨y, List.mem_cons_of_mem _ hy, hp⟩

theorem forall₂_mem_r {α β : Type} {P : α → β → Prop} : ∀ {l : List α} {m : List β},
    List.Forall₂ P l m → ∀ y ∈ m, ∃ x ∈ l, P x y
  | _, _, .nil, _, h => nomatch h
  | _, _, .cons (a := a) h t, y, hy => by
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨a, List.mem_cons_self, h⟩
    · obtain ⟨x, hx, hp⟩ := forall₂_mem_r t y hy
      exact ⟨x, List.mem_cons_of_mem _ hx, hp⟩

/-- **The pairs that the test on taken sources reads off the book are, as a set, the places of the
trees at D.ts.** -/
theorem tk_eq_places (hF : Fixes π t a rest G0 Ly D) {id : ℕ} (hm : t.mask = some id) (ω : ℕ)
    (tk : List (ℕ × ℕ)) (htk : tkOf t ω = some tk)
    (alone : ∀ i ∈ G0.members.toList ++ t.mask.toList, ∀ q p z, t.book.place[ω]? = some q →
      t.book.place[i]? = some (z, p) → q.1 = z → i = ω) :
    ∀ x, x ∈ tk ↔ x ∈ D.ts.map (plOf t.book ω) := by
  unfold tkOf at htk
  rw [hF.2.1] at htk
  have W := optMapM_ok _ _ _ (show (G0.members.toList ++ t.mask.toList).mapM (pairAt t.book ω) =
    some tk from htk)
  have al : ∀ i ∈ G0.members.toList ++ t.mask.toList, ∀ z n, Sits t.book i z n →
      plOf t.book ω z = (if i == ω then 1 else 0, n) := by
    intro i hi z n hs
    refine plOf_of_sits hs fun q hq hq1 => ?_
    obtain ⟨p, _, hp, _, _⟩ := hs
    exact alone i hi q p z hq hp hq1
  intro x
  constructor
  · intro hx
    obtain ⟨i, hi, hp⟩ := forall₂_mem_r W x hx
    obtain ⟨z, n, hs, hz⟩ := sits_of_member hF hm i hi
    rw [pairAt_of_sits hs] at hp
    refine List.mem_map.2 ⟨z, hz, ?_⟩
    rw [al i hi z n hs]
    exact Option.some.inj hp
  · intro hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i, hi, n, hs⟩ := member_of_ts hF hm z hz
    obtain ⟨y, hy, hp⟩ := forall₂_mem_l W i hi
    rw [pairAt_of_sits hs] at hp
    rw [al i hi z n hs, Option.some.inj hp]
    exact hy

end

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.members_layout
#print axioms VerifiableInference.Desc.K12.Coin.sits_of_member
#print axioms VerifiableInference.Desc.K12.Coin.member_of_ts
#print axioms VerifiableInference.Desc.K12.Coin.tk_eq_places
