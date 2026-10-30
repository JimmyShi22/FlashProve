-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/AskPoint.lean: CONDITIONAL.

What is here. Of a family of tables in the verifier's list (`tableAsks`,
OnBytes/Model/LayerForms.lean) the NAME says the point and the sort: a family named prefix@Z, the
prefix without the sign @, is taken at the point Z (`point_of_name`); its runs have 2 ^ la rows if
it is long and T rows if it is short (`ask_named`); and where the verifier's `readsOf` has made the
lists of points, a family at zt, rt, P_V or r_tV is short, and one at Z, Z_V, Y, Z_a, Z_b or Z_E is
long (`short_of_point`, `long_of_point`). So a reader's table, which it picks by such a name, can be
held against the honest side's test on a point's size (`wtsFit`, Johnson/Desc/K4/Honest/Cells.lean).

  `cut_at_sign`   two lists cut at the first occurrence of a sign.
  `name_split`   the same for two names prefix@point.
  `ask_named`   each family of the list: named prefix@point with its numbers, or one of the three on
      the lookup's planes.
  `mem_one`, `long_pts`, `short_pts`, `rd_points`   the points that readsOf lists: five long, four
      short.
  `point_of_name`, `short_of_point`, `long_of_point`   the name says the point; the point says the
      sort.

Not shown here. That readsOf returns: a hypothesis of rd_points, short_of_point and long_of_point.
Whether a family under a given name is in the list. Nothing on soundness, on completeness or on any
other property. No property is claimed.
-/
import Johnson.Road.FormsKeysLaid
import OnBytes.Model.LayerForms

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Lay Reads TableAsk tableAsks readsOf)

/-- Two lists cut at the first occurrence of a sign. -/
theorem cut_at_sign {α : Type} {c : α} : ∀ {l1 l2 a b : List α}, c ∉ l1 → c ∉ l2 →
    l1 ++ c :: a = l2 ++ c :: b → l1 = l2 ∧ a = b
  | [], [], _, _, _, _, h => ⟨rfl, (List.cons.inj h).2⟩
  | [], y :: l2, _, _, _, h2, h => absurd (List.cons.inj h).1 fun e => h2 (e ▸ List.mem_cons_self)
  | x :: l1, [], _, _, h1, _, h => absurd (List.cons.inj h).1 fun e => h1 (e ▸ List.mem_cons_self)
  | x :: l1, y :: l2, a, b, h1, h2, h => by
    obtain ⟨e1, e2⟩ := List.cons.inj h
    obtain ⟨r1, r2⟩ := cut_at_sign (fun m => h1 (List.mem_cons_of_mem _ m))
      (fun m => h2 (List.mem_cons_of_mem _ m)) e2
    exact ⟨by rw [e1, r1], r2⟩

/-- Two names prefix@point, the prefixes without the sign @. -/
theorem name_split {m1 m2 n1 n2 : String} (h1 : '@' ∉ m1.toList) (h2 : '@' ∉ m2.toList)
    (e : m1 ++ "@" ++ n1 = m2 ++ "@" ++ n2) : m1 = m2 ∧ n1 = n2 := by
  have e' := congrArg String.toList e
  rw [String.toList_append, String.toList_append, String.toList_append, String.toList_append,
    List.append_assoc, List.append_assoc] at e'
  obtain ⟨r1, r2⟩ := cut_at_sign h1 h2 (a := n1.toList) (b := n2.toList) e'
  exact ⟨String.toList_inj.mp r1, String.toList_inj.mp r2⟩

/-- **Each family of the verifier's list.** -/
theorem ask_named {y : Lay} {rd : Reads} {g : ℕ} {a : TableAsk} (ha : a ∈ tableAsks y rd g) :
    (∃ mn, '@' ∉ mn.toList ∧ a.name = mn ++ "@" ++ a.point ∧
      a.L = (if a.lng then 2 ^ y.h.la else y.T) ∧
      ((a.lng = true ∧ (a.point ∈ rd.rdAF ∨ a.point ∈ rd.rdQA ∨ a.point ∈ rd.rdXI ∨
          a.point = "Z_E" ∨ a.point ∈ rd.rdXO)) ∨
        (a.lng = false ∧ (a.point ∈ rd.rdAD ∨ a.point ∈ rd.rdAR ∨ a.point ∈ rd.rdQS)))) ∨
      ('@' ∉ a.name.toList ∧ a.point = "") := by
  unfold tableAsks at ha
  simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with (((((((⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩) | ⟨n, hn, rfl⟩) | h) | ⟨n, hn, rfl⟩) |
    ⟨n, hn, rfl⟩) | ⟨n, hn, rfl⟩) | h) | (rfl | rfl | rfl)
  · exact Or.inl ⟨"af", by decide, rfl, rfl, Or.inl ⟨rfl, Or.inl hn⟩⟩
  · exact Or.inl ⟨"qa", by decide, rfl, rfl, Or.inl ⟨rfl, Or.inr (Or.inl hn)⟩⟩
  · exact Or.inl ⟨"xbI", by decide, rfl, rfl, Or.inl ⟨rfl, Or.inr (Or.inr (Or.inl hn))⟩⟩
  · split at h
    · simp only [List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at h
      obtain ⟨n, rfl, rfl⟩ := h
      exact Or.inl ⟨"xbI", by decide, rfl, rfl,
        Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩⟩
    · cases h
  · exact Or.inl ⟨"xbO", by decide, rfl, rfl,
      Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr hn)))⟩⟩
  · exact Or.inl ⟨"ad", by decide, rfl, rfl, Or.inr ⟨rfl, Or.inl hn⟩⟩
  · exact Or.inl ⟨"ar", by decide, rfl, rfl, Or.inr ⟨rfl, Or.inr (Or.inl hn)⟩⟩
  · split at h
    · simp only [List.mem_map] at h
      obtain ⟨n, hn, rfl⟩ := h
      exact Or.inl ⟨"qa", by decide, rfl, rfl, Or.inr ⟨rfl, Or.inr (Or.inr hn)⟩⟩
    · cases h
  · exact Or.inr ⟨by show '@' ∉ ("b-bits-0" : String).toList; decide, rfl⟩
  · exact Or.inr ⟨by show '@' ∉ ("b-bits-1" : String).toList; decide, rfl⟩
  · exact Or.inr ⟨by show '@' ∉ ("b-pin" : String).toList; decide, rfl⟩

/-- A list of one member or none. -/
theorem mem_one {c : Prop} [Decidable c] {x n : String} (h : n ∈ (if c then [x] else [])) :
    n = x := by
  split at h
  · exact List.mem_singleton.mp h
  · cases h

/-- The points of a long family's list, as readsOf lays it. -/
theorem long_pts {a b c d e : Prop} [Decidable a] [Decidable b] [Decidable c] [Decidable d]
    [Decidable e] {n : String}
    (h : n ∈ (if a then ["Z"] else []) ++ (if b then ["Z_V"] else []) ++
      (if c then ["Y"] else []) ++ (if d then ["Z_a"] ++ (if e then ["Z_b"] else []) else [])) :
    n ∈ ["Z", "Z_V", "Y", "Z_a", "Z_b"] := by
  rcases List.mem_append.mp h with h | h
  · rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · rw [mem_one h]; decide
      · rw [mem_one h]; decide
    · rw [mem_one h]; decide
  · split at h
    · rcases List.mem_append.mp h with h | h
      · rw [List.mem_singleton.mp h]; decide
      · rw [mem_one h]; decide
    · cases h

/-- The points of a short family's list. -/
theorem short_pts {a b c : Prop} [Decidable a] [Decidable b] [Decidable c] {n : String}
    (h : n ∈ (if a then ["zt"] else []) ++ (if b then ["P_V", "r_tV"] else []) ++
      (if c then ["rt"] else [])) : n ∈ ["zt", "P_V", "r_tV", "rt"] := by
  rcases List.mem_append.mp h with h | h
  · rcases List.mem_append.mp h with h | h
    · rw [mem_one h]; decide
    · split at h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl <;> decide
      · cases h
  · rw [mem_one h]; decide

/-- **The points that readsOf lists.** CONDITIONAL: on the return. -/
theorem rd_points {y : Lay} {rd : Reads} (e : readsOf y = .ok rd) :
    (∀ n, (n ∈ rd.rdAF ∨ n ∈ rd.rdQA ∨ n ∈ rd.rdXI ∨ n ∈ rd.rdXO) →
      n ∈ ["Z", "Z_V", "Y", "Z_a", "Z_b"]) ∧
    (∀ n, (n ∈ rd.rdAD ∨ n ∈ rd.rdAR ∨ n ∈ rd.rdQS) → n ∈ ["zt", "P_V", "r_tV", "rt"]) := by
  unfold Layer.readsOf at e
  dsimp only at e
  obtain ⟨_, e⟩ := ok_of_refuse e
  cases e
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · rcases hn with h | h | h | h <;> exact long_pts h
  · rcases hn with h | h | h <;> exact short_pts h

/-- **The name says the point.** -/
theorem point_of_name {y : Lay} {rd : Reads} {g : ℕ} {a : TableAsk} (ha : a ∈ tableAsks y rd g)
    {mn Z : String} (hm : '@' ∉ mn.toList) (e : a.name = mn ++ "@" ++ Z) : a.point = Z := by
  rcases ask_named ha with ⟨mn', h', en, _, _⟩ | ⟨h, _⟩
  · exact (name_split h' hm (en.symm.trans e)).2
  · exfalso
    apply h
    rw [e, String.toList_append, String.toList_append]
    simp

/-- **A family at a token point is short**, with runs of T rows. CONDITIONAL: on the return. -/
theorem short_of_point {y : Lay} {rd : Reads} (hrd : readsOf y = .ok rd) {g : ℕ} {a : TableAsk}
    (ha : a ∈ tableAsks y rd g) (hp : a.point ∈ ["zt", "P_V", "r_tV", "rt"]) :
    a.lng = false ∧ a.L = y.T := by
  rcases ask_named ha with ⟨_, _, _, hL, (⟨hl, hq⟩ | ⟨hl, _⟩)⟩ | ⟨_, h⟩
  · exfalso
    have hq' : a.point ∈ ["Z", "Z_V", "Y", "Z_a", "Z_b", "Z_E"] := by
      rcases hq with q | q | q | q | q
      · exact List.mem_append_left ["Z_E"] ((rd_points hrd).1 _ (Or.inl q))
      · exact List.mem_append_left ["Z_E"] ((rd_points hrd).1 _ (Or.inr (Or.inl q)))
      · exact List.mem_append_left ["Z_E"] ((rd_points hrd).1 _ (Or.inr (Or.inr (Or.inl q))))
      · rw [q]; decide
      · exact List.mem_append_left ["Z_E"] ((rd_points hrd).1 _ (Or.inr (Or.inr (Or.inr q))))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hq'
    rcases hp with e | e | e | e <;> rw [e] at hq' <;> revert hq' <;> decide
  · rw [hl] at hL
    exact ⟨hl, hL⟩
  · exfalso
    rw [h] at hp
    revert hp
    decide

/-- **A family at a long point is long**, with runs of 2 ^ la rows. CONDITIONAL: on the return. -/
theorem long_of_point {y : Lay} {rd : Reads} (hrd : readsOf y = .ok rd) {g : ℕ} {a : TableAsk}
    (ha : a ∈ tableAsks y rd g) (hp : a.point ∈ ["Z", "Z_V", "Y", "Z_a", "Z_b", "Z_E"]) :
    a.lng = true ∧ a.L = 2 ^ y.h.la := by
  rcases ask_named ha with ⟨_, _, _, hL, (⟨hl, _⟩ | ⟨hl, hq⟩)⟩ | ⟨_, h⟩
  · rw [hl] at hL
    exact ⟨hl, hL⟩
  · exfalso
    have hq' := (rd_points hrd).2 _ hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hq'
    rcases hp with e | e | e | e | e | e <;> rw [e] at hq' <;> revert hq' <;> decide
  · exfalso
    rw [h] at hp
    revert hp
    decide

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.cut_at_sign
#print axioms OnBytes.Road.K4.C.name_split
#print axioms OnBytes.Road.K4.C.ask_named
#print axioms OnBytes.Road.K4.C.mem_one
#print axioms OnBytes.Road.K4.C.long_pts
#print axioms OnBytes.Road.K4.C.short_pts
#print axioms OnBytes.Road.K4.C.rd_points
#print axioms OnBytes.Road.K4.C.point_of_name
#print axioms OnBytes.Road.K4.C.short_of_point
#print axioms OnBytes.Road.K4.C.long_of_point
