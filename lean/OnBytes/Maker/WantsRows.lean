-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/WantsRows.lean: what the drawn positions of a chain ask for is what the chain's
openings list.

The reduction of a whole file (OnBytes/Maker/Whole.lean) makes, from each round's drawn positions, a
list of wants: a tree at a leaf, or the stored table at a place. A file as read holds, round by
round, openings, each with the list of places at which it was opened. Where each opening is listed
at the list of its round's draws (`ListedAsDrawn`, OnBytes/Maker/ReadFacts.lean), and under the
premises below, the two say the same.

  `tree_wanted`, `table_wanted`
        one chain: the draws as read ask for the tree j at x exactly if an opening of j in the chain
        lists x; for the stored table at x exactly if an opening of a stored table lists x.
  `ownRows_less`, `storedRows_less`
        a chain whose last round opens nothing has the openings of its rounds before the last.

The premises of `tree_wanted`, four: as many rounds of data as rounds read; each round as read has
as many openings as its data have stored tables and trees; dep gives to each opened tree the depth
of the shape as read beside it; `ListedAsDrawn`. `table_wanted` has the first, the second and the
fourth. None is shown here.

OnBytes/Maker/TypingAlike.lean has the whole file (`tree_wanted_read`,
`table_wanted_read`). There `ListedAsDrawn` stays a premise, once for each chain; the other premises
come from `TabsHold` or the test `fitsW`, and the tests `shapesFit` and `sealBare`, which are
premises there.

Not claimed. Nothing on hashes; nothing on soundness.


-/
import OnBytes.Maker.TypingViews
import OnBytes.Maker.ReadsAt

set_option autoImplicit false

namespace OnBytes.Maker

open Iop _root_.Compile _root_.Run _root_.Run.PQ

/-! ## Lists -/

/-- A member of the first of two lists has a partner, if the second is as long. -/
theorem exists_zip_of_mem {α β : Type} : ∀ (l₁ : List α) (l₂ : List β) (a : α),
    l₁.length ≤ l₂.length → a ∈ l₁ → ∃ b, (a, b) ∈ l₁.zip l₂
  | [], _, _, _, h => by cases h
  | _ :: _, [], _, h, _ => by simp at h
  | x :: l₁, y :: l₂, a, h, ha => by
    rw [List.zip_cons_cons]
    rcases List.mem_cons.1 ha with e | ha'
    · exact ⟨y, e ▸ List.mem_cons_self⟩
    · obtain ⟨b, hb⟩ := exists_zip_of_mem l₁ l₂ a (Nat.le_of_succ_le_succ h) ha'
      exact ⟨b, List.mem_cons_of_mem _ hb⟩

/-! ## One round -/

theorem mem_treeWants {dep : ℕ → Option ℕ} {poss : List ℕ} {j j' x : ℕ} :
    Want.tree j x ∈ treeWants dep poss j' ↔
      j = j' ∧ ∃ b, dep j = some b ∧ x ∈ Fmt.listOf (poss.map (· % 2 ^ b)) := by
  unfold treeWants
  cases h : dep j' with
  | none =>
    constructor
    · intro hm
      cases hm
    · rintro ⟨rfl, b, hb, -⟩
      rw [h] at hb
      cases hb
  | some b =>
    constructor
    · intro hm
      obtain ⟨y, hy, e⟩ := List.mem_map.1 hm
      cases e
      exact ⟨rfl, b, h, hy⟩
    · rintro ⟨rfl, b', hb, hx⟩
      obtain rfl : b = b' := Option.some.inj (h.symm.trans hb)
      exact List.mem_map.2 ⟨x, hx, rfl⟩

theorem table_not_mem_trees (dep : ℕ → Option ℕ) (poss : List ℕ) (js : List ℕ) (item x : ℕ) :
    Want.table item x ∉ js.flatMap (treeWants dep poss) := by
  intro h
  obtain ⟨j, -, hj⟩ := List.mem_flatMap.1 h
  unfold treeWants at hj
  cases e : dep j with
  | none => rw [e] at hj; cases hj
  | some b =>
    rw [e] at hj
    obtain ⟨y, -, e'⟩ := List.mem_map.1 hj
    cases e'

theorem tree_not_mem_stored (a : ℕ) (poss : List ℕ) (ts : List Fmt.Stored) (j x : ℕ) :
    Want.tree j x ∉ ts.flatMap fun s =>
      (Fmt.listOf ((Fmt.partOf s poss).map (· % 2 ^ a))).map fun x => Want.table s.item x := by
  intro h
  obtain ⟨s, -, hs⟩ := List.mem_flatMap.1 h
  obtain ⟨y, -, e⟩ := List.mem_map.1 hs
  cases e

/-! ## One chain -/

/-- **The draws as read ask for the tree j at x exactly if an opening of j in the chain lists x.**
dep: the trees' depths. -/
theorem tree_wanted (a : ℕ) (dep : ℕ → Option ℕ) :
    ∀ (dl : List Three.RDL) (ros : List Fmt.RoundOut), dl.length = ros.length →
      (∀ p ∈ dl.zip ros, p.2.opens.length = p.1.stored.length + p.1.opens.length) →
      (∀ p ∈ dl.zip ros, ∀ q ∈ p.1.opens.zip (p.2.opens.drop p.1.stored.length),
        dep q.1 = some q.2.1.a) →
      ListedAsDrawn a dl ros → ∀ j x,
      (Want.tree j x ∈ wantsOf a dep (dl.map rdtOf) (ros.map (·.drawn)) ↔
        ∃ z, (j, z) ∈ ((dl.zip ros).flatMap fun u =>
          u.1.opens.zip (u.2.opens.drop u.1.stored.length)) ∧ x ∈ z.2.1)
  | [], [], _, _, _, _, j, x => by
    constructor
    · intro h
      cases h
    · rintro ⟨z, h, -⟩
      cases h
  | [], _ :: _, h, _, _, _, _, _ => by cases h
  | _ :: _, [], h, _, _, _, _, _ => by cases h
  | d :: dl, ro :: ros, hlen, hop, hdep, hl, j, x => by
    have hin : (d, ro) ∈ (d :: dl).zip (ro :: ros) := by
      rw [List.zip_cons_cons]
      exact List.mem_cons_self
    have hlo : ro.opens.length = d.stored.length + d.opens.length := hop _ hin
    have sub : ∀ p ∈ dl.zip ros, p ∈ (d :: dl).zip (ro :: ros) := fun p hp => by
      rw [List.zip_cons_cons]
      exact List.mem_cons_of_mem _ hp
    have ih := tree_wanted a dep dl ros (Nat.succ.inj hlen) (fun p hp => hop p (sub p hp))
      (fun p hp => hdep p (sub p hp)) (fun p hp => hl p (sub p hp)) j x
    have head : Want.tree j x ∈ d.opens.flatMap (treeWants dep ro.drawn.poss) ↔
        ∃ z, (j, z) ∈ d.opens.zip (ro.opens.drop d.stored.length) ∧ x ∈ z.2.1 := by
      constructor
      · intro h
        obtain ⟨j', hj', hm⟩ := List.mem_flatMap.1 h
        obtain ⟨rfl, b, hb, hx⟩ := mem_treeWants.1 hm
        obtain ⟨z, hz⟩ := exists_zip_of_mem d.opens (ro.opens.drop d.stored.length) j
          (by rw [List.length_drop]; omega) hj'
        obtain rfl : b = z.1.a := Option.some.inj (hb.symm.trans (hdep _ hin _ hz))
        exact ⟨z, hz, by rw [(hl _ hin).2 z (List.of_mem_zip hz).2]; exact hx⟩
      · rintro ⟨z, hz, hx⟩
        refine List.mem_flatMap.2 ⟨j, (List.of_mem_zip hz).1, mem_treeWants.2
          ⟨rfl, z.1.a, hdep _ hin _ hz, ?_⟩⟩
        rw [← (hl _ hin).2 z (List.of_mem_zip hz).2]
        exact hx
    rw [List.map_cons, List.map_cons, wantsOf_cons, List.mem_append, List.mem_append,
      List.zip_cons_cons, List.flatMap_cons]
    constructor
    · rintro ((h | h) | h)
      · exact absurd h (tree_not_mem_stored a _ _ j x)
      · obtain ⟨z, hz, hx⟩ := head.1 h
        exact ⟨z, List.mem_append_left _ hz, hx⟩
      · obtain ⟨z, hz, hx⟩ := ih.1 h
        exact ⟨z, List.mem_append_right _ hz, hx⟩
    · rintro ⟨z, hz, hx⟩
      rcases List.mem_append.1 hz with h | h
      · exact Or.inl (Or.inr (head.2 ⟨z, h, hx⟩))
      · exact Or.inr (ih.2 ⟨z, h, hx⟩)

/-- **The draws as read ask for the stored table at x exactly if an opening of a stored table in the
chain lists x.** -/
theorem table_wanted (a : ℕ) (dep : ℕ → Option ℕ) :
    ∀ (dl : List Three.RDL) (ros : List Fmt.RoundOut), dl.length = ros.length →
      (∀ p ∈ dl.zip ros, p.2.opens.length = p.1.stored.length + p.1.opens.length) →
      ListedAsDrawn a dl ros → ∀ x,
      ((∃ item, Want.table item x ∈ wantsOf a dep (dl.map rdtOf) (ros.map (·.drawn))) ↔
        ∃ t z, (t, z) ∈ ((dl.zip ros).flatMap fun u => u.1.stored.zip u.2.opens) ∧ x ∈ z.2.1)
  | [], [], _, _, _, x => by
    constructor
    · rintro ⟨_, h⟩
      cases h
    · rintro ⟨_, _, h, -⟩
      cases h
  | [], _ :: _, h, _, _, _ => by cases h
  | _ :: _, [], h, _, _, _ => by cases h
  | d :: dl, ro :: ros, hlen, hop, hl, x => by
    have hin : (d, ro) ∈ (d :: dl).zip (ro :: ros) := by
      rw [List.zip_cons_cons]
      exact List.mem_cons_self
    have hlo : ro.opens.length = d.stored.length + d.opens.length := hop _ hin
    have sub : ∀ p ∈ dl.zip ros, p ∈ (d :: dl).zip (ro :: ros) := fun p hp => by
      rw [List.zip_cons_cons]
      exact List.mem_cons_of_mem _ hp
    have ih := table_wanted a dep dl ros (Nat.succ.inj hlen) (fun p hp => hop p (sub p hp))
      (fun p hp => hl p (sub p hp)) x
    have head : (∃ item, Want.table item x ∈ d.stored.flatMap fun s =>
          (Fmt.listOf ((Fmt.partOf s ro.drawn.poss).map (· % 2 ^ a))).map fun x =>
            Want.table s.item x) ↔
        ∃ t z, (t, z) ∈ d.stored.zip ro.opens ∧ x ∈ z.2.1 := by
      constructor
      · rintro ⟨item, h⟩
        obtain ⟨t, ht, hm⟩ := List.mem_flatMap.1 h
        obtain ⟨y, hy, e⟩ := List.mem_map.1 hm
        cases e
        obtain ⟨z, hz⟩ := exists_zip_of_mem d.stored ro.opens t (by omega) ht
        exact ⟨t, z, hz, by rw [(hl _ hin).1 _ hz]; exact hy⟩
      · rintro ⟨t, z, hz, hx⟩
        refine ⟨t.item, List.mem_flatMap.2 ⟨t, (List.of_mem_zip hz).1, List.mem_map.2 ⟨x, ?_, rfl⟩⟩⟩
        rw [← (hl _ hin).1 _ hz]
        exact hx
    rw [List.map_cons, List.map_cons, wantsOf_cons, List.zip_cons_cons, List.flatMap_cons]
    constructor
    · rintro ⟨item, h⟩
      rcases List.mem_append.1 h with h | h
      · rcases List.mem_append.1 h with h | h
        · obtain ⟨t, z, hz, hx⟩ := head.1 ⟨item, h⟩
          exact ⟨t, z, List.mem_append_left _ hz, hx⟩
        · exact absurd h (table_not_mem_trees dep _ _ item x)
      · obtain ⟨t, z, hz, hx⟩ := ih.1 ⟨item, h⟩
        exact ⟨t, z, List.mem_append_right _ hz, hx⟩
    · rintro ⟨t, z, hz, hx⟩
      rcases List.mem_append.1 hz with h | h
      · obtain ⟨item, hi⟩ := head.2 ⟨t, z, h, hx⟩
        exact ⟨item, List.mem_append_left _ (List.mem_append_left _ hi)⟩
      · obtain ⟨item, hi⟩ := ih.2 ⟨t, z, h, hx⟩
        exact ⟨item, List.mem_append_right _ hi⟩

/-! ## A chain whose last round opens nothing -/

theorem flatMap_zip_less {α β γ : Type} (f : α × β → List γ) (l₁ : List α) (l₂ : List β)
    (h : l₁.length = l₂.length) (a : α) (ha : l₁.getLast? = some a) (hf : ∀ b, f (a, b) = []) :
    (l₁.zip l₂).flatMap f = (l₁.dropLast.zip l₂.dropLast).flatMap f := by
  obtain ⟨b, e1, e2, -⟩ := split_last l₁ l₂ h a ha
  have hl : l₁.dropLast.length = l₂.dropLast.length := by
    rw [List.length_dropLast, List.length_dropLast, h]
  conv_lhs => rw [e1, e2, List.zip_append hl]
  rw [List.flatMap_append]
  simp [hf]

/-- What `sealBare` says. -/
theorem sealBare_spec {W : Three.Whole} (h : sealBare W = true) :
    ∃ d, W.ds₁.getLast? = some d ∧ d.stored = [] ∧ d.opens = [] := by
  unfold sealBare at h
  cases hg : W.ds₁.getLast? with
  | none => rw [hg] at h; cases h
  | some d =>
    rw [hg] at h
    simp only [Bool.and_eq_true, List.isEmpty_iff] at h
    exact ⟨d, rfl, h.1, h.2⟩

theorem ownRows_less {W : Three.Whole} (h : sealBare W = true) (o : Fmt.ChainOut)
    (hlen : W.ds₁.length = o.rounds.toList.length) :
    ownRows W.ds₁ o = (W.ds₁.dropLast.zip o.rounds.toList.dropLast).flatMap fun u =>
      u.1.opens.zip (u.2.opens.drop u.1.stored.length) := by
  obtain ⟨d, hd, -, ho⟩ := sealBare_spec h
  exact flatMap_zip_less _ _ _ hlen d hd fun b => by
    show d.opens.zip _ = []
    rw [ho, List.zip_nil_left]

theorem storedRows_less {W : Three.Whole} (h : sealBare W = true) (o : Fmt.ChainOut)
    (hlen : W.ds₁.length = o.rounds.toList.length) :
    storedRows W.ds₁ o = (W.ds₁.dropLast.zip o.rounds.toList.dropLast).flatMap fun u =>
      u.1.stored.zip u.2.opens := by
  obtain ⟨d, hd, hs, -⟩ := sealBare_spec h
  exact flatMap_zip_less _ _ _ hlen d hd fun b => by
    show d.stored.zip _ = []
    rw [hs, List.zip_nil_left]

end OnBytes.Maker
