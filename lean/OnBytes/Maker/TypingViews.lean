-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/TypingViews.lean: the rounds of a file's chain as read fit the rounds' data of the
reduction of a whole file, at a transcript that holds what was read.

The reduction of OnBytes/Maker/Whole.lean hands three views to its run: one for each chain, made of
the chain's part of the transcript, of the stored table's string, and of what the drawn positions
ask for. The program's blocks run on the views that the strict reader forms of the chains as read
(`Fmt.viewX`). OnBytes/Maker/ViewsAlike.lean ties the two
. This file has the part of that tie that speaks of one chain's opened
columns: round by round, what
OnBytes/Maker/ViewOrder.lean asks (`RoundFits`).

What `chain_fits` asks, in five groups.
  The tables. tabs and etab hold the file's columns (`TabsHold`, `ExtHolds`,
    OnBytes/Maker/TablesLaws.lean): so do those that `tabsW` or `tabsWFull`, `extTabW` or
    `extTabWFull` return (OnBytes/Maker/Tables.lean).
  The data. A test that can be evaluated: `shapesFit` (OnBytes/Maker/ViewTests.lean): the shape of
    each tree in the rounds' data is the one in the data's table.
  The reading. `ListedAsDrawn` (OnBytes/Maker/ReadFacts.lean): each opening is listed at the list of
    the round's draws, cut to the tree's depth; a stored table's at its part of the draws.
  The transcript and the stored string. At a position where `opensT` has an opening the transcript
    holds its symbol; the string holds place and column at a listed place.
  The two lists. They have one length; each round has as many openings as its data say; the own
    trees' and the stored tables' openings stand among the file's.

Main theorems.
  `colOf_tree`, `colOf_table`: the look-up finds a listed column.
  `chain_fits`: the rounds of a chain fit.
  `roundsFit_spec`: what the test `roundsFit` says: the data have as many rounds as were read, and
    each round has as many openings as its data have stored tables and trees.
  `split_last`: a list that has a last member is the others and that one.

What is not claimed. None of the hypotheses. Nothing on soundness.


-/
import OnBytes.Maker.ViewOrder
import OnBytes.Maker.TablesLaws
import OnBytes.Maker.TypingTLaws
import OnBytes.Maker.ViewTests
import OnBytes.Maker.ReadFacts

set_option autoImplicit false

namespace OnBytes.Maker

open Iop _root_.Compile _root_.Run _root_.Run.PQ

/-! ## Lists -/

/-- Two lists of one length whose pairs are related are related member by member. -/
theorem forall₂_of_zip {α β : Type} {R : α → β → Prop} : ∀ (l₁ : List α) (l₂ : List β),
    l₁.length = l₂.length → (∀ p ∈ l₁.zip l₂, R p.1 p.2) → List.Forall₂ R l₁ l₂
  | [], [], _, _ => .nil
  | [], _ :: _, h, _ => by cases h
  | _ :: _, [], h, _ => by cases h
  | a :: l₁, b :: l₂, h, hp =>
    .cons (hp (a, b) (by rw [List.zip_cons_cons]; exact List.mem_cons_self))
      (forall₂_of_zip l₁ l₂ (Nat.succ.inj h) fun p hm =>
        hp p (by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hm))

/-- A pair of two lists without their last members is a pair of the lists, if these have one
length. -/
theorem mem_zip_dropLast {α β : Type} : ∀ (l₁ : List α) (l₂ : List β), l₁.length = l₂.length →
    ∀ p ∈ l₁.dropLast.zip l₂.dropLast, p ∈ l₁.zip l₂
  | [], _, _, _, hp => by simp at hp
  | _ :: _, [], h, _, _ => by cases h
  | [_], [_], _, _, hp => by simp at hp
  | [_], _ :: _ :: _, h, _, _ => by simp at h
  | _ :: _ :: _, [_], h, _, _ => by simp at h
  | a :: a' :: l₁, b :: b' :: l₂, h, p, hp => by
    rw [List.dropLast_cons₂, List.dropLast_cons₂, List.zip_cons_cons] at hp
    rw [List.zip_cons_cons]
    rcases List.mem_cons.1 hp with e | hp'
    · exact e ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_zip_dropLast (a' :: l₁) (b' :: l₂) (Nat.succ.inj h) p hp')

/-! ## The data -/

/-- The depth is the shape's. -/
theorem WholeD.depth_shape (D : WholeD) (j : ℕ) : D.depth j = (D.shape j).map (·.a) := by
  unfold WholeD.depth WholeD.shape
  split
  · rfl
  · split <;> rfl

theorem shapesFit_at {a : ℕ} {W : Three.Whole} (h : shapesFit a W = true) {j : ℕ} {t : Three.Tree}
    (ht : W.table[j]? = some t) : (WholeD.of a W).shape j = some t.shape := by
  have hj : j < W.table.length := (List.getElem?_eq_some_iff.1 ht).1
  have h1 := List.all_eq_true.1 h j (List.mem_range.2 hj)
  rw [beq_iff_eq, ht] at h1
  exact h1

/-! ## The transcript -/

section
variable (C : CK) (D : WholeD) (y : (oneExternalString (2 ^ D.a) SgX).Str) (τ₁ : Iop.Tr (uLT C D.ds₁))
  (τ₂ : Iop.Tr (uLT C D.ds₂)) (τ₃ : Iop.Tr (uLT C D.ds₃)) (tabs : List (ℕ × List (ℕ × Row3)))

/-- **The look-up at a tree finds the tables' column.** -/
theorem colOf_tree
    (h₁ : ∀ p op, opensT C D.ds₁ 0 tabs p = some op → τ₁.read p = op.sym)
    (h₂ : ∀ p op, opensT C D.ds₂ D.t₁ tabs p = some op → τ₂.read p = op.sym)
    (h₃ : ∀ p op, opensT C D.ds₃ (D.t₁ + D.t₂) tabs p = some op → τ₃.read p = op.sym)
    (j x : ℕ) (sh : Fmt.Shape) (tab : List (ℕ × Row3)) (c : List UInt64) (s : Rom.Bits)
    (pt : List (Dig 256)) (hsh : D.shape j = some sh) (hx : x < 2 ^ sh.a)
    (ht : tabs.lookup j = some tab) (hl : tab.lookup x = some (c, s, pt)) (hc : c.length = sh.W) :
    colOf C D y τ₁ τ₂ τ₃ (.tree j x) = some c := by
  unfold WholeD.shape at hsh
  show (if j < D.t₁ then colAtST C D.ds₁ τ₁ j x
    else if j - D.t₁ < D.t₂ then colAtST C D.ds₂ τ₂ (j - D.t₁) x
    else colAtST C D.ds₃ τ₃ (j - D.t₁ - D.t₂) x) = some c
  by_cases c1 : j < D.t₁
  · rw [if_pos c1] at hsh ⊢
    exact colAtST_opensT C D.ds₁ 0 tabs τ₁ j x sh tab c s pt (fun p op _ ho => h₁ p op ho) hsh hx
      (by rw [Nat.zero_add]; exact ht) hl hc
  · rw [if_neg c1] at hsh ⊢
    by_cases c2 : j - D.t₁ < D.t₂
    · rw [if_pos c2] at hsh ⊢
      exact colAtST_opensT C D.ds₂ D.t₁ tabs τ₂ (j - D.t₁) x sh tab c s pt
        (fun p op _ ho => h₂ p op ho) hsh hx
        (by rw [show D.t₁ + (j - D.t₁) = j by omega]; exact ht) hl hc
    · rw [if_neg c2] at hsh ⊢
      exact colAtST_opensT C D.ds₃ (D.t₁ + D.t₂) tabs τ₃ (j - D.t₁ - D.t₂) x sh tab c s pt
        (fun p op _ ho => h₃ p op ho) hsh hx
        (by rw [show D.t₁ + D.t₂ + (j - D.t₁ - D.t₂) = j by omega]; exact ht) hl hc

/-- **The look-up at the stored table finds the string's column.** -/
theorem colOf_table (item x : ℕ) (c : List UInt64) (hx : x < 2 ^ D.a) (hy : y ⟨x, hx⟩ = (x, c)) :
    colOf C D y τ₁ τ₂ τ₃ (.table item x) = some c := by
  show (if h : x < 2 ^ D.a then some (y ⟨x, h⟩).2 else none) = some c
  rw [dif_pos hx, hy]

end

/-! ## A chain's rounds fit -/

section
variable (C : CK) (a : ℕ) (W : Three.Whole) (sb : ℕ) (r : Proof.TailRead)
  (tabs : List (ℕ × List (ℕ × Row3))) (etab : List (ℕ × Row3))
  (y : (oneExternalString (2 ^ (WholeD.of a W).a) SgX).Str) (τ₁ : Iop.Tr (uLT C (WholeD.of a W).ds₁))
  (τ₂ : Iop.Tr (uLT C (WholeD.of a W).ds₂)) (τ₃ : Iop.Tr (uLT C (WholeD.of a W).ds₃))

/-- **The rounds of a chain fit.** dl, ros: the chain's data and its rounds as read, of one length,
each round with as many openings as its data says; all their openings are among the file's
(`hown`, `hsto`). c: the chain's number. -/
theorem chain_fits (htabs : TabsHold W sb r tabs) (hext : ExtHolds a W r etab)
    (hshape : shapesFit a W = true)
    (h₁ : ∀ p op, opensT C (WholeD.of a W).ds₁ 0 tabs p = some op → τ₁.read p = op.sym)
    (h₂ : ∀ p op, opensT C (WholeD.of a W).ds₂ (WholeD.of a W).t₁ tabs p = some op →
      τ₂.read p = op.sym)
    (h₃ : ∀ p op, opensT C (WholeD.of a W).ds₃ ((WholeD.of a W).t₁ + (WholeD.of a W).t₂) tabs p =
      some op → τ₃.read p = op.sym)
    (hy : ∀ (x : ℕ) (hx : x < 2 ^ a) c s pt, etab.lookup x = some (c, s, pt) →
      y ⟨x, hx⟩ = (x, c))
    (c : ℕ) (dl : List Three.RDL) (ros : List Fmt.RoundOut) (hlen : dl.length = ros.length)
    (hop : ∀ p ∈ dl.zip ros, p.2.opens.length = p.1.stored.length + p.1.opens.length)
    (hown : ∀ p ∈ dl.zip ros, ∀ q ∈ p.1.opens.zip (p.2.opens.drop p.1.stored.length),
      q ∈ ownRowsW W r)
    (hsto : ∀ p ∈ dl.zip ros, ∀ q ∈ p.1.stored.zip p.2.opens, q ∈ storedRowsW W r)
    (hlist : ListedAsDrawn a dl ros) :
    List.Forall₂ (RoundFits a (WholeD.of a W).depth (W.key c)
        (if c = 2 then Three.first₃ W.t₁ else 0) (colOf C (WholeD.of a W) y τ₁ τ₂ τ₃))
      (dl.map rdtOf) ros := by
  rw [List.forall₂_map_left_iff]
  refine forall₂_of_zip dl ros hlen fun p hp => ?_
  obtain ⟨d, ro⟩ := p
  have hl := hlist (d, ro) hp
  have hlo : ro.opens.length = d.stored.length + d.opens.length := hop (d, ro) hp
  refine ⟨?_, ?_⟩
  · -- the stored tables
    show List.Forall₂ _ d.stored (ro.opens.take d.stored.length)
    refine forall₂_of_zip _ _ (by rw [List.length_take]; omega) fun q hq => ?_
    have hq' : q ∈ d.stored.zip ro.opens := by
      have e := zip_take_length d.stored ro.opens
      exact e ▸ hq
    obtain ⟨t, z⟩ := q
    obtain ⟨e1, e2, -, hok⟩ := hext.row t z (hsto (d, ro) hp _ hq')
    refine ⟨hl.1 _ hq', (TieTree.ok_spec (asOpenB z) _ _ hok).1, fun x c' hm => ?_⟩
    obtain ⟨s, pt, hlk⟩ := hext.look t z (hsto (d, ro) hp _ hq') x c' hm
    have hx : x < 2 ^ a := by
      have := (TieTree.ok_list (asOpenB z) _ _ hok).2.1 x (List.of_mem_zip hm).1
      rw [show (asOpenB z).a = z.1.a from rfl, e1, e2] at this
      exact this
    exact colOf_table C (WholeD.of a W) y τ₁ τ₂ τ₃ t.item x c' hx (hy x hx c' s pt hlk)
  · -- the trees
    show List.Forall₂ _ d.opens (ro.opens.drop d.stored.length)
    refine forall₂_of_zip _ _ (by rw [List.length_drop]; omega) fun q hq => ?_
    obtain ⟨j, z⟩ := q
    have hz : (j, z) ∈ ownRowsW W r := hown (d, ro) hp _ hq
    obtain ⟨t, ht, e1, hok⟩ := htabs.row j z hz
    have hsh := shapesFit_at hshape ht
    refine ⟨?_, hl.2 z (List.of_mem_zip hq).2, (TieTree.ok_spec (asOpenB z) _ _ hok).1, ?_,
      fun x c' hm => ?_⟩
    · rw [WholeD.depth_shape, hsh, e1]
      rfl
    · show ((W.table[j]?).map (·.shape.tree)).getD 0 - _ = _
      rw [ht, e1]
      rfl
    · obtain ⟨tab, s, pt, hlt, hlx⟩ := htabs.look j z hz x c' hm
      have hx : x < 2 ^ t.shape.a := by
        have := (TieTree.ok_list (asOpenB z) _ _ hok).2.1 x (List.of_mem_zip hm).1
        rw [show (asOpenB z).a = z.1.a from rfl, e1] at this
        exact this
      exact colOf_tree C (WholeD.of a W) y τ₁ τ₂ τ₃ tabs h₁ h₂ h₃ j x t.shape tab c' s pt hsh hx
        hlt hlx ((TieTree.ok_list (asOpenB z) _ _ hok).2.2 c' (List.of_mem_zip hm).2)

end

/-! ## The test on the rounds, and a list's last member -/

/-- What `roundsFit` says. -/
theorem roundsFit_spec {ds : List Three.RDL} {o : Fmt.ChainOut} (h : roundsFit ds o = true) :
    ds.length = o.rounds.toList.length ∧
      ∀ p ∈ ds.zip o.rounds.toList, p.2.opens.length = p.1.stored.length + p.1.opens.length := by
  unfold roundsFit at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact ⟨by rw [h.1, Array.length_toList], h.2⟩

/-- Two lists of one length, the first with a last member: both are what stands before the last
member and that member, and the two last members are a pair of the lists. -/
theorem split_last {α β : Type} (l₁ : List α) (l₂ : List β) (h : l₁.length = l₂.length) (a : α)
    (ha : l₁.getLast? = some a) :
    ∃ b, l₁ = l₁.dropLast ++ [a] ∧ l₂ = l₂.dropLast ++ [b] ∧ (a, b) ∈ l₁.zip l₂ := by
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.1 ha
  have hne : l₂ ≠ [] := by
    intro e
    rw [e] at h
    simp at h
  obtain ⟨L, b, rfl⟩ : ∃ L b, l₂ = L ++ [b] :=
    ⟨l₂.dropLast, l₂.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
  have hl : ys.length = L.length := by simpa using h
  refine ⟨b, by rw [List.dropLast_concat], by rw [List.dropLast_concat], ?_⟩
  rw [List.zip_append hl]
  simp

end OnBytes.Maker
