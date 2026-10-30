-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/RowBack.lean: the item "row m c" goes back over a step that leaves what the item
reads of the record. It joins `rowSaysFirst_back` (Johnson/Desc/First/Close/Law/FillRowRides.lean)
with its two premises on the class's rows and on the book, from five plain facts on the two records.

Main names:
  `RowKept s s'`: the five facts: the codes stay; every message in front stands behind with its
    shape, mark and sample rows; every group in front stands behind with its open rows; every
    message in front keeps its place in the book; the tree at such a place stays.
  `RowKept.extends`, `RowKept.bookKept`, `classRows_sub`: what `rowSaysFirst_back` asks.
  `row_back`: at `rowSays N (wordsAtFirst arr)`. `row_holds_back`: at `Item.holds`, for every
    meaning whose letter `row` is that sentence.

What is not claimed. That a block's yes gives `RowKept`. AT ONE WITNESS: the witness behind and in
front is the same. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.First.Close.Law.FillRowRides

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes (Statement TreeBook)
open OnBytes.Means (InOrder Extends)
open OnBytes.Maker Fo.Peel Cb Johnson.Pack
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First (S Numbers RowClass Item Meaning classRows rowSays wordsAtFirst
  BookKept rowSaysFirst_back)

/-- **What a step leaves, as far as the item "row" reads the record.** -/
structure RowKept (s s' : S) : Prop where
  codes : s'.st.codes = s.st.codes
  msgs : ∀ j : Nat, j < s.st.oracles.size →
    (s'.st.oracles[j]?).map (fun x : OnBytes.Oracle => (x.shape, x.sampled, x.sampleRows)) =
      (s.st.oracles[j]?).map fun x : OnBytes.Oracle => (x.shape, x.sampled, x.sampleRows)
  rows : ∀ (j : Nat) (G : OnBytes.Group), s.st.groups[j]? = some G →
    ∃ G' : OnBytes.Group, s'.st.groups[j]? = some G' ∧ G'.rows = G.rows
  place : ∀ o : Nat, o < s.st.oracles.size → s'.book.place[o]? = s.book.place[o]?
  trees : ∀ (o : Nat) (q : Nat × Nat), s.book.place[o]? = some q →
    s'.book.trees[q.1]? = s.book.trees[q.1]?

/-- A message in front stands behind with its shape and its sample rows. -/
theorem RowKept.msg {s s' : S} (h : RowKept s s') (o : Nat) (x : OnBytes.Oracle)
    (hx : s.st.oracles[o]? = some x) :
    ∃ x' : OnBytes.Oracle, s'.st.oracles[o]? = some x' ∧ x'.shape = x.shape ∧
      x'.sampleRows = x.sampleRows := by
  have ho : o < s.st.oracles.size := by
    by_contra hn
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt hn)] at hx
    cases hx
  have e := h.msgs o ho
  rw [hx] at e
  obtain ⟨x', hx', e⟩ := Option.map_eq_some_iff.1 e
  obtain ⟨e1, e23⟩ := Prod.mk.inj e
  exact ⟨x', hx', e1, (Prod.mk.inj e23).2⟩

theorem RowKept.extends {s s' : S} (h : RowKept s s') : Extends s.st s'.st :=
  ⟨h.codes, fun o x hx => by
    obtain ⟨x', hx', e, _⟩ := h.msg o x hx
    exact ⟨x', hx', e⟩⟩

theorem RowKept.bookKept {s s' : S} (h : RowKept s s') : BookKept s s' :=
  fun o ho => ⟨h.place o ho, fun q hq => h.trees o q hq⟩

/-- **The rows of a class in front are among its rows behind.** -/
theorem classRows_sub (N : Numbers) (m : Nat) (c : RowClass) {s s' : S} (h : RowKept s s') :
    ∀ r ∈ classRows N m c s, r ∈ classRows N m c s' := by
  intro r hr
  have list : ∀ a n : Nat, (r ∈ match s.st.groups[N.groupAt m]? with
      | none => []
      | some G => (List.range n).filterMap fun j => G.rows[a + j]?) →
      r ∈ match s'.st.groups[N.groupAt m]? with
      | none => []
      | some G => (List.range n).filterMap fun j => G.rows[a + j]? := by
    intro a n h0
    cases hG : s.st.groups[N.groupAt m]? with
    | none => rw [hG] at h0; cases h0
    | some G =>
      obtain ⟨G', hG', e⟩ := h.rows _ G hG
      rw [hG] at h0
      rw [hG']
      show r ∈ (List.range n).filterMap fun j => G'.rows[a + j]?
      rw [e]
      exact h0
  cases c with
  | carried => exact list _ _ hr
  | position => exact list _ _ hr
  | equation => exact list _ _ hr
  | sample t =>
    obtain ⟨o, ho, hr⟩ := List.mem_flatMap.1 hr
    have ho' := List.mem_range.1 ho
    split at hr
    · rename_i hpl
      cases hor : s.st.oracles[o]? with
      | none => rw [hor] at hr; cases hr
      | some X =>
        rw [hor] at hr
        obtain ⟨X', hX', _, e⟩ := h.msg o X hor
        refine List.mem_flatMap.2 ⟨o, List.mem_range.2
          (Nat.lt_of_lt_of_le ho' h.extends.size), ?_⟩
        rw [h.place o ho', if_pos hpl, hX']
        show r ∈ X'.sampleRows.toList
        rw [e]
        exact hr
    · cases hr

variable {P Cells Tok : Type}

/-- **The item "row" goes back over such a step**, at one witness. -/
theorem row_back (arr : ℕ → ℕ → ℕ) (N : Numbers) (m : Nat) (c : RowClass) (a b : P × S)
    (y y' : Strs) (w : Wit Cells Tok MsgT) (hI : InOrder a.2.st) (hK : RowKept a.2 b.2)
    (h : rowSays N (wordsAtFirst arr) m c b y' w) : rowSays N (wordsAtFirst arr) m c a y w :=
  rowSaysFirst_back arr N m c a b y y' w hI hK.extends (classRows_sub N m c hK) hK.bookKept h

/-- The same at `Item.holds`, for every meaning whose letter `row` is that sentence. -/
theorem row_holds_back (arr : ℕ → ℕ → ℕ) (N : Numbers) (Mg : Meaning P (Wit Cells Tok MsgT))
    (hrow : Mg.row = rowSays N (wordsAtFirst arr)) (m : Nat) (c : RowClass) (a b : P × S)
    (y y' : Strs) (w : Wit Cells Tok MsgT) (hI : InOrder a.2.st) (hK : RowKept a.2 b.2)
    (h : (Item.row m c).holds N Mg b y' w) : (Item.row m c).holds N Mg a y w := by
  have h' : Mg.row m c b y' w := h
  show Mg.row m c a y w
  rw [hrow] at h' ⊢
  exact row_back arr N m c a b y y' w hI hK h'

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.classRows_sub
#print axioms VerifiableInference.Desc.K1.row_back
#print axioms VerifiableInference.Desc.K1.row_holds_back
