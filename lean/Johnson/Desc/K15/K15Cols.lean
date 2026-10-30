-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K15/K15Cols.lean: beneath K15's law: the columns that the format's Block.step hands a
block, against the library's way of saying
which columns a run has read (viewColumns · columnRows: OnBytes/Iop/OpenLaws.lean ·
OnBytes/Slice/BlkLinkRun.lean). Lemmas on lists;
no program is run.
-/
import Johnson.Desc.K15.K15Rows
import OnBytes.Slice.BlkLinkRun
import OnBytes.Slice.ProgMle

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K15
open OnBytes OnBytes.Params OnBytes.Slice

abbrev Col3 : Type := Nat × Nat × List UInt64

/-- The columns' words, as the library's arrays. -/
def wordsOf (got : List Col3) : Array (Array F) := (got.map fun c => c.2.2.toArray).toArray

/-- Columns that are, in key and position, those of a list under one key ARE the library's
viewColumns of that list. -/
theorem view_of_fit (key W : Nat) : ∀ (xs : List Nat) (got : List Col3),
    got.map (fun c => (c.1, c.2.1, c.2.2.length)) = xs.map (fun x => (key, x, W)) →
    got = viewColumns key xs.toArray (wordsOf got)
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, c :: got, h => by
    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨h1, h2, _⟩, ht⟩ := h
    have ih := view_of_fit key W xs got ht
    obtain ⟨a, b, w⟩ := c
    simp only at h1 h2
    subst h1 h2
    unfold viewColumns wordsOf at ih ⊢
    simp only [List.map_cons, List.zip_cons_cons] at ih ⊢
    rw [← ih]

/-- A look-up by position among such columns is the library's: the place of the position in the
list, and the column there. -/
theorem lookup_fit (key W : Nat) (x : Nat) : ∀ (xs : List Nat) (got : List Col3),
    got.map (fun c => (c.1, c.2.1, c.2.2.length)) = xs.map (fun x => (key, x, W)) →
    ((got.map fun c => (c.2.1, c.2.2)).lookup x).map (·.toArray) =
      (xs.idxOf? x).bind fun i => (wordsOf got)[i]?
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | y :: xs, c :: got, h => by
    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨_, h2, _⟩, ht⟩ := h
    have ih := lookup_fit key W x xs got ht
    obtain ⟨a, b, w⟩ := c
    simp only at h2
    subst h2
    by_cases hx : x = b
    · subst hx
      simp [List.lookup, List.idxOf?, List.findIdx?_cons, wordsOf]
    · have hx' : (x == b) = false := by simpa using hx
      have hx'' : (b == x) = false := by simpa using fun e => hx e.symm
      simp only [List.map_cons, List.lookup, hx']
      rw [ih]
      simp [List.idxOf?, List.findIdx?_cons, hx'', wordsOf, Option.bind_map]

/-- Each such column has the width. -/
theorem size_of_fit (key W : Nat) : ∀ (xs : List Nat) (got : List Col3),
    got.map (fun c => (c.1, c.2.1, c.2.2.length)) = xs.map (fun x => (key, x, W)) →
    ∀ (i : Nat) (c : Array F), (wordsOf got)[i]? = some c → c.size = W
  | [], [], _, i, c, h => by simp [wordsOf] at h
  | [], _ :: _, h, _, _, _ => by simp at h
  | _ :: _, [], h, _, _, _ => by simp at h
  | y :: xs, g :: got, h, i, c, hc => by
    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨_, _, h3⟩, ht⟩ := h
    cases i with
    | zero =>
      simp [wordsOf] at hc
      rw [← hc]
      simpa using h3
    | succ j =>
      apply size_of_fit key W xs got ht j c
      simpa [wordsOf] using hc

/-- **One table's share of the rows of "LINK"**: K15's text (one (loc_x) a location drawn, its
column by look-up among the columns
that Block.step hands) is the library's columnRows' body, at the same list of locations. -/
theorem locRows_eq (S : FoldeqShape) (w : Array E) (u : FoldedRow) (key W : Nat) (xs : List Nat)
    (got : List Col3) (draws : List Nat)
    (hfit : got.map (fun c => (c.1, c.2.1, c.2.2.length)) = xs.map (fun x => (key, x, W)))
    (hW : w.size ≤ W) :
    (draws.mapM fun x => do
      Desc.K14.locX S x w ((← (got.map fun c => (c.2.1, c.2.2)).lookup x).toArray) u) =
    (draws.mapM fun x => do
      let i ← xs.toArray.idxOf? x
      foldeqColumnRow S x (foldeqSymbol w (← (wordsOf got)[i]?)) u) := by
  congr 1
  funext x
  have hl := lookup_fit key W x xs got hfit
  have hs := size_of_fit key W xs got hfit
  simp only [List.idxOf?_toArray]
  cases hi : xs.idxOf? x with
  | none =>
    rw [hi] at hl
    cases hk : (got.map fun c => (c.2.1, c.2.2)).lookup x with
    | none => rfl
    | some v => rw [hk] at hl; simp at hl
  | some i =>
    rw [hi] at hl
    cases hk : (got.map fun c => (c.2.1, c.2.2)).lookup x with
    | none =>
      rw [hk] at hl
      simp only [Option.map_none, Option.bind_some] at hl
      simp [← hl]
    | some v =>
      rw [hk] at hl
      simp only [Option.map_some, Option.bind_some] at hl
      have hv := hs i v.toArray hl.symm
      simp only [Option.bind_eq_bind, Option.bind_some, ← hl]
      exact locX_eq S x w v.toArray u (by rw [hv]; exact hW)

end Desc.K15

#print axioms Desc.K15.view_of_fit
#print axioms Desc.K15.lookup_fit
#print axioms Desc.K15.locRows_eq
