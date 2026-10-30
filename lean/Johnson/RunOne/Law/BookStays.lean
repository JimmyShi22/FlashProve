-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/BookStays.lean: FROM BEHIND
THE KEY FILE's TWO FIRST SENDINGS TO THE FRONT OF ITS FIRST PROXIMITY TEST THE BOOK OF TREES STAYS:
every block of a lookup's link, and the block that lays the lookups' rows, leaves the state's book
as it is; so a state of the first chain that was reached at a border 2 + j, up to the test's own,
has the book of a state that was reached at border 2 on the same history.

Main names:
  link_book: a yes of any of the six blocks of a lookup's link leaves the book.
  rows_book: so does a yes of the block that lays the lookups' rows.
  book_back: Hist₁ (Key.descriptionFromSource X N P) D (2 + j) a, j ≤ 6 · (the lookups) + 1 ⊢ there is a0 with
    Hist₁ … 2 a0, a0.1 = a.1 and a.2.d.book = a0.2.d.book.

By: the eight quiet routines of the plain ground leave the book (coreStill_same,
Johnson/Desc/CoreKeeps.lean). No premise on the plan.

Object: Key.lookupLink, Key.layRows at their places in Key.descriptionFromSource X N P. User:
Johnson/RunOne/Law/BookAt15.lean.
Limits. Nothing on soundness.

-/
import Johnson.RunOne.Law.StepSide4
import Johnson.RunOne.Law.RecOfHist
import Johnson.Desc.CoreKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.BookStays
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K3 VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Ground (coreStill_same)
open VerifiableInference.Desc.Key (FirstState Claim Source lookupSeat lookupLink lookupPlace caller
  layer layRows lookupsOf)
open Johnson.RunOne.Sound (FK fk_link_at fk_rows_at)
open Johnson.RunOne.Law.AtKeyD
open Johnson.RunOne.Law.JoinKeyD
open Johnson.RunOne.Law.LinkSeats
open Johnson.RunOne.Law.StepSide4 (claims_d)
open LPFD (Hist₁ Reached)

/-- **A yes of any of the six blocks of a lookup's link leaves the book.** -/
theorem link_book {one : OneTime} {set : Setting} {i : ℕ}
    {x : VerifiableInference.Desc.Key.Lookup} (j : ℕ) (hj : j < 6) (c : Block FirstState Claim)
    (hc : (lookupLink one set i x).blocksInOrder[j]? = some c) (s s' : FirstState) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) (hy : c.decide s rs gs = .ok s') :
    s'.d.book = s.d.book := by
  obtain ⟨c0, c4, c5, hF, d0, d4, d5⟩ := link_flat one set i x
  rw [hF] at hc
  have c6 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  rcases c6 with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain rfl := Option.some.inj hc
    have hy' : (lookupLink one set i x).lay s = .ok s' := (d0 s rs gs) ▸ hy
    obtain rfl := lay_same hy'
    rfl
  · obtain rfl := Option.some.inj hc
    obtain ⟨-, -, o, k, t1, t2, -, rfl⟩ := callerD_law hy
    exact (coreStill_same.takeMasks o.2 k.2 _ _ k.1 t2).1.trans
      (coreStill_same.takeMasks s.d o.2 _ _ o.1 t1).1
  · obtain rfl := Option.some.inj hc
    obtain ⟨F, g, G, es, -, -, -, -, -, rfl⟩ := block_law _ _ _ _ _ hy
    rfl
  · obtain rfl := Option.some.inj hc
    obtain ⟨cls, s1, F, g', rows, keys, e1, -, -, -, -, rfl⟩ := layerD_law hy
    show s1.d.book = s.d.book
    rw [claims_d e1]
  · obtain rfl := Option.some.inj hc
    have hy' := (d4 s rs gs) ▸ hy
    obtain rfl := after_same hy'
    rfl
  · obtain rfl := Option.some.inj hc
    have hy' : (lookupLink one set i x).clear s = .ok s' := (d5 s rs gs) ▸ hy
    obtain rfl := clear_eq hy'
    rfl

/-- **A yes of the block that lays the lookups' rows leaves the book.** -/
theorem rows_book {one : OneTime} {s s' : FirstState} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} (h : (layRows one).decide s rs gs = .ok s') :
    s'.d.book = s.d.book := by
  dsimp only [layRows, VerifiableInference.Desc.Key.quietAt] at h
  obtain ⟨_, -, h⟩ := bindX h
  obtain ⟨_, -, h⟩ := bindX h
  obtain ⟨d, hd, h⟩ := bindX h
  cases h
  exact (coreStill_same.addRows s.d d _ _ (namedX hd)).1

variable {X : Source} {N : H2U.PlaceNums} {P : VerifiableInference.Desc.Key.LaterPlaces}

/-- **THE BOOK AT A BORDER FROM 2 TO THE FIRST TEST's IS THE BOOK AT BORDER 2.** -/
theorem book_back (D : WholeD) :
    ∀ (j : ℕ), j ≤ 6 * (lookupsOf X.Y.k.oneTime).length + 1 →
      ∀ a, Hist₁ (VerifiableInference.Desc.Key.descriptionFromSource X N P) D (2 + j) a →
        ∃ a0, Hist₁ (VerifiableInference.Desc.Key.descriptionFromSource X N P) D 2 a0 ∧ a0.1 = a.1 ∧
          (show FirstState from a.2).d.book = (show FirstState from a0.2).d.book
  | 0, _, a, h => ⟨a, h, rfl, rfl⟩
  | j + 1, hj, a, h => by
    obtain ⟨a', b, rs, cols, hr, hb, hd, -⟩ := Reached.last (k := 2 + j) h
    rw [List.getElem?_map] at hb
    obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 hb
    obtain ⟨e1, hd'⟩ := VerifiableInference.Desc.Plain.held_decide b₀ a' _ _ a hd
    obtain ⟨a0, h0, e0, eb⟩ := book_back D j (by omega) a' hr
    refine ⟨a0, h0, e0.trans e1.symm, ?_⟩
    rw [← eb]
    rcases Nat.lt_or_ge j (6 * (lookupsOf X.Y.k.oneTime).length) with hlt | hge
    · obtain ⟨l, i, hi, rfl⟩ : ∃ l i, i < 6 ∧ j = 6 * l + i :=
        ⟨j / 6, j % 6, Nat.mod_lt _ (by omega), by omega⟩
      have hl : l < (lookupsOf X.Y.k.oneTime).length := by omega
      have hc := (fk_link_at X N P l i hi _ (List.getElem?_eq_getElem hl)).symm.trans hb₀
      exact link_book i hi b₀ hc _ _ _ _ hd'
    · obtain rfl : j = 6 * (lookupsOf X.Y.k.oneTime).length := by omega
      have hc := (fk_rows_at X N P).symm.trans hb₀
      obtain rfl := Option.some.inj hc
      exact rows_book hd'

end Johnson.RunOne.Law.BookStays

#print axioms Johnson.RunOne.Law.BookStays.link_book
#print axioms Johnson.RunOne.Law.BookStays.rows_book
#print axioms Johnson.RunOne.Law.BookStays.book_back
