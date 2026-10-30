-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HidPack.lean: a family of 25 lists of small integers, packed into messages so
that ownAt gives it back, cut to the sizes.

ownAt s seat msg (Johnson/Goal/Meaning/HidSeat.lean) reads the 25 lists of a witness in its
messages. This file goes the other way: given lists seen k of integers, it makes messages msgOf s
seen, one for each label, and shows that at the seats seatBy seat0 (message: the label; main row:
the row of symbols; place: the column) ownAt is seen, cut to the sizes, if the sizes pack uniquely
(Size.Uniq), the entries within the sizes are below twice the shift in absolute value, and an entry
that bears another's label has its owner's radix, rows and entries.

Main names:
  cutOf s L, mzTot_cutOf   the list L as typed integers within the sizes s; its total form (mzTot)
    is L within the sizes, and 0 outside by mzTot's text.
  packTot rad m col i   the library's packing (Alg.pack) of the first m entries of a column on all
    numbers.
  seat0, msgOf s seen   the seats and the messages: the message with the number lab holds the packed
    columns of entry ownerA lab of the list of sub-proof ownerK lab
    (Johnson/Goal/Meaning/HidOwner.lean).
  OwnSame X s seen k   at every entry of sub-proof k: the owner that the label names has the same
    radix, the same rows and, within the entry's sizes, the same integers.
  ownAt_msgOf   THE STATEMENT ABOVE.

What is not claimed. That an honest prover's messages are msgOf: the release lays its arrays by the
layout file, in other messages, rows and places. It is a tool for showing that premises on ownAt can
be met. The program does not import this file.
-/
import Johnson.Goal.Meaning.HidOwner

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open OnBytes OnBytes.Road OnBytes.Road.L5 OnBytes.Road.Rows.Norms
open Cb.Pv.Tail (Size Syms BaseAt)

/-- A list on all numbers, as typed integers within the sizes. -/
def cutOf (s : Size) (L : Mats ℤ) : ∀ μ : Fin s.NM, Fin (s.k μ) → Fin (s.m μ) → ℤ :=
  fun μ c r => L μ.val r.val c.val

theorem mzTot_cutOf (s : Size) (L : Mats ℤ) {a r c : ℕ} (h : a < s.NM) (hc : c < s.k a)
    (hr : r < s.m a) : mzTot (cutOf s L) a r c = L a r c := by
  unfold mzTot
  rw [dif_pos h, dif_pos hc, dif_pos hr]
  rfl

/-- The library's packing of the first m entries of a column on all numbers. -/
def packTot (rad : ℤ) (m : ℕ) (col : ℕ → ℤ) (i : ℕ) : ℤ :=
  Alg.pack rad (fun r : Fin m => col r.val) i

/-- The seats: the message's number is the label, the main row the row of symbols, the place the
column. -/
def seat0 : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ := fun lab r c => (lab, r, c)

/-- The messages: the message with the number lab holds the packed columns of its owner's entry. -/
def msgOf (s : ℕ → Size) (seen : ℕ → Mats ℤ) : Msgs := fun lab _ i c =>
  ((packTot ((s (ownerK lab)).rad : ℤ) ((s (ownerK lab)).m (ownerA lab))
    (fun r => seen (ownerK lab) (ownerA lab) r c) i : ℤ) : Cb.Gl.E)

/-- At every entry of sub-proof k the owner that the label names has the same radix, the same rows
and, within the entry's sizes, the same integers. -/
structure OwnSame (X : Model.Verify.Public) (s : ℕ → Size) (seen : ℕ → Mats ℤ) (k : ℕ) : Prop where
  rad : ∀ a < (s k).NM, (s (ownerK (labAt X k a))).rad = (s k).rad
  m : ∀ a < (s k).NM, (s (ownerK (labAt X k a))).m (ownerA (labAt X k a)) = (s k).m a
  val : ∀ a < (s k).NM, ∀ r < (s k).m a, ∀ c < (s k).k a,
    seen (ownerK (labAt X k a)) (ownerA (labAt X k a)) r c = seen k a r c

/-- **ownAt at the messages msgOf is the family, cut to the sizes.** -/
theorem ownAt_msgOf {X : Model.Verify.Public} {s : ℕ → Size} {seen : ℕ → Mats ℤ} {k : ℕ} (p : ℕ)
    [CharP Cb.Gl.E p] (U : (s k).Uniq p)
    (sm : ∀ a < (s k).NM, ∀ r < (s k).m a, ∀ c < (s k).k a,
      |seen k a r c| < 2 * ((s k).beta : ℤ))
    (O : OwnSame X s seen k) :
    ownAt s (seatBy seat0 X s) (msgOf s seen) k = mzTot (cutOf (s k) (seen k)) := by
  unfold ownAt
  refine ownOf_unique p U (Cb.Pv.Tail.baseAt_of_packs p U
    (fun μ c i => sm μ.val μ.isLt i.val i.isLt c.val c.isLt) fun μ c i' => ?_)
  show ((packTot ((s (ownerK (labAt X k μ.val))).rad : ℤ)
      ((s (ownerK (labAt X k μ.val))).m (ownerA (labAt X k μ.val)))
      (fun r => seen (ownerK (labAt X k μ.val)) (ownerA (labAt X k μ.val)) r c.val) i'.val : ℤ) :
        Cb.Gl.E) = ((Alg.pack ((s k).rad : ℤ) (cutOf (s k) (seen k) μ c) i'.val : ℤ) : Cb.Gl.E)
  rw [O.rad μ.val μ.isLt, O.m μ.val μ.isLt]
  unfold packTot
  congr 2
  funext r
  exact O.val μ.val μ.isLt r.val r.isLt c.val c.isLt

end Meaning

#print axioms Meaning.mzTot_cutOf
#print axioms Meaning.ownAt_msgOf
