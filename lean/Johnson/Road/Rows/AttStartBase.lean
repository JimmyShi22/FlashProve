-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttStartBase.lean: the four parts of what an attention link means, with the lift
as Cb/Pv/Tail/Base.lean states it, give that the attention link is in order at the lift's integers,
numbered anew through a map of places.

The lift BaseAt y Mz says of the committed symbols y and integers Mz: the integers are small, the
symbols are their packing, and the cells read off the symbols are their images in the field. The
other three parts speak of the cells t of the attention segment: the identities at1 and at2 (what
the sub-proof's own rounds are there to prove), the keys' clause (the lookup's own claim), and the
identities at3 (tested at the lookup's point).

Main definitions and theorems.
 - zsOf pl Mz: the integers Mz as matrices numbered (number in the list, row, column), through a map
   pl from such triples to the cells JCell (Cb/Pv/Tail/Agree.lean): (matrix, column, row).
 - PlaceOK pl: pl sends a triple within the sizes to the cell with the same matrix, the same column
   and the same row. zsOf_at: then zsOf pl Mz is Mz with row and column swapped. The two theorems
   below hold for every pl: only for a pl with PlaceOK are the matrices zsOf pl Mz the integers
   behind the committed symbols.
 - att_rel_base: the four parts give the relation of the segment (RFraw in
   Inst/Model/Att/Trace.lean) over the field K, of the cells of zsOf pl Mz.
 - att_ord_base: and, if the base field maps into K, AttOrd S (zsOf pl Mz)
   (Johnson/Road/Lane5AttDef.lean).

What is taken as given: that the cell t c is read off the symbols at the place pl (addrA S c), at
every name c (ht); that twice the shift beta is at most 2^18. What is not claimed: that the four
parts hold of a run; that they are the relation of a joint of a reduction. Nothing is said about
probabilities or about hiding. The program does not import this file.


-/
import Johnson.Road.Rows.AttEndsAll
import Cb.Pv.Tail.Base

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open OnBytes.Attention (Shape)
open Inst.Model.AttSeg (Raw Idn RFraw idnVal keyVec lut lutSet castT)
open Cb.Pv.Tail (Size Syms JCell BaseAt cellValS)

variable {K : Type} [Field K] {s : Size}

/-- The integers Mz as matrices numbered (number in the list, row, column). -/
def zsOf (pl : ℕ → ℕ → ℕ → JCell s) (Mz : ∀ μ : Fin s.NM, Fin (s.k μ) → Fin (s.m μ) → ℤ) : L5.Zs :=
  fun a r c => Mz (pl a r c).1 (pl a r c).2.1 (pl a r c).2.2

/-- The map pl sends a triple within the sizes to the cell with the same matrix, column and row. -/
def PlaceOK (pl : ℕ → ℕ → ℕ → JCell s) : Prop :=
  ∀ (μ : Fin s.NM) (c : Fin (s.k μ)) (r : Fin (s.m μ)), pl μ.val r.val c.val = ⟨μ, c, r⟩

/-- Under PlaceOK the matrices are the integers Mz, with row and column swapped. -/
theorem zsOf_at {pl : ℕ → ℕ → ℕ → JCell s} (hp : PlaceOK pl)
    (Mz : ∀ μ : Fin s.NM, Fin (s.k μ) → Fin (s.m μ) → ℤ) (μ : Fin s.NM) (c : Fin (s.k μ))
    (r : Fin (s.m μ)) : zsOf pl Mz μ.val r.val c.val = Mz μ c r := by
  unfold zsOf
  rw [hp μ c r]

/-- The four parts give the relation of the segment over K. -/
theorem att_rel_base {S : Shape} {y : Syms K s}
    {Mz : ∀ μ : Fin s.NM, Fin (s.k μ) → Fin (s.m μ) → ℤ} (hB : BaseAt y Mz)
    (pl : ℕ → ℕ → ℕ → JCell s) (h2 : 2 * (s.beta : ℤ) ≤ 2 ^ 18) {t : Raw → K}
    (ht : ∀ c, t c = cellValS y (pl (L5.addrA S c).1 (L5.addrA S c).2.1 (L5.addrA S c).2.2))
    (own1 : ∀ k b g i, (Idn.at1 k b g i).Valid (L5.dimOf S) →
      idnVal (L5.dimOf S) t (.at1 k b g i) = 0)
    (own2 : ∀ b g i, (Idn.at2 b g i).Valid (L5.dimOf S) → idnVal (L5.dimOf S) t (.at2 b g i) = 0)
    (keys : ∀ (c : Fin 4) (X : ℕ), X < (L5.dimOf S).used c →
      keyVec (scl := L5.sclOf S) (L5.dimOf S) (L5.tbOf S) t c X ∈
        lutSet (lut (scl := L5.sclOf S) (L5.dimOf S) (L5.tbOf S) c))
    (ridden : ∀ b g i, (Idn.at3 b g i).Valid (L5.dimOf S) →
      idnVal (L5.dimOf S) t (.at3 b g i) = 0) :
    RFraw (scl := L5.sclOf S) (L5.dimOf S) (L5.tbOf S) K (L5.cellsA S (zsOf pl Mz)) := by
  have e : t = (castT (L5.cellsA S (zsOf pl Mz)) : Raw → K) := funext fun c =>
    (ht c).trans (hB.2.2 _)
  refine ⟨fun c _ => lt_of_lt_of_le (hB.1 _ _ _) h2, fun c X hX => ?_, fun j hj => ?_⟩
  · rw [← e]
    exact keys c X hX
  · rw [← e]
    cases j with
    | at1 k b g i => exact own1 k b g i hj
    | at2 b g i => exact own2 b g i hj
    | at3 b g i => exact ridden b g i hj

/-- The four parts give that the attention link is in order at the integers behind the symbols. -/
theorem att_ord_base {S : Shape} {y : Syms K s}
    {Mz : ∀ μ : Fin s.NM, Fin (s.k μ) → Fin (s.m μ) → ℤ} (φ : Cb.Gl.F →+* K) (hB : BaseAt y Mz)
    (pl : ℕ → ℕ → ℕ → JCell s) (h2 : 2 * (s.beta : ℤ) ≤ 2 ^ 18) {t : Raw → K}
    (ht : ∀ c, t c = cellValS y (pl (L5.addrA S c).1 (L5.addrA S c).2.1 (L5.addrA S c).2.2))
    (own1 : ∀ k b g i, (Idn.at1 k b g i).Valid (L5.dimOf S) →
      idnVal (L5.dimOf S) t (.at1 k b g i) = 0)
    (own2 : ∀ b g i, (Idn.at2 b g i).Valid (L5.dimOf S) → idnVal (L5.dimOf S) t (.at2 b g i) = 0)
    (keys : ∀ (c : Fin 4) (X : ℕ), X < (L5.dimOf S).used c →
      keyVec (scl := L5.sclOf S) (L5.dimOf S) (L5.tbOf S) t c X ∈
        lutSet (lut (scl := L5.sclOf S) (L5.dimOf S) (L5.tbOf S) c))
    (ridden : ∀ b g i, (Idn.at3 b g i).Valid (L5.dimOf S) →
      idnVal (L5.dimOf S) t (.at3 b g i) = 0) :
    L5.AttOrd S (zsOf pl Mz) :=
  ⟨rfraw_down (scl := L5.sclOf S) (L5.dimOf S) (L5.tbOf S) φ φ.injective
    (att_rel_base hB pl h2 ht own1 own2 keys ridden)⟩

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.att_rel_base
#print axioms OnBytes.Road.Rows.att_ord_base
