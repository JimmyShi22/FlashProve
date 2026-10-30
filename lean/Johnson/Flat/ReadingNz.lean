-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ReadingNz.lean: an element that a round's entry counts as drawn "never 0" is read as an
element other than 0, in every view that is made of a written transcript. No test asks this, and
none need: the format's sampler makes it so.

Already in the library: a draw "never 0" (`Fmt.Draw.elemNZ`) has as its typed value an element
together with a proof that it is not zero, and `elemsV_nz` (OnBytes/Slice/Draws.lean) says that the
list of the typed values' elements is not 0 at such a place.
New here:
  `elems_collect`: the elements that a round's record bears (`Fmt.Drawn.elems`), read into the field
  by `toE`, are that list.
  `isNZ_dsOf`: in a round that is not one of seeds, the last drawNZ of the elements are the draws
  "never 0".
  `drawnOf_nz`: so these elements of `drawnOf .two e k v` are read as other than 0, at all typed
  values v.
  `drawn_nz`: the same at the typed values of any verifier message c of a written round d.

Limits. A round of seeds is not covered (there each seed's factor is the draw "never 0":
`Fmt.dsSeeds`). That a round of a view has `drawnOf .two d.entry d.kind (valsOf (toRD d) c)` as what
it shows as drawn is `Maps.rvT_cons` (Johnson/Flat/ReadingLaw.lean), not stated here. Of an
arbitrary value of the type `View` nothing is said, and the like is false there: a law on all views
has to take it as a clause of "the view is well formed". At an entry with drawNZ above drawE the
subtraction is cut at 0.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Flat.RoundsT
import OnBytes.Slice.Draws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Flat
open Iop Run OnBytes.Maker OnBytes.Slice

/-- The elements that a round's record bears, read into the field, are the typed values' elements.
-/
theorem elems_collect : ∀ (ds : List Fmt.Draw) (v : Vals .two ds),
    (Fmt.collect (outAll .two ds v)).elems.map toE = elemsV ds v
  | [], _ => rfl
  | .elem :: ds, v => by
      show toE (toU3 v.1) :: (Fmt.collect (outAll .two ds v.2)).elems.map toE =
        evE v.1 :: elemsV ds v.2
      rw [elems_collect ds v.2]
      rfl
  | .elemNZ :: ds, v => by
      show toE (toU3 v.1.1) :: (Fmt.collect (outAll .two ds v.2)).elems.map toE =
        evE v.1.1 :: elemsV ds v.2
      rw [elems_collect ds v.2]
      rfl
  | .pos _ :: ds, v => elems_collect ds v.2
  | .trits _ :: ds, v => elems_collect ds v.2
  | .sealed :: ds, v => elems_collect ds v.2

theorem isNZ_pos (p : ℕ) (l : List Fmt.Draw) (i : ℕ) :
    ∀ n, IsNZ (List.replicate n (Fmt.Draw.pos p) ++ l) i = IsNZ l i
  | 0 => rfl
  | n + 1 => isNZ_pos p l i n

theorem isNZ_elem (l : List Fmt.Draw) (i : ℕ) :
    ∀ a, IsNZ (List.replicate a Fmt.Draw.elem ++ l) (a + i) = IsNZ l i
  | 0 => by rw [Nat.zero_add]; rfl
  | a + 1 => by
      have h : a + 1 + i = (a + i) + 1 := by omega
      rw [h]
      exact isNZ_elem l i a

theorem isNZ_nz (l : List Fmt.Draw) :
    ∀ b i, i < b → IsNZ (List.replicate b Fmt.Draw.elemNZ ++ l) i
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _ => trivial
  | b + 1, i + 1, h => isNZ_nz l b i (Nat.lt_of_succ_lt_succ h)

/-- In a round that is not one of seeds the last drawNZ elements are the draws "never 0". -/
theorem isNZ_dsOf (e : Fmt.Entry) (k : Fmt.Kind) (hk : k ≠ .seeds) (j : ℕ) (hj : j < e.drawNZ) :
    IsNZ (Fmt.dsOf e k) (e.drawE - e.drawNZ + j) := by
  unfold Fmt.dsOf Fmt.dsElems
  rw [if_neg hk, isNZ_pos, List.append_assoc, isNZ_elem]
  exact isNZ_nz _ _ _ hj

/-- These elements read as other than 0, at all typed values. -/
theorem drawnOf_nz (e : Fmt.Entry) (k : Fmt.Kind) (hk : k ≠ .seeds) (v : Vals .two (Fmt.dsOf e k))
    (j : ℕ) (hj : j < e.drawNZ) :
    ((drawnOf .two e k v).elems.map toE).getD (e.drawE - e.drawNZ + j) 0 ≠ 0 := by
  show ((Fmt.collect (outAll .two (Fmt.dsOf e k) v)).elems.map toE).getD _ 0 ≠ 0
  rw [elems_collect]
  exact elemsV_nz _ _ (isNZ_dsOf e k hk j hj) v

/-- **And so at what a view shows of a written round**, at any verifier's message. -/
theorem drawn_nz (d : RDT) (c : (wT d).Chal) (hk : d.kind ≠ .seeds) (j : ℕ)
    (hj : j < d.entry.drawNZ) :
    ((drawnOf .two d.entry d.kind (valsOf (toRD d) c)).elems.map toE).getD
      (d.entry.drawE - d.entry.drawNZ + j) 0 ≠ 0 :=
  drawnOf_nz d.entry d.kind hk _ j hj

end OnBytes.Flat

#print axioms OnBytes.Flat.elems_collect
#print axioms OnBytes.Flat.isNZ_dsOf
#print axioms OnBytes.Flat.drawn_nz
