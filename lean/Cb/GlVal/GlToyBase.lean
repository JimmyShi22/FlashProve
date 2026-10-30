-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/GlVal/GlToyBase.lean: a Reed-Solomon code of length 8 and dimension 3 over the field with
p = 2^64 - 2^32 + 1 elements, read over its cubic extension, as a small test instance: its distance
is at least 6, and at the radius 1 it decodes uniquely and has mutual correlated agreement, all
proved; with small lemmas on numbers in the two fields.

The smallest code of Cb/Gl/GlCodes.lean, in length and then in dimension, that hides two positions
and is read within a third of its distance, at a radius of at least 1 and with a message symbol (by
a reckoning; no theorem of this file says that it is the smallest). Definitions, statements and
proofs. A guard against empty theorems; no parameter of a protocol.

Why: the toys of Cb/Ld/LdRelToy.lean, Cb/Ld/LdRelToy7.lean are over the field with 101 elements,
with one field in the place of both, and Reed-Solomon codes on the points 1, .., 5 and 1, .., 7. The
statements of Cb/Gl/GlOff.lean speak of F = the integers modulo p, E = F[x] / (x^3 - 2)
(Cb/Gl/GlField.lean), and codes on subgroups. This file has what a toy over F and E takes in the
place of Cb/Ld/LdRelToy.lean, Cb/Ld/LdRelToy7.lean.

Main names:
  `C8`: `rs 3 2 1 2 1 2` (`rs a k msg r e mca`, Cb/Gl/GlCodes.lean: length 2^a, dimension k + 1):
    the subgroup of order 8; dimension 3: one message symbol, two symbols of randomness (they fill
    the dimension); distance 6; in its data the radius 1 and the count 2 for mutual correlated
    agreement.
  `Spec.gl_toy8`: for every finite R with decidable equality: `GlC (toyLd8 R) 6 2`
    (Cb/Gl/GlLd.lean), so: laws, distance at least 6, transparent, reads what it declares, zero
    knowledge at 2 positions; 3 · 1 < 6; lists of at most one member and at most 2 exceptional
    values at the radius 1.
  `small`: every number below 2^32 is below p (for the lookups' conditions on numbers).

Which field is used where in a toy over these fields: F for entries of index messages and the pads
beside them (`Ood.PadInF F`, Cb/Gen/OodDecPad.lean), the model (body, heldB), `Code.Enc`; E for
codes as they are read (`LdCode`, `OMsg`, `Sig`, `StdFam`, `StdL`), keys, tables, bits, masks,
samples, evaders, `LkAsm2`, `BattPar`, challenges.
Why the numerals (`natF_ne`, `natE_ne`, `n57F` and their like): a proof "by decide" on elements of
the field would enumerate it. Nothing may enumerate the field.
Why `up_inj`, `up_ofNat`, `up_eq_ofNat`: because F ≠ E, an entry of an index message reaches a key
through `algebraMap` (`Cf.upM`); they turn "the key is 5 or 7 in E" into "the entry is 5 or 7 in F".

Limits: this file says nothing on real parameters.
Terms: lean/GLOSSARY.md.
-/
import Cb.Gl.GlLd
import Cb.Ld.LdBaseCode

set_option autoImplicit false

namespace Cb.Gl
open Code Prob Blocks Iop Hiop

/-- The code of the toy. -/
def C8 : Code.Enc F := rs 3 2 1 2 1 2

/-- Its positions. -/
abbrev P8 : Type := (Reading.one C8).P

/-- Rows R under `C8`, read as they stand. -/
@[reducible] def toyLd8 (R : Type) [Fintype R] [DecidableEq R] : LdCode E P8 :=
  (Reading.one C8).ld E fun _ => R

namespace Spec

def gl_toy8 : Prop :=
  ∀ (R : Type) [Fintype R] [DecidableEq R], GlC (toyLd8 R) 6 2 ∧ (toyLd8 R).Laws ∧
    (toyLd8 R).Dist 6 ∧ (toyLd8 R).Transparent ∧ (toyLd8 R).Reads ∧ (toyLd8 R).Zk 2 ∧ 3 * 1 < 6 ∧
    (toyLd8 R).ListAt 1 1 ∧ (toyLd8 R).MCAat 1 2

end Spec

theorem core8 : C8.Core := gl_rs_core 3 2 1 2 1 2 (by norm_num) (by norm_num) (by norm_num)
theorem d8 : C8.d = 6 := rfl
theorem dist8 : HasDist C8.G C8.d := rs_hasDist 1 2 1 2 (by norm_num) (by norm_num)
theorem card8 : Fintype.card P8 = 8 := Fintype.card_fin 8
instance neP8 : Nonempty P8 := ⟨(⟨0, by norm_num⟩ : Fin (2 ^ 3))⟩

/-- Every code at the eight positions with the laws and the distance 6: at most one codeword within
one position (`list8`); at most two exceptional values (`mca8`). -/
theorem list8 (D : LdCode E P8) (hL : D.Laws) (hD : D.Dist 6) : D.ListAt 1 1 :=
  ld_list_unique E P8 D 6 1 hL hD (by norm_num)
theorem mca8 (D : LdCode E P8) (hL : D.Laws) (hD : D.Dist 6) : D.MCAat 1 2 :=
  ld_mca_third E P8 D 6 1 hL hD (by norm_num)

theorem glC8 (R : Type) [Fintype R] [DecidableEq R] : GlC (toyLd8 R) 6 2 :=
  .base (gl_code_one 3 2 1 2 R (by norm_num) (by norm_num) (by norm_num))

theorem gl_toy8 : Spec.gl_toy8 := fun R _ _ =>
  have h := glC_code P8 (toyLd8 R) 6 2 (glC8 R)
  ⟨glC8 R, h.1, h.2.2.2.1, h.2.1, h.2.2.1, h.2.2.2.2, by norm_num,
    list8 _ h.1 h.2.2.2.1, mca8 _ h.1 h.2.2.2.1⟩

/-! ### Numerals -/

theorem small {n : ℕ} (h : n < 2 ^ 32) : n < p := lt_trans h (by decide +kernel)

/-- Two different numbers below p are different in a ring of characteristic p. -/
theorem nat_ne (R : Type) [AddGroupWithOne R] [CharP R p] {m n : ℕ} (hm : m < p)
    (hn : n < p) (h : m ≠ n) : (m : R) ≠ (n : R) := by
  intro e
  have := (CharP.natCast_eq_natCast R p).1 e
  exact h (Nat.ModEq.eq_of_lt_of_lt this hm hn)

theorem natF_ne {m n : ℕ} (hm : m < 2 ^ 32) (hn : n < 2 ^ 32) (h : m ≠ n) : (m : F) ≠ (n : F) :=
  nat_ne F (small hm) (small hn) h
theorem natE_ne {m n : ℕ} (hm : m < 2 ^ 32) (hn : n < 2 ^ 32) (h : m ≠ n) : (m : E) ≠ (n : E) :=
  nat_ne E (small hm) (small hn) h

theorem n57F : (5 : F) ≠ 7 := by
  simpa using natF_ne (m := 5) (n := 7) (by norm_num) (by norm_num) (by norm_num)
theorem n65F : (6 : F) ≠ 5 := by
  simpa using natF_ne (m := 6) (n := 5) (by norm_num) (by norm_num) (by norm_num)
theorem n67F : (6 : F) ≠ 7 := by
  simpa using natF_ne (m := 6) (n := 7) (by norm_num) (by norm_num) (by norm_num)
theorem n57E : (5 : E) ≠ 7 := by
  simpa using natE_ne (m := 5) (n := 7) (by norm_num) (by norm_num) (by norm_num)
theorem n65E : (6 : E) ≠ 5 := by
  simpa using natE_ne (m := 6) (n := 5) (by norm_num) (by norm_num) (by norm_num)
theorem n67E : (6 : E) ≠ 7 := by
  simpa using natE_ne (m := 6) (n := 7) (by norm_num) (by norm_num) (by norm_num)
theorem n01E : (0 : E) ≠ 1 := zero_ne_one

/-- The embedding of F in E. -/
theorem up_inj : Function.Injective (algebraMap F E) := Cubic.algebraMap_injective
theorem up_nat (n : ℕ) : algebraMap F E (n : F) = (n : E) := map_natCast _ n
theorem up_ofNat (n : ℕ) [n.AtLeastTwo] : algebraMap F E (OfNat.ofNat n) = OfNat.ofNat n :=
  map_ofNat _ n
theorem up_eq_ofNat (n : ℕ) [n.AtLeastTwo] (x : F) :
    algebraMap F E x = OfNat.ofNat n ↔ x = OfNat.ofNat n := by
  rw [← up_ofNat n]
  exact up_inj.eq_iff

end Cb.Gl
