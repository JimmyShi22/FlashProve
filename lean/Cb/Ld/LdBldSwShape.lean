-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBldSwShape.lean: book-keeping: bijections of the index types of one fold's codes with the
numbers below their counts, for the first fold on a group's complex (`Sh.par`, `Sh.fold`,
Cb/Ld/LdGroupFold.lean).

Definitions and two statements with their proofs (by definition). Generic: any field. Nothing
assumed; no choice in a definition.

Why: Cb/Ld/LdBldSwOrd.lean builds the parts of the code switch after any fold Y from two numberings
that meet `SwEqP`: N of Y and N' of the next fold. A numbering (`FoldNo Y`, that file) has numbers
m, r (main row: message, randomness), m', r' (mask row), c (coordinates of a long symbol of the
output code), and a bijection of each index type with the numbers below its count. This file gives
the numbering of the fold of a group's shape; in `LdTowG.shaped` (Cb/Obj/LdObjectTower.lean) the
first stage of a whole test on a group uses that fold. That fold's main code is a super-row: one
slot for the folded rows and one for each kept row.

Main names:
  `N.at sl`: the same numbering at the fold `Y.reform sl` (a fold with other forms has the same
    codes).
  `optNo kp`: the slots of a super-row: the slot of the folded rows has the number 0, the kept slot
    j the number 1 + j's.
  `shNo Sh kp cJ cQ zJ zQ aC aZ aW`: the numbering of the coordinates of `Sh.par`, from numberings
    of the base code's and the mask code's, of the kept slots and of `Sh.AaW`.
  `Spec.bldSwS_nums`: its numbers, for κ kept slots: m, r are κ + 1 times the base code's; m', r'
    are the mask code's; c = (κ + 1) cb + (cz + cw) (the counts of `Sh.Cb.Aa`, `Sh.Zb.Aa`, `Sh.AaW`,
    Cb/Ld/LdGroupFold.lean); and `Sh.par.h` = `Sh.h`, `Sh.par.g` = `Sh.g` (mask rows on the cube of
    h variables, main rows on the cube of h + g: `GShape`, Cb/Ld/LdGroupFold.lean).
  `Spec.bldSwS_at`: the indices: `rowsNoF eR no` gives (x, j) the number (x's) + ρ · (j's), ρ the
    number of rows, so the row's number runs fastest; `optNo`: as told above.

Limits: declared: the order of a super-row's slots is ours. This file does not say that a shape has
no kept slot. It does not say that `shNo` meets `SwEqP`.
It says nothing on
codes beyond their index types and the counts of these, on lists, radii.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdBldSwOrd
import Cb.Ld.LdGroupFold

set_option autoImplicit false

namespace Cb
open Prob Blocks Alg Cb.Ood

namespace Bld

/-- The same numbering at other forms. -/
def FoldNo.at {E P : Type} [Field E] {Y : SumPar E P} (N : FoldNo Y)
    {St : Type} (sl : Slf E St Y.Cin.J) : FoldNo (Y.reform sl) :=
  ⟨N.m, N.r, N.m', N.r', N.c, N.cJ, N.cQ, N.zJ, N.zQ, N.aa⟩

/-- finitely many coordinates of a long symbol -/
@[reducible] def FoldNo.finAa {E P : Type} [Field E] {Y : SumPar E P} (N : FoldNo Y) :
    Fintype Y.Cout.Aa :=
  Fintype.ofEquiv (Fin N.c) N.aa.symm

/-- rows named by a numbered type over a numbered type; rows first -/
def rowsNoF {R J : Type} {ρ n : ℕ} (eR : R ≃ Fin ρ) (no : J ≃ Fin n) : R × J ≃ Fin (ρ * n) :=
  (Equiv.prodComm R J).trans
    (((Equiv.prodCongr no eR).trans finProdFinEquiv).trans (finCongr (Nat.mul_comm n ρ)))

/-- the slots of a super-row -/
def optNo {Kp : Type} {κ : ℕ} (kp : Kp ≃ Fin κ) : Option Kp ≃ Fin (κ + 1) :=
  (Equiv.optionCongr kp).trans (finSuccEquiv κ).symm

/-- The numbering of the first fold on a group's complex. -/
def shNo {E : Type} [Field E] {S : Sig E} {G : Grp S} (Sh : GShape G)
    {κ m r m' r' cb cz cw : ℕ} (kp : Sh.Kp ≃ Fin κ) (cJ : Sh.Cb.J ≃ Fin m)
    (cQ : Sh.Cb.Q ≃ Fin r) (zJ : Sh.Zb.J ≃ Fin m') (zQ : Sh.Zb.Q ≃ Fin r')
    (aC : Sh.Cb.Aa ≃ Fin cb) (aZ : Sh.Zb.Aa ≃ Fin cz) (aW : Sh.AaW ≃ Fin cw) : FoldNo Sh.par where
  m := (κ + 1) * m
  r := (κ + 1) * r
  m' := m'
  r' := r'
  c := (κ + 1) * cb + (cz + cw)
  cJ := rowsNoF (optNo kp) cJ
  cQ := rowsNoF (optNo kp) cQ
  zJ := zJ
  zQ := zQ
  aa := sumNo (rowsNoF (optNo kp) aC) (sumNo aZ aW)

end Bld

namespace Spec
open Cb.Bld

def bldSwS_nums : Prop :=
  ∀ (E : Type) [Field E] (S : Sig E) (G : Grp S) (Sh : GShape G) (κ m r m' r' cb cz cw : ℕ)
      (kp : Sh.Kp ≃ Fin κ) (cJ : Sh.Cb.J ≃ Fin m) (cQ : Sh.Cb.Q ≃ Fin r)
      (zJ : Sh.Zb.J ≃ Fin m') (zQ : Sh.Zb.Q ≃ Fin r') (aC : Sh.Cb.Aa ≃ Fin cb)
      (aZ : Sh.Zb.Aa ≃ Fin cz) (aW : Sh.AaW ≃ Fin cw),
    (shNo Sh kp cJ cQ zJ zQ aC aZ aW).m = (κ + 1) * m ∧
    (shNo Sh kp cJ cQ zJ zQ aC aZ aW).r = (κ + 1) * r ∧
    (shNo Sh kp cJ cQ zJ zQ aC aZ aW).m' = m' ∧
    (shNo Sh kp cJ cQ zJ zQ aC aZ aW).r' = r' ∧
    (shNo Sh kp cJ cQ zJ zQ aC aZ aW).c = (κ + 1) * cb + (cz + cw) ∧
    Sh.par.h = Sh.h ∧ Sh.par.g = Sh.g

/-- where an entry of a super-row stands -/
def bldSwS_at : Prop :=
  (∀ (R J : Type) (ρ n : ℕ) (eR : R ≃ Fin ρ) (no : J ≃ Fin n) (x : R) (j : J),
    (rowsNoF eR no (x, j)).val = (eR x).val + ρ * (no j).val) ∧
  ∀ (Kp : Type) (κ : ℕ) (kp : Kp ≃ Fin κ),
    (optNo kp none).val = 0 ∧ ∀ j, (optNo kp (some j)).val = (kp j).val + 1

end Spec

theorem bldSwS_nums : Spec.bldSwS_nums := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem bldSwS_at : Spec.bldSwS_at := ⟨fun _ _ _ _ _ _ _ _ => rfl, fun _ _ _ => ⟨rfl, fun _ => rfl⟩⟩

end Cb
