-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/HalveWLaw.lean: each definition of HalveW.lean equals its original
at `Fld.two`, as functions, for all arguments and without hypothesis. Imports Mathlib (through
FldWLaw.lean and HalveLaw.lean).

  `dotLW_eq`, `dotW_eq`, `fold1AW_eq`, `fold1LW_eq`, `fold1W_eq`, `foldLowW_eq`, `tailProdW_eq`,
  `hidePolyW_eq`, `coeffsW_eq`, `lightTermW_eq`, `lightAtW_eq`, `halvedFromW_eq`
                    one for each copy: for example `dotLW = dotL .two`
  `halvedW_eq`      `halvedW = halved .two`
  `halvedW_honest`  so `halvedW T g` is the list of `FoldOwn.honest` at `Fld.two`

By what. The three recursions (`dotLW`, `fold1AW`, `halvedFromW`) by induction along their own
patterns. The others are unfolded on both sides. The five equations of FldWLaw.lean rewrite the
operations, and `mulEF_eq` (Fmt/FieldEFast.lean) turns `Fld.mulEF` into `Fld.mulE`. The last by
`halved_eq` (HalveLaw.lean).

Limits. Nothing on cost.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.HalveW
import Johnson.Desc.ProofFile.Honest.K12.FldWLaw
import Johnson.Desc.ProofFile.Honest.K12.HalveLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open Fmt (Fld)
open Fmt.M1 (E dotL dot fold1A fold1L fold1 foldLow tailProd)
open Fmt.M1.FoldOwn (Trial Hide hidePoly cube coeffs honest)

/-- `Fld.mulEF` at `Fld.two` is `mulEW`, as functions. -/
theorem mulEF_words : Fld.two.mulEF = mulEW := by
  funext a b
  rw [mulEW_eq]
  exact Fmt.mulEF_eq .two a b

/-- `dotLW` at all arguments. -/
theorem dotLW_at : ∀ (u v : List E) (acc : E), dotLW u v acc = dotL .two u v acc
  | a :: u, b :: v, acc => by
    have e1 : dotLW (a :: u) (b :: v) acc = dotLW u v (addEW acc (mulEW a b)) := by
      conv => lhs; unfold dotLW
    have e2 : dotL .two (a :: u) (b :: v) acc =
        dotL .two u v (Fld.two.addE acc (Fld.two.mulEF a b)) := by
      conv => lhs; unfold dotL
    rw [e1, e2, dotLW_at u v, mulEF_words, addEW_eq]
  | [], v, _ => by cases v <;> rfl
  | _ :: _, [], _ => rfl

theorem dotLW_eq : dotLW = dotL .two := by
  funext u v acc
  exact dotLW_at u v acc

theorem dotW_eq : dotW = dot .two := by
  funext u v
  unfold dotW dot
  rw [dotLW_eq]

/-- `fold1AW` at all arguments. -/
theorem fold1AW_at (g : E) : ∀ (T acc : List E), fold1AW g T acc = fold1A .two g T acc
  | a :: b :: T, acc => by
    rw [fold1AW, fold1A, fold1AW_at g T, mulEF_words, addEW_eq, subEW_eq]
  | [a], acc => by rw [fold1AW, fold1A, mulEF_words, addEW_eq, subEW_eq]
  | [], acc => by rw [fold1AW, fold1A]

theorem fold1AW_eq : fold1AW = fold1A .two := by
  funext g T acc
  exact fold1AW_at g T acc

theorem fold1LW_eq : fold1LW = fold1L .two := by
  funext g T
  unfold fold1LW fold1L
  rw [fold1AW_eq]

theorem fold1W_eq : fold1W = fold1 .two := by
  funext g T
  unfold fold1W fold1
  rw [fold1LW_eq]

theorem foldLowW_eq : foldLowW = foldLow .two := by
  funext g T
  unfold foldLowW foldLow
  rw [fold1LW_eq]

theorem tailProdW_eq : tailProdW = tailProd .two := by
  funext g l
  unfold tailProdW tailProd
  rw [mulEW_eq]

theorem hidePolyW_eq : hidePolyW = hidePoly .two := by
  funext k U xs
  unfold hidePolyW hidePoly
  rw [tailProdW_eq, addEW_eq, mulEW_eq]

theorem coeffsW_eq : coeffsW = coeffs .two := by
  funext v0 v1 vm
  unfold coeffsW coeffs
  rw [addEW_eq, subEW_eq, mulEW_eq]

theorem lightTermW_eq : lightTermW = lightTerm .two := by
  funext T xs
  unfold lightTermW lightTerm
  rw [hidePolyW_eq, dotW_eq, foldLowW_eq, tailProdW_eq, addEW_eq, mulEW_eq]

theorem lightAtW_eq : lightAtW = lightAt .two := by
  funext T before X
  unfold lightAtW lightAt
  rw [lightTermW_eq, addEW_eq]

/-- `halvedFromW` at all arguments. -/
theorem halvedFromW_at (T : Trial) : ∀ (gs before : List E) (c m : Array E),
    halvedFromW T before c m gs = halvedFrom .two T before c m gs
  | [], _, _, _ => by rw [halvedFromW, halvedFrom]
  | g :: gs, before, c, m => by
    rw [halvedFromW, halvedFrom, halvedFromW_at T gs, lightAtW_eq, dotW_eq, fold1W_eq, coeffsW_eq,
      addEW_eq, mulEW_eq, negEW_eq]

theorem halvedFromW_eq : halvedFromW = halvedFrom .two := by
  funext T before c m gs
  exact halvedFromW_at T gs before c m

/-- **The rounds on 64-bit words alone are the rounds of `halved` at `Fld.two`.** -/
theorem halvedW_eq : halvedW = halved .two := by
  funext T g
  unfold halvedW halved
  rw [halvedFromW_eq]

/-- So they are the list of `FoldOwn.honest` at `Fld.two`. -/
theorem halvedW_honest (T : Trial) (g : List E) : halvedW T g = honest .two T [] g := by
  rw [halvedW_eq]
  exact halved_eq T g

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.mulEF_words
#print axioms ProofFile.Honest.K12.Light.dotLW_at
#print axioms ProofFile.Honest.K12.Light.dotLW_eq
#print axioms ProofFile.Honest.K12.Light.dotW_eq
#print axioms ProofFile.Honest.K12.Light.fold1AW_at
#print axioms ProofFile.Honest.K12.Light.fold1AW_eq
#print axioms ProofFile.Honest.K12.Light.fold1LW_eq
#print axioms ProofFile.Honest.K12.Light.fold1W_eq
#print axioms ProofFile.Honest.K12.Light.foldLowW_eq
#print axioms ProofFile.Honest.K12.Light.tailProdW_eq
#print axioms ProofFile.Honest.K12.Light.hidePolyW_eq
#print axioms ProofFile.Honest.K12.Light.coeffsW_eq
#print axioms ProofFile.Honest.K12.Light.lightTermW_eq
#print axioms ProofFile.Honest.K12.Light.lightAtW_eq
#print axioms ProofFile.Honest.K12.Light.halvedFromW_at
#print axioms ProofFile.Honest.K12.Light.halvedFromW_eq
#print axioms ProofFile.Honest.K12.Light.halvedW_eq
#print axioms ProofFile.Honest.K12.Light.halvedW_honest
