-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectTowers.lean: this file is on the object with both closings at the plan (`LdObjP`,
Cb/Obj/LdObjectPlan.lean), in the case that every whole test on a group is a concrete tower.

In standard terms: the record of all sub-protocols with, beside each of the five proximity tests on
groups that `P.Hyp` names, a concrete one of Cb/Obj/LdObjectTower.lean. The hypothesis that each of
these tests has its properties is replaced by hypotheses on the test's parts and two equations that
say that the test is the concrete one (`D.Pre T`).

Definitions, statements (`Cb.Spec.ldObjW_hyp`, `Cb.Spec.ldObjW3_hyp`) and proofs. In
Cb/Obj/LdObjectPlan.lean five tests on groups have the clause "the whole test on the group's complex
is a tail of a chain": the link's one, the two of the offline plan, the two of the online plan. A
test on a group: `LdRunD`, Cb/Ld/LdLinCloseRuns.lean.

Main names:
  `LdObjW F E`: data only, but for the proofs inside its fields' types (among them `same'` of
    `P : LdObjP`: head of Cb/Obj/LdObjectPlan.lean): `P : LdObjP`; five towers twK, tw₁, tw₂, tw₁B,
    tw₂B.
  `D.Pre T`: what is asked of one test D with the tower T. Two equations: D's whole test is
    `T.toEnd`, D's number of positions is `T.q` (whoever builds P with towers has them by
    definition; they are hypotheses here, not fields of the data); the bridge's evader, the list of
    the group's complex, Fits; the tower's own hypotheses (`T.Hyp`: the blocks' own records).
  `W.Hyp L`: `P.HypR L` (all of `P.Hyp` but the five tests); `D.Pre T` for each of the five.
  `Spec.ldObjW_hyp`: `W.Hyp L` ⇒ `W.P.Hyp L`.
Within a third of the distances (Cb/Obj/LdObjectTowerThird.lean):
  `W.Hyp L` (`W : LdObjW3 F E`): `P.HypR L`; `D.Pre3 T d` for each of the five.
  `Spec.ldObjW3_hyp`: `W.Hyp L` ⇒ `W.P.Hyp L`: of the five tests no clause on a list or on agreement
    is left. (`P.HypR` still has such clauses elsewhere: `Cf.OK`'s list, the bounds on the folds'
    bad points, the senders' lists.)

Notation: `L`: a natural number (`LdCf.OK L`, Cb/Obj/LdObjectConf.lean, says that it bounds the
lists at the radius of decoding).

Limits: what is still a parameter with a property: "the rest" of each plan; the request's moves; the
blocks of weights-formedness; senders (heads of Cb/Obj/LdObjectPlan.lean,
Cb/Obj/LdObjectTerms.lean).
That `W.Hyp L` can be met is shown nowhere (on `P.Hyp`: those heads). This file gives no instance
that meets its hypotheses, so as far as this file shows its theorems may hold of nothing.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectPlan
import Cb.Obj.LdObjectTowerThird

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- the concrete towers on the complex of a test's group -/
abbrev LdRunD.Tow {E : Type} [Field E] [Fintype E] {S : Sig E} (D : LdRunD S) : Type 1 :=
  LdTowG D.G D.Sb D.sl D.Z
abbrev LdRunD.Tow3 {E : Type} [Field E] [Fintype E] {S : Sig E} (D : LdRunD S) : Type 1 :=
  LdTowG3 D.G D.Sb D.sl D.Z

/-- The object, every whole test a concrete tower: the data. -/
structure LdObjW (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] where
  P    : LdObjP F E
  twK  : P.Kc.run.Tow
  tw₁  : P.TP.D₁.Tow
  tw₂  : P.TP.D₂.Tow
  tw₁B : P.TB.D₁.Tow
  tw₂B : P.TB.D₂.Tow

/-- what is asked of one test with the tower T: its whole test is the tower, its number of positions
the tower's; the bridge's evader, the list of the complex, Fits; the tower's own hypotheses -/
structure LdRunD.Pre {E : Type} [Field E] [Fintype E] {S : Sig E} (D : LdRunD S) (T : D.Tow) :
    Prop where
  isT  : D.T = T.toEnd
  isQ  : D.t = T.q
  ev   : D.Z.OK
  list : D.G.C.ListAt D.G.e D.L
  fits : D.G.Fits
  tow  : T.Hyp

structure LdObjW.Hyp {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    (W : LdObjW F E) (L : ℕ) : Prop where
  r    : W.P.HypR L
  pK   : W.P.Kc.run.Pre W.twK
  p₁   : W.P.TP.D₁.Pre W.tw₁
  p₂   : W.P.TP.D₂.Pre W.tw₂
  p₁B  : W.P.TB.D₁.Pre W.tw₁B
  p₂B  : W.P.TB.D₂.Pre W.tw₂B

/-- The same within a third of the distances: the data. -/
structure LdObjW3 (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] where
  P    : LdObjP F E
  twK  : P.Kc.run.Tow3
  tw₁  : P.TP.D₁.Tow3
  tw₂  : P.TP.D₂.Tow3
  tw₁B : P.TB.D₁.Tow3
  tw₂B : P.TB.D₂.Tow3
  dK   : ℕ
  d₁   : ℕ
  d₂   : ℕ
  d₁B  : ℕ
  d₂B  : ℕ

/-- what is asked of one test with the tower T, within unique decoding of the group's complex: its
whole test is the tower, its number of positions the tower's, its list bound is 1; laws and a
distance of the members' codes; evader, Fits; `T.Third` -/
structure LdRunD.Pre3 {E : Type} [Field E] [Fintype E] {S : Sig E}
    (D : LdRunD S) (T : D.Tow3) (d : ℕ) : Prop where
  isT  : D.T = T.toG.toEnd
  isQ  : D.t = T.toG.q
  isL  : D.L = 1
  laws : ∀ a : D.G.A, ((S.om a.1).C.atPos (D.G.pos a)).Laws
  dist : ∀ a : D.G.A, ((S.om a.1).C.atPos (D.G.pos a)).Dist d
  half : 2 * D.G.e < d
  ev   : D.Z.OK
  fits : D.G.Fits
  tow  : T.Third

structure LdObjW3.Hyp {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    (W : LdObjW3 F E) (L : ℕ) : Prop where
  r    : W.P.HypR L
  pK   : W.P.Kc.run.Pre3 W.twK W.dK
  p₁   : W.P.TP.D₁.Pre3 W.tw₁ W.d₁
  p₂   : W.P.TP.D₂.Pre3 W.tw₂ W.d₂
  p₁B  : W.P.TB.D₁.Pre3 W.tw₁B W.d₁B
  p₂B  : W.P.TB.D₂.Pre3 W.tw₂B W.d₂B

def Spec.ldObjW_hyp (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] : Prop :=
  ∀ (W : LdObjW F E) (L : ℕ), W.Hyp L → W.P.Hyp L

def Spec.ldObjW3_hyp (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Prop :=
  ∀ (W : LdObjW3 F E) (L : ℕ), W.Hyp L → W.P.Hyp L

theorem LdRunD.Pre.ok {E : Type} [Field E] [Fintype E] {S : Sig E} {D : LdRunD S}
    {T : D.Tow} (h : D.Pre T) : D.OK :=
  ldTowG_run E S D T h.isT h.isQ h.ev h.list h.fits h.tow

theorem LdRunD.Pre3.ok {E : Type} [Field E] [Fintype E] {S : Sig E} {D : LdRunD S} {T : D.Tow3}
    {d : ℕ} (h : D.Pre3 T d) : D.OK :=
  ldTowG3_run E S D T d h.isT h.isQ h.isL h.laws h.dist h.half h.ev h.fits h.tow

theorem ldObjW_hyp (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Spec.ldObjW_hyp F E := fun _ _ h =>
  ⟨h.r, h.pK.ok, h.p₁.ok, h.p₂.ok, h.p₁B.ok, h.p₂B.ok⟩

theorem ldObjW3_hyp (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Spec.ldObjW3_hyp F E := fun _ _ h =>
  ⟨h.r, h.pK.ok, h.p₁.ok, h.p₂.ok, h.p₁B.ok, h.p₂B.ok⟩

end Cb
