-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/CallerOf.lean: who calls a proximity test on a group of sent oracle messages, as a
function of the group's data and of the list of the test's later stages; and the conditions of the
typed list of its blocks.

The record is `TestCaller`, the list `testLK` and the conditions `TestOK`
(Johnson/Top/H/Key2.lean). The group's data are `Rows` (Johnson/Top/H/GroupRows.lean); the stages
and the last step are made by `Rows.towOf` (Johnson/Top/H/TestOf.lean). The rows that the round
before the test batches, which members are kept for later, and the joint that is carried are the
caller's letters. Definitions, statements and proofs.
Main names:
  `Rows.sizeB`: the record of the round before the test (`Cb.Pv.Bat.Size`) on the group, at the
    Johnson bound on its lists.
  `Rows.caller`: the value of `TestCaller` at given data of the stages.
  `Rows.caller_ok`: `TestOK`, clause by clause: the coefficients evade zero (asked); the lists
    (`Rows.list`); the joint radius implies each member's own (asked); the shape's laws
    (`Rows.sh_ok`); the conditions of the stages and what locality asks (asked).
  `Rows.callerOf`: the caller as a function of the list of later stages; nothing where sizes do
    not fit.
  `Rows.callerOf_some`, `Rows.callerOf_ok`: under the test on numbers it returns a caller; with
    `Rows.Good`, `CountsAt` at the first stage and `CntL` behind it, `TestOK` holds of what it
    returns.
  `Rows.callerOf_good`: so the one block of its typed list has the property that a typed list
    asks.
Limits: the limits of the files named hold here. `CountsAt` and `CntL` are not proved here. How
the joints at the list's two ends meet the joints of a description of a file's protocol is not
treated.

-/
import Johnson.Top.H.Key2
import Johnson.Top.H.TestOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes.Slice Cb Iop IOR Cb.Pv.Tower VerifiableInference.OnPublicFiles

namespace Rows
variable {S : Sig GE} (R : Rows S) (keep : S.O → Prop) [DecidablePred keep] {B : Type} [Fintype B]
  (Sb : B → Type) (sl : ∀ b, Slf GE (Sb b) R.G.C.J) (Z : Evader GE (R.G.Row B))

/-- The record of the round before the test. -/
@[reducible] noncomputable def sizeB : Cb.Pv.Bat.Size GE where
  S := S
  G := R.G
  keep := keep
  B := B
  Sb := Sb
  sl := sl
  Z := Z
  L := lstJ R.s R.e

variable {Kc St₀ Wp : Type} {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub (R.sizeB keep Sb sl Z).kp).Msg × Wp)) (w₀ : S.Wit × Wp)

/-- Who calls the test, at given data of the stages. -/
noncomputable def caller
    (T : TowR (wholeJ R.Sh.par (R.Sh.form Sb sl Z) R.G.e) R.Sh.par.Cw.nat) : TestCaller GE where
  s := R.sizeB keep Sb sl Z
  Sh := R.Sh
  T := T
  Kc := Kc
  St₀ := St₀
  Wp := Wp
  E₀ := E₀
  A₀ := A₀
  w₀ := w₀

theorem caller_ok (T : TowR (wholeJ R.Sh.par (R.Sh.form Sb sl Z) R.G.e) R.Sh.par.Cw.nat)
    (hZ : Z.OK) (hF : R.G.Fits) (hg : R.Good) (hj : InJ R.s R.e) (hT : T.HypK) (hR : T.Reads) :
    TestOK (R.caller keep Sb sl Z A₀ w₀ T) where
  z := hZ
  list := R.list hg hj
  fits := hF
  shape := R.sh_ok hg
  tower := hT
  reads := hR

variable (bC bZ : Sg → ℕ → ℕ) (c₁ z₁ : ℕ)

/-- The caller as a function of the list of later stages. -/
noncomputable def callerOf (l : List (Sg × ℕ)) : Option (TestCaller GE) :=
  (R.towOf bC bZ c₁ z₁ Sb sl Z l).map (R.caller keep Sb sl Z A₀ w₀)

theorem callerOf_some (l : List (Sg × ℕ)) (h : R.goodT l = true) :
    (R.callerOf keep Sb sl Z A₀ w₀ bC bZ c₁ z₁ l).isSome = true := by
  unfold callerOf
  rw [Option.isSome_map]
  exact R.towOf_some bC bZ c₁ z₁ Sb sl Z l h

theorem goodT_inJ : ∀ l, R.goodT l = true → InJ R.s R.e
  | [], h => absurd h Bool.false_ne_true
  | _ :: _, h => by
    simp only [goodT, Bool.and_eq_true] at h
    exact inJ_of h.1.2

theorem callerOf_ok (hZ : Z.OK) (hF : R.G.Fits) (hg : R.Good)
    (hc : CountsAt R.s R.e c₁ z₁) (l : List (Sg × ℕ)) (h : R.goodT l = true)
    (hl : ∀ x l', l = x :: l' → CntL bC bZ l' x.1 x.2) (c : TestCaller GE)
    (hcl : R.callerOf keep Sb sl Z A₀ w₀ bC bZ c₁ z₁ l = some c) : TestOK c := by
  obtain ⟨T, hT, rfl⟩ := Option.map_eq_some_iff.1 hcl
  exact R.caller_ok keep Sb sl Z A₀ w₀ T hZ hF hg (R.goodT_inJ l h)
    (R.towOf_hypK bC bZ c₁ z₁ Sb sl Z hg hc l h hl T hT)
    (R.towOf_reads bC bZ c₁ z₁ Sb sl Z l h T hT)

/-- The one block of the caller's typed list has the property that a typed list asks. -/
theorem callerOf_good (hZ : Z.OK) (hF : R.G.Fits) (hg : R.Good)
    (hc : CountsAt R.s R.e c₁ z₁) (l : List (Sg × ℕ)) (h : R.goodT l = true)
    (hl : ∀ x l', l = x :: l' → CntL bC bZ l' x.1 x.2) (c : TestCaller GE)
    (hcl : R.callerOf keep Sb sl Z A₀ w₀ bC bZ c₁ z₁ l = some c) :
    ((testLK c).blk c.w₀).Good :=
  testLK_good c (R.callerOf_ok keep Sb sl Z A₀ w₀ bC bZ c₁ z₁ hZ hF hg hc l h hl c hcl)

end Rows

end Johnson.Top.H

#print axioms Johnson.Top.H.Rows.caller_ok
#print axioms Johnson.Top.H.Rows.callerOf_ok
#print axioms Johnson.Top.H.Rows.callerOf_good
