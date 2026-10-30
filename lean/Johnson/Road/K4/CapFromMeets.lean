-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/CapFromMeets.lean: THE FOUR BOUNDS `CapSizes` (Johnson/Road/K4/CapK4.lean) FOLLOW
FROM `Plan4.Meets` (Johnson/Road/K4/PlanMaps.lean): the function `layout` refuses a shape with more
than 16 bits of positions or more than 6 bits of layers (its test "shape-words",
OnBytes/Model/LayerLayout.lean; `layout_caps`, OnBytes/Model/Fit/LayoutCaps.lean). So the
written counts of the rounds that K4's block declares lie below the cap at 128 under `Meets` alone,
in a group that is not the first. Three statements.

  `nW_closed`: the value's number of weight claims is 6 nl + 4 ne (`sum_cntB`,
    Johnson/Road/K4/PlanSizes.lean).
  `capSizes_of_meets`: `CapSizes Q.D Q.nW`: lT ≤ 16, lL ≤ 6, nNu ≤ 128, nW ≤ 512.
  `Plan4.herr_cap`: `Plan4.le_cap_at` without the premise `CapSizes`.

Limits. Those of CapK4.lean but for `CapSizes`: `Meets` is a premise; the declared rounds, not a
made plan's; a share of the written challenges of each round taken alone; nothing is added up; no
soundness is concluded.
-/
import Johnson.Road.K4.CapK4
import OnBytes.Model.Fit.LayoutCaps

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop _root_.Run OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat OnBytes.Slice
open Inst.Model (Scl)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.P1 (TailNums)

variable [scl : Scl] {M X : Type} {Q : Plan4 Cb.Gl.E M X} {p : Par} {hS : Layer.Shape}
  {pc : List (List String)}

/-- The value's number of weight claims. -/
theorem nW_closed (A : Q.Meets p hS pc) : Q.nW = 6 * Q.D.nl + 4 * Q.D.ne := by
  have e1 : Q.nW = (Verify.layerNumbers p.P p.hp p.g).weightClaims :=
    OnBytes.Tie.Pv.Lay.At.nW_eq Q.full _ A.dimIs
  rw [e1, ← A.dimIs.claims, sum_cntB]

/-- **The four bounds, from `Meets`.** -/
theorem capSizes_of_meets (A : Q.Meets p hS pc) : CapSizes Q.D Q.nW := by
  have Wd := Model.Fit.layout_caps A.hy
  have L := laySizes_of_layout A.hy
  have two60 : (2 : ℕ) ^ 60 = 1152921504606846976 := by norm_num
  have hp : 2 ^ hS.ll ≤ 64 := by
    calc 2 ^ hS.ll ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) Wd.ll
      _ = 64 := by norm_num
  have e1 := nl_tie A.Z
  have e2 := ne_tie A.Z
  have e3 := nNu_tie A.Z
  have e4 := nW_closed A
  have e5 : Q.D.lT = hS.lt := A.Z.lT
  have e6 : Q.D.lL = hS.ll := by
    have := A.dimIs.ll
    rw [← L.shape]
    exact this
  have w1 := Wd.lt
  have w2 := Wd.ll
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- **The written counts of K4's own rounds are at most the cap at 128, under `Meets` alone**, at
any list that is K4's declared one. -/
theorem Plan4.herr_cap (A : Q.Meets p hS pc) (N : TailNums Q.full.own.toOwn.tail)
    (Ex : Iop.ExtSpec) {ds : List RDT} (e : ds = dsLater p) :
    Err.le (((Plan4.mapsK4 A N Ex).castD e).err (Q.full.own.toOwn.ch.eps Ex))
      (Err.cap 128 (uLT (ckP .two) ds)) :=
  Plan4.le_cap_at A N Ex (capSizes_of_meets A) e

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.capSizes_of_meets
#print axioms OnBytes.Road.K4.Plan4.herr_cap
