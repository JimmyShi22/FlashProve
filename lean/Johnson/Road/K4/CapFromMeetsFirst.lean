-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/CapFromMeetsFirst.lean: THE SIX BOUNDS `CapSizesF` (Johnson/Road/K4/CapK4First.lean)
FOLLOW FROM `Plan4F.MeetsF` (Johnson/Road/K4/PlanMapsFirst.lean), by the layout's own tests (the
theorem `layout_caps`, OnBytes/Model/Fit/LayoutCaps.lean). So the written counts of K4's own rounds
in the first group lie below the cap at 128 under `MeetsF` alone. Two statements.

  `capSizesF_of_meetsF`: lT ≤ 16, lL ≤ 6, nNu ≤ 128, nW ≤ 512, ls + lT ≤ 36, gB ≤ 20.
  `Plan4F.herr_capF`: `Plan4F.le_cap_atF` without the premise `CapSizesF`.

Limits. Those of CapK4.lean: `MeetsF` is a premise; a share of the written challenges of each round
taken alone; nothing is added up; no soundness is concluded.
-/
import Johnson.Road.K4.CapK4First
import Johnson.Road.K4.CapFromMeets
import Johnson.Road.K4.PlanClauses

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop _root_.Run OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat OnBytes.Slice
open Inst.Model (Scl)
open Inst.Model.FFSeg (lDd)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.P1 (TailNums)

variable [scl : Scl] {M X : Type} {Q : Plan4F Cb.Gl.E M X} {p : Par} {hS : Layer.Shape}
  {pc : List (List String)}

/-- **The six bounds, from `MeetsF`.** -/
theorem capSizesF_of_meetsF (A : Q.MeetsF p hS pc) : CapSizesF Q := by
  have Wd := Model.Fit.layout_caps A.hy
  have L := laySizes_of_layout A.hy
  have two60 : (2 : ℕ) ^ 60 = 1152921504606846976 := by norm_num
  have hp : 2 ^ hS.ll ≤ 64 := by
    calc 2 ^ hS.ll ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) Wd.ll
      _ = 64 := by norm_num
  have e1 := nl_tie A.Z
  have e2 := ne_tie A.Z
  have e3 := nNu_tie A.Z
  have e4 : Q.nW = 6 * Q.D.nl + 4 * Q.D.ne := by
    have e : Q.nW = (Verify.layerNumbers p.P p.hp p.g).weightClaims :=
      OnBytes.Tie.Pv.Lay.At.nW_eq Q.toPlan4.full _ A.dimIs
    rw [e, ← A.dimIs.claims, sum_cntB]
  have e5 : Q.D.lT = hS.lt := A.Z.lT
  have e6 : Q.D.lL = hS.ll := by
    have := A.dimIs.ll
    rw [← L.shape]
    exact this
  have e7 : p.P.y.lPd ≤ 20 := by
    have a : lDd Q.D = p.P.y.lPd := A.dimIs.lPd
    have b : Q.D.d ≤ 2 ^ 20 := by
      show Q.D.P.d ≤ 2 ^ 20
      rw [A.Z.d]
      exact Wd.d
    rw [← a]
    calc lDd Q.D ≤ Nat.clog 2 (2 ^ 20) := Nat.clog_mono_right 2 b
      _ = 20 := Nat.clog_pow 2 20 (by norm_num)
  have e8 : p.P.y.ls ≤ p.P.y.lPd := (norms_sizes A.hy A.Z).2.2.2.1
  have e9 := A.hls
  have e10 := A.hB
  have w1 := Wd.lt
  have w2 := Wd.ll
  exact { nNu := by omega, nW := by omega, lT := by omega, lL := by omega, gA := by omega,
          gB := by omega }

/-- **The written counts of K4's own rounds in the first group are at most the cap at 128, under
`MeetsF` alone**, at any list that is K4's declared one. -/
theorem Plan4F.herr_capF (A : Q.MeetsF p hS pc) (N : TailNums Q.fullF.ownF.toOwn.tail)
    (Ex : Iop.ExtSpec) {ds : List RDT} (e : ds = dsFirst p) :
    Err.le (((Plan4F.mapsK4F A N Ex).castD e).err ((chFF Q.fullF).eps Ex))
      (Err.cap 128 (uLT (ckP .two) ds)) :=
  Plan4F.le_cap_atF A N Ex (capSizesF_of_meetsF A) e

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.capSizesF_of_meetsF
#print axioms OnBytes.Road.K4.Plan4F.herr_capF
