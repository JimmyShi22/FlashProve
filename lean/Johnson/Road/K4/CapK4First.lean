-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/CapK4First.lean: THE WRITTEN COUNTS OF K4's OWN ROUNDS LIE BELOW THE CAP AT 128, IN
THE FIRST GROUP, at the library's value (`Plan4F.fullF`) and the maps of
Johnson/Road/K4/PlanMapsFirst.lean. The twin of Johnson/Road/K4/CapK4.lean, whose head says how the
clause at one round is had and what is not said; its lemmas on the four kinds of rounds are used
here. A record and three statements.

What is other in the first group: two more points are drawn in front (ls + lT and gB coordinates;
the typed counts g q^(g - 1)); the typed count at the weights' round is nW, not nW - 1 (one claim
more, the embedding's).

  `CapSizesF`: `CapSizes`, and ls + lT ≤ 2^60, gB ≤ 2^60.
  `Plan4F.tailBelowF`, `Plan4F.le_capK4F`, `Plan4F.le_cap_atF`.

Limits. Those of CapK4.lean: `CapSizesF` and `MeetsF` are premises; a share of the written
challenges of each round taken alone; nothing is added up; no soundness is concluded.
-/
import Johnson.Road.K4.CapK4
import Johnson.Road.K4.PlanMapsFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop _root_.Run OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat OnBytes.Slice
open Inst.Model (Scl)
open OnBytes.Desc.First.K4 (Par Rd Fit rdOf fit_rdOf pointRd batchRd)
open OnBytes.Desc.First.P1 (RdBelow ScR TailM TailNums TailBelow ownFirst_le_cap)
open scoped ENNReal

variable [scl : Scl] {M X : Type}

/-- Six bounds on the library's sizes. -/
structure CapSizesF (Q : Plan4F Cb.Gl.E M X) : Prop extends CapSizes Q.D Q.nW where
  gA : Q.ls + Q.D.lT ≤ 2 ^ 60
  gB : Q.gB ≤ 2 ^ 60

variable {Q : Plan4F Cb.Gl.E M X} {p : Par} {hS : Layer.Shape} {pc : List (List String)}

/-- **The clause at every written round from the limbs' scalars on.** -/
theorem Plan4F.tailBelowF (A : Q.MeetsF p hS pc) (N : TailNums Q.fullF.ownF.toOwn.tail)
    (C : CapSizes Q.D Q.nW) :
    TailBelow ((2 : ℝ≥0∞)⁻¹ ^ 128) (TailM.ofIs A.tailIs A.written.2.2.2.2 N) := by
  have two65 : (2 : ℕ) ^ 65 = 36893488147419103232 := by norm_num
  have two60 : (2 : ℕ) ^ 60 = 1152921504606846976 := by norm_num
  have c1 := C.nNu
  have c2 := C.nW
  have c4 := C.lL
  have Xd := A.dimIs
  exact
    { l := rb_one (fit_rdOf _) rfl rfl rfl (9 - 1) (by norm_num)
      n := rb_pt (fit_rdOf _) rfl (g := Q.D.lL + 1) Xd.lNI.symm rfl (by omega)
      s1 := scR_below _ _ _ _ (Nat.le_refl 2)
      t1 := rb_one (fit_rdOf _) rfl rfl rfl 1 (by norm_num)
      p := rb_one (fit_rdOf _) rfl rfl rfl (Q.D.nNu * 7 - 1) (by omega)
      s2 := scR_below _ _ _ _ (Nat.le_refl 2)
      s3 := scR_below _ _ _ _ (show 1 ≤ 2 by norm_num)
      d4 := rb_one (fit_rdOf _) rfl rfl rfl (2 - 1) (by norm_num)
      s4 := scR_below _ _ _ _ (Nat.le_refl 2)
      s5 := scR_below _ _ _ _ (Nat.le_refl 2)
      t5 := rb_one (fit_rdOf _) rfl rfl rfl 1 (by norm_num)
      r := rb_pt (fit_rdOf _) rfl (g := Q.D.lL - 1) (congrArg (· - 1) Xd.ll.symm) rfl (by omega)
      s6 := scR_below _ _ _ _ (Nat.le_refl 2)
      t6 := rb_one (fit_rdOf _) rfl rfl rfl 1 (by norm_num)
      w := rb_one (fit_rdOf _) rfl rfl rfl Q.nW (by omega)
      s7 := scR_below _ _ _ _ (show 1 ≤ 2 by norm_num) }

/-- **The written counts of K4's own rounds in the first group are at most the cap at 128.** -/
theorem Plan4F.le_capK4F (A : Q.MeetsF p hS pc) (N : TailNums Q.fullF.ownF.toOwn.tail)
    (Ex : Iop.ExtSpec) (C : CapSizesF Q) :
    Err.le ((Plan4F.mapsK4F A N Ex).err ((chFF Q.fullF).eps Ex))
      (Err.cap 128 (uLT (ckP .two) (dsFirst p))) := by
  have two65 : (2 : ℕ) ^ 65 = 36893488147419103232 := by norm_num
  have two60 : (2 : ℕ) ^ 60 = 1152921504606846976 := by norm_num
  have c3 := C.lT
  have c5 := C.gA
  have c6 := C.gB
  exact ownFirst_le_cap 128 Ex Q.fullF.ownF.toOwn _
    (rb_pt (fit_rdOf _) rfl (g := Q.D.lT) A.dimIs.lt.symm rfl (by omega))
    (rb_pt (fit_rdOf _) rfl (g := Q.ls + Q.D.lT)
      (congrArg₂ (· + ·) A.hls A.dimIs.lt).symm rfl (by omega))
    (rb_pt (fit_rdOf _) rfl (g := Q.gB) A.hB.symm rfl (by omega))
    (Plan4F.tailBelowF A N C.toCapSizes)

/-- **At any list that is K4's declared one.** -/
theorem Plan4F.le_cap_atF (A : Q.MeetsF p hS pc) (N : TailNums Q.fullF.ownF.toOwn.tail)
    (Ex : Iop.ExtSpec) (C : CapSizesF Q) {ds : List RDT} (e : ds = dsFirst p) :
    Err.le (((Plan4F.mapsK4F A N Ex).castD e).err ((chFF Q.fullF).eps Ex))
      (Err.cap 128 (uLT (ckP .two) ds)) := by
  subst e
  exact Plan4F.le_capK4F A N Ex C

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4F.le_capK4F
#print axioms OnBytes.Road.K4.Plan4F.le_cap_atF
