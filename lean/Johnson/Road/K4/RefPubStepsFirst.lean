-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/RefPubStepsFirst.lean: THE FIRST GROUP's TWIN OF Johnson/Road/K4/RefPubSteps.lean:
`Plan4F.meetsF_public` (Johnson/Road/K4/PlanPublicFirst.lean), `refPF_meets` and `refPF_valueIs`
(Johnson/Road/K4/RefPubFirst.lean) WITH THE HASH-FREE RECORD `PublicSteps pol KL X`
(Johnson/Desc/Ok/PlanWritten/PublicAtSteps.lean) IN THE PLACE OF "`publicOf` returns X". Three
statements, each to the letter in its conclusion; turned from the three named by program.

  `Plan4F.meetsF_steps`, `refSF_meets`, `refSF_valueIs`.

Limits. Those of RefPubSteps.lean and RefPubFirst.lean: THE PUBLIC SIDE ALONE; `RefPub X g` and hla
(the shape's number la is 16) stay premises. `refPF_lines_pub` and `refPF_rope` (RefPubFirst.lean)
take no return of `publicOf`. No soundness is concluded.
-/
import Johnson.Road.K4.RefPubSteps
import Johnson.Road.K4.RefPubFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop OnBytes OnBytes.K.Kc OnBytes.Model OnBytes.Flat OnBytes.Maker
open OnBytes.Model.Layer (nEndT)
open OnBytes.Model.Verify (Public layerShape)
open Inst.Model (Scl)
open OnBytes.Desc.First.K4 (covers Par)
open VerifiableInference.PlanWritten (PublicSteps)

variable [scl : Scl] {M Xs : Type} {pol KL : ByteArray} {X : Public} {p : Par} {tk : Array Nat}

/-- **The premises of the first group's maps hold at a place that holds the public part's record and
plan**: four of the ten are shown; hc, Z, wk, hg, hls, hB are handed through. -/
theorem Plan4F.meetsF_steps (Q : Plan4F Cb.Gl.E M Xs) (St : PublicSteps pol KL X)
    (hP : p.P = { X.layers with tokv := tk }) (hG : X.G[p.g]? = some p.hp)
    (hc : covers X.layers = true) (Z : Sized (layerShape X.P) Q.D)
    (wk : Q.kW = X.layers.wsLay.lk) (hg : (p.g == 0) = true) (hls : Q.ls = X.layers.y.ls)
    (hB : Q.gB = X.layers.y.lPd - X.layers.y.ls) :
    Q.MeetsF p (layerShape X.P) X.P.polCalls where
  hy := by rw [hP]; exact steps_lay St
  hc := by rw [hP]; exact hc
  hrd := by rw [hP]; exact St.reads
  Z := Z
  hl := by rw [hP]; exact (planG_sizes (steps_G St p.g p.hp hG)).1
  hn := by rw [hP]; exact (planG_sizes (steps_G St p.g p.hp hG)).2
  wk := by rw [hP]; exact wk
  hg := hg
  hls := by rw [hP]; exact hls
  hB := by rw [hP]; exact hB

/-- **`MeetsF` holds of the first group's value**, under `RefPub`, where the group is the first and
la is 16. -/
theorem refSF_meets (R : RefLetters M Xs) (tok : Xs → ℕ → ℕ) (nT nI : ℕ)
    (St : PublicSteps pol KL X) (B : RefPub X p.g)
    (hP : p.P = { X.layers with tokv := tk }) (hG : X.G[p.g]? = some p.hp)
    (hg0 : (p.g == 0) = true) (hla : (layerShape X.P).la = 16) :
    (refLF R tok nT nI).planF.MeetsF p (layerShape X.P) X.P.polCalls := by
  obtain ⟨s0, H, _⟩ := B.lines p.hp hG
  obtain ⟨s1, s2⟩ := refF_sizes (H #[]).hy (H #[]).Z hla
  exact (refLF R tok nT nI).planF.meetsF_steps St hP hG B.covers (H #[]).Z
    (wsLayOf_units (H #[]).hlw).1.symm hg0 s1.symm s2.symm

/-- **`ValueIs` holds of the first group's value at the record's own two numbers of end values**,
under `RefPub`, where the group is the first, la is 16 and the section's table of scales is
`sclX X p.g`. -/
theorem refSF_valueIs (hscl : scl = sclX X p.g) (R : RefLetters M Xs) (tok : Xs → ℕ → ℕ)
    (St : PublicSteps pol KL X) (B : RefPub X p.g)
    (hP : p.P = { X.layers with tokv := tk }) (hG : X.G[p.g]? = some p.hp)
    (hg0 : (p.g == 0) = true) (hla : (layerShape X.P).la = 16) :
    Plan4L.ValueIs (refLF R tok (nEndT X.layers.y)
        (2 + (1 + X.layers.y.LamM) + (p.hp.NCL - (if (p.g == 0) = true then 1 else 0)))).toPlan4L
      p (layerShape X.P) := by
  have A := refSF_meets R tok (nEndT X.layers.y)
    (2 + (1 + X.layers.y.LamM) + (p.hp.NCL - (if (p.g == 0) = true then 1 else 0))) St B hP hG hg0
    hla
  have eg : p.g = 0 := beq_iff_eq.mp hg0
  have eT := A.nEndT_eq
  rw [hP] at eT
  refine ⟨by rw [hP]; rfl, by rw [hP]; rfl, fun _ => rfl, Nat.le_of_eq eT.symm,
    (refF_room R tok _ _).1, rfl, rfl, by rw [hscl, hP], ?_⟩
  rw [eg, Nat.zero_mul]
  rfl

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4F.meetsF_steps
#print axioms OnBytes.Road.K4.refSF_meets
#print axioms OnBytes.Road.K4.refSF_valueIs
