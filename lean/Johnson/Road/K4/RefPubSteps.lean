-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/RefPubSteps.lean: THE PUBLIC PREMISES OF THE THEOREMS ON K4's BLOCK AT THE REFERENCE
VALUE, FROM THE HASH-FREE RECORD `PublicSteps pol KL X`
(Johnson/Desc/Ok/PlanWritten/PublicAtSteps.lean) IN THE PLACE OF "`publicOf` returns X". WHY:
`publicOf` tests three digests with the second hash function as a concrete function; a description
that takes the hash as a letter o hands the record of `publicOfO o`. `PublicSteps` holds every step
of the public part that takes no hash, and both returns pay it (`publicSteps_of`,
`publicSteps_of_O`). What the statements below spend of the return are four such steps: the layout's
return, the reads', the plans', and that the record's lists of matrices are the layout's.

  `steps_lay`, `steps_G`, `steps_G_lt`: the layers' layout returns the record's; the members of X.G
    come from `planG`; a group that has a plan is below the number of groups.
  `steps_ok`: `pub_ok` (Johnson/Road/K4/RefPub.lean).
  `Plan4.meets_steps`: `Plan4.meets_public` (Johnson/Road/K4/PlanPublic.lean).
  `refS_meets`, `refS_valueIs`: `refP_meets`, `refP_valueIs` (RefPub.lean).
  `steps_planeMatB`, `planes_steps`: `Fo.PlaneMatG.public_planeMatB`
    (OnBytes/Tie/Pv/Lookup/Ends/FoPlaneMatPubG.lean) and `planes_pub`
    (Johnson/Road/K4/MemberPlanes.lean).
  Each to the letter in its conclusion, with (St : PublicSteps pol KL X) for h.

Limits. THE PUBLIC SIDE ALONE. `RefPub X g` stays a premise of `refS_meets` and `refS_valueIs`: its
door with no test (`refPub_in_scope`, Johnson/Road/K4/RefInScope.lean) still takes `publicOf`'s
return. The proofs are those of the statements named, with the record's fields in the place of the
lemmas that open `publicOf`'s text. No soundness is concluded.
-/
import Johnson.Road.K4.RefPub
import Johnson.Road.K4.MemberPlanes
import Johnson.Desc.Ok.PlanWritten.PublicAtSteps

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop OnBytes OnBytes.K.Kc OnBytes.Model OnBytes.Flat OnBytes.Maker
open OnBytes.Model.Layer (HPlan2 nEndT layout matIx)
open OnBytes.Model.Verify (Public layerShape)
open Inst.Model (Scl)
open OnBytes.Desc.First.K4 (covers Par)
open VerifiableInference.PlanWritten (PublicSteps)

variable {pol KL : ByteArray} {X : Public}

/-- The layers' layout returns the record's. -/
theorem steps_lay (St : PublicSteps pol KL X) :
    layout (layerShape X.P) X.P.polCalls = .ok X.layers.y :=
  Hd.layerLayout_of_polLayout St.layout

/-- The members of X.G come from `planG`. -/
theorem steps_G (St : PublicSteps pol KL X) (g : ℕ) (hp : HPlan2) (hG : X.G[g]? = some hp) :
    Layer.planG X.layers g (if g = 0 then none else X.G[g - 1]?) = .ok hp :=
  _root_.Fo.Pub.plansG_at X.layers X.G St.plans g hp hG

/-- A group that has a plan is below the number of groups. -/
theorem steps_G_lt (St : PublicSteps pol KL X) {g : ℕ} {hp : HPlan2} (hG : X.G[g]? = some hp) :
    g < X.layers.y.NGr := by
  have e := St.plans
  unfold Layer.plansG at e
  obtain ⟨l, h1, e⟩ := _root_.Fo.BatRows.bindE_ok e
  have hl := _root_.Fo.PlaneMatG.plansFrom_len X.layers _ _ _ l h1
  have hs : X.G.size = X.layers.y.NGr := by
    rw [← Except.ok.inj e]
    simpa using hl
  rw [← hs]
  exact (Array.getElem?_eq_some_iff.mp hG).1

/-- The layout's shape of the lookup passes the lookup's test on numbers. -/
theorem steps_ok (St : PublicSteps pol KL X) : FoNums.ok X.layers.y.fo = true :=
  _root_.Fo.Pay.shapeOf_ok (_root_.Fo.layout_shape (steps_lay St))

variable [scl : Scl] {M Xs : Type} {p : Par} {tk : Array Nat}

/-- **The premises of the maps hold at a place that holds the record's layers and plan**: four of
the eight are shown; hc, Z, wk, hg are handed through. -/
theorem Plan4.meets_steps (Q : Plan4 Cb.Gl.E M Xs) (St : PublicSteps pol KL X)
    (hP : p.P = { X.layers with tokv := tk }) (hG : X.G[p.g]? = some p.hp)
    (hc : covers X.layers = true) (Z : Sized (layerShape X.P) Q.D)
    (wk : Q.kW = X.layers.wsLay.lk) (hg : (p.g == 0) = false) :
    Q.Meets p (layerShape X.P) X.P.polCalls where
  hy := by rw [hP]; exact steps_lay St
  hc := by rw [hP]; exact hc
  hrd := by rw [hP]; exact St.reads
  Z := Z
  hl := by rw [hP]; exact (planG_sizes (steps_G St p.g p.hp hG)).1
  hn := by rw [hP]; exact (planG_sizes (steps_G St p.g p.hp hG)).2
  wk := by rw [hP]; exact wk
  hg := hg

/-- **`Meets` holds of the value**, under `RefPub`, in a group that is not the first. -/
theorem refS_meets (R : RefLetters M Xs) (hg : p.g < 12) (St : PublicSteps pol KL X)
    (B : RefPub X p.g) (hP : p.P = { X.layers with tokv := tk }) (hG : X.G[p.g]? = some p.hp)
    (hg0 : (p.g == 0) = false) (nT nI : ℕ) :
    (refL R p.g hg nT nI).plan.Meets p (layerShape X.P) X.P.polCalls := by
  obtain ⟨s0, H, _⟩ := B.lines p.hp hG
  exact (refL R p.g hg nT nI).plan.meets_steps St hP hG B.covers (H #[]).Z
    (wsLayOf_units (H #[]).hlw).1.symm hg0

/-- **`ValueIs` holds of the value at the record's own two numbers of end values**, under `RefPub`,
in a group that is not the first, where the section's table of scales is `sclX X p.g`. -/
theorem refS_valueIs (hscl : scl = sclX X p.g) (R : RefLetters M Xs) (hg : p.g < 12)
    (St : PublicSteps pol KL X) (B : RefPub X p.g)
    (hP : p.P = { X.layers with tokv := tk }) (hG : X.G[p.g]? = some p.hp)
    (hg0 : (p.g == 0) = false) :
    Plan4L.ValueIs (refL R p.g hg (nEndT X.layers.y)
        (2 + (1 + X.layers.y.LamM) + (p.hp.NCL - (if (p.g == 0) = true then 1 else 0))))
      p (layerShape X.P) := by
  have A := refS_meets R hg St B hP hG hg0 (nEndT X.layers.y)
    (2 + (1 + X.layers.y.LamM) + (p.hp.NCL - (if (p.g == 0) = true then 1 else 0)))
  have S7 := sevenSizes_of_meets A tk
  have L := laySizes_of_layout A.hy
  have eLam : p.P.y.Lam = 4 := by
    rw [L.Lam, ← A.Z.lL]
    rfl
  have e := S7.hEnd
  rw [hP] at e
  exact ⟨by rw [hP]; rfl, by rw [hP]; rfl, fun _ => rfl, e, (ref_room R p.g hg _ _).1, rfl, rfl,
    by rw [hscl, hP], by rw [eLam]; rfl⟩

omit scl in
/-- **The test on the planes' matrix says yes at every group's plan.** -/
theorem steps_planeMatB (St : PublicSteps pol KL X) (g : ℕ) (hp : HPlan2)
    (hG : X.G[g]? = some hp) : _root_.Fo.planeMatB X.layers.y hp.tl.mats = true := by
  obtain ⟨r, hb, hm⟩ := _root_.Fo.PlaneMatG.planG_mats X.layers g _ hp (steps_G St g hp hG)
  obtain ⟨k1, k2⟩ := _root_.Fo.PlaneMatG.sameMK_getD (_root_.Fo.PlaneMatG.bordersOf_keeps hb)
    (matIx X.layers.y).iB
  rw [St.tails] at k1 k2
  obtain ⟨b1, b2⟩ := _root_.Fo.PlaneMatG.tailsOf_b X.layers.y g (steps_G_lt St hG)
  simp only [_root_.Fo.planeMatB, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨_root_.Fo.test_of_made (_root_.Fo.made_layout (steps_lay St)), ?_⟩, ?_⟩
  · rw [hm, k1, b1]
    exact Nat.div_self (Nat.pos_of_ne_zero (by positivity))
  · rw [hm, k2, b2, _root_.Fo.PlaneMatG.layout_kbm (steps_lay St)]

omit scl in
/-- **The planes' matrix: its rows over 2 ^ lmb, rounded down, are 1, and it has columns enough**,
where the place holds the record's layers and the group's plan. -/
theorem planes_steps (St : PublicSteps pol KL X) (hP : p.P = { X.layers with tokv := tk })
    (hG : X.G[p.g]? = some p.hp) :
    (p.hp.tl.mats.getD (matIx p.P.y).iB {}).m / 2 ^ p.P.y.h.lmb = 1 ∧
      _root_.Fo.planeCols p.P.y.fo p.P.y.h.lmb ≤ (p.hp.tl.mats.getD (matIx p.P.y).iB {}).k := by
  have b := steps_planeMatB St p.g p.hp hG
  simp only [_root_.Fo.planeMatB, Bool.and_eq_true, decide_eq_true_eq] at b
  rw [hP]
  exact ⟨b.1.2, b.2⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.steps_lay
#print axioms OnBytes.Road.K4.steps_G
#print axioms OnBytes.Road.K4.steps_G_lt
#print axioms OnBytes.Road.K4.steps_ok
#print axioms OnBytes.Road.K4.Plan4.meets_steps
#print axioms OnBytes.Road.K4.refS_meets
#print axioms OnBytes.Road.K4.refS_valueIs
#print axioms OnBytes.Road.K4.steps_planeMatB
#print axioms OnBytes.Road.K4.planes_steps
