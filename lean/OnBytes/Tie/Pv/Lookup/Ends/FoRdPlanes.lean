-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoRdPlanes.lean.
Which claims a lookup's own routines add, as written lists: the three on the planes of its counts,
for every caller whose two readers of the planes leave the state; its rows; its join.

By the rules of OnBytes/Tie/Pv/Lookup/Ends/FoRd.lean.

Main names:
  `planesAtT`, `countT`, `planeFormsT g lm bit pin`: the three forms, bit and pin the values of
    the caller's two readers. They are the total twins of planesAtO, countO and planeFormsO
    (OnBytes/Tie/Pv/Led/LedWalkPlanes.lean), whose readers do not read
    the state.
  `rd_planesAt`, `adV_planeClaims`, `ad_planeLins`: `Forest.planeLins` adds just these three, if
    each of the caller's two readers leaves the state and returns that value (`Rd`).
  `ad_objects`: `Forest.objects` adds the lookup's rows. `adV_join`: `Forest.join` adds nothing and
    returns `joinForm` (OnBytes/Tie/Pv/Lookup/Forest/FoJoinRun.lean).

Limits: those of OnBytes/Tie/Pv/Lookup/Ends/FoRd.lean: the list is total; off a run that returns it
means nothing.

Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed what the forms are worth.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoRd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

/-- The value of the planes at the point zb e, as a form. -/
def planesAtT (g : Forest.Heard) (lm e : ℕ) (bit : ℕ → ℕ → Aff) : Aff :=
  (List.range (g.shape.NC * 2 ^ (g.shape.kT + 5 - lm))).foldl
    (fun (f : Aff) col => Aff.addMul f (bit e col)
      (mulE ((eqTab ((g.zb e).extract g.shape.kT (g.shape.kT + g.shape.cK))).getD
          (col / 2 ^ (g.shape.kT + 5 - lm)) zeroE)
        ((eqTab ((g.zb e).extract 0 (g.shape.kT + 5 - lm))).getD
          (col % 2 ^ (g.shape.kT + 5 - lm)) zeroE)))
    (Aff.ofConst zeroE)

/-- The sum of the counts, less the number of keys that are not padding, as a form. -/
def countT (g : Forest.Heard) (lm : ℕ) (pin : ℕ → Aff) : Aff :=
  (List.range (g.shape.NC * 2 ^ (g.shape.kT + 5 - lm))).foldl (fun (f : Aff) col => f + pin col)
    (Aff.ofConst (negE (ofF (2 ^ g.shape.v - g.shape.padding).toUInt64)))

/-- The three forms. -/
def planeFormsT (g : Forest.Heard) (lm : ℕ) (bit : ℕ → ℕ → Aff) (pin : ℕ → Aff) : Array Aff :=
  #[g.leaves.rowForm oneE (Aff.scale (planesAtT g lm 0 bit) g.leavesA),
    Aff.slot g.sBit - planesAtT g lm 1 bit, countT g lm pin]

section
variable {t K : ℕ} {bit : ℕ → ℕ → SubM Aff} {pin : ℕ → SubM Aff} {bitT : ℕ → ℕ → Aff}
  {pinT : ℕ → Aff}

theorem rd_planesAt (g : Forest.Heard) (lm e : ℕ) (hb : ∀ e x, Rd t K (bit e x) (bitT e x)) :
    Rd t K (Forest.planesAt g lm e bit) (planesAtT g lm e bitT) := by
  unfold Forest.planesAt planesAtT
  refine Rd.foldlM _ _ ?_ _ _
  intro f col
  exact Rd.bind (hb e col) (Rd.pure _)

theorem adV_planeClaims (g : Forest.Heard) (lm : ℕ) (hb : ∀ e x, Rd t K (bit e x) (bitT e x))
    (hp : ∀ x, Rd t K (pin x) (pinT x)) :
    AdV t K (Forest.planeClaims g lm bit pin) (planeFormsT g lm bitT pinT) [] := by
  unfold Forest.planeClaims planeFormsT
  refine AdV.bind (l₁ := []) (AdV.ofRd (Rd.must _)) ?_
  refine AdV.bind (l₁ := []) (AdV.ofRd (rd_planesAt g lm 0 hb)) ?_
  refine AdV.bind (l₁ := []) (AdV.ofRd (rd_planesAt g lm 1 hb)) ?_
  refine AdV.bind (l₁ := []) (v := countT g lm pinT) (AdV.ofRd ?_) ?_
  · unfold countT
    refine Rd.foldlM _ _ ?_ _ _
    intro f col
    exact Rd.bind (hp col) (Rd.pure _)
  · exact AdV.bind (l₁ := []) (adV_pscRow _ _ _) (AdV.pure _)

/-- `Forest.planeLins` adds just the three forms. -/
theorem ad_planeLins (g : Forest.Heard) (lm : ℕ) (hb : ∀ e x, Rd t K (bit e x) (bitT e x))
    (hp : ∀ x, Rd t K (pin x) (pinT x)) :
    Ad t K (Forest.planeLins g lm bit pin) (planeFormsT g lm bitT pinT).toList := by
  unfold Forest.planeLins Forest.planesAdded
  refine AdV.ad (AdV.bind (l₁ := []) (adV_planeClaims g lm hb hp) ?_)
  exact Ad.adV (Ad.then0 (ad_forM_lin _) (ad_paid _))

end

/-! ### the lookup's own claims, and its join -/

section
variable {t K : ℕ}

theorem ad_objects (g : Forest.Heard) : Ad t K (Forest.objects g) g.rows.toList :=
  Ad.then0 (ad_forM_lin g.rows) (ad_paid _)

theorem adV_join (g : Forest.Heard) (KF : Array Aff) :
    AdV t K (Forest.join g KF) (joinForm g KF) [] :=
  AdV.after (Rd.unit _) (AdV.seq (l₂ := []) (ad_paid _) (AdV.pure _))

end

end Fo
