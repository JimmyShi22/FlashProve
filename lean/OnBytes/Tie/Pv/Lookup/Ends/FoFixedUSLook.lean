-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoFixedUSLook.lean.
The lookup's routines of the second pass: Fo.FixedUS (OnBytes/Tie/Pv/Lookup/Ends/FoFixedUS.lean) in
the place of Fo.FixedU.

The statements are those of OnBytes/Tie/Pv/Lookup/Ends/FoFixedULook.lean, one for one, with
Fo.FixedUS in the place of Fo.FixedU and the tactic `fixedus` in the place of `fixedu`; what is
asked of the records, and the instances, are that file's. The limits of Fo.Fixed, Fo.FixedU and
Fo.FixedUS stand here too.

Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed here that a heard record is good: for the records of the checks' own runs that is
good_aHeard and good_hRun (OnBytes/Tie/Pv/Lookup/Ends/FoRetJoin.lean).

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoFixedUS
import OnBytes.Tie.Pv.Lookup.Ends.FoFixedULook

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

variable {t0 : ℕ}

theorem FixedUS.hideRun (first : ℕ) (v : Array E) (f : E) :
    FixedUS t0 (SubM.change (·.hideRun first v f)) :=
  FixedUS.unit fun F c a G c' hr hs => by
    obtain ⟨G', h1, e⟩ := (change_ok _ _ _ _).1 hr
    have e2 : G = G' := congrArg (fun x : (Unit × Fork) × Ctx => x.1.2) e
    rw [e2]
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hideRun_fields h1
    exact ⟨added_same hs a1 a2 a3 a4 a5 a6, cols_of_trees a1⟩

macro_rules | `(tactic| fixedus_rule) => `(tactic| with_reducible exact FixedUS.hideRun _ _ _)

theorem fixedUS_pscRow (p : Psc) (S0 : E) (kept : Aff) [Good t0 p] [Good t0 kept] :
    FixedUS t0 (pscRow p S0 kept) := by fixedus
theorem fixedUS_objects (g : Forest.Heard) [Good t0 g] : FixedUS t0 (Forest.objects g) := by fixedus
theorem fixedUS_joinAdded (g : Forest.Heard) : FixedUS t0 (Forest.joinAdded g) := by fixedus
theorem fixedUS_planesAdded (g : Forest.Heard) : FixedUS t0 (Forest.planesAdded g) := by fixedus
theorem fixedUS_paddingLaid (g : Forest.Heard) (l : Array ℕ) :
    FixedUS t0 (Forest.paddingLaid g l) := by fixedus
theorem fixedUS_join (g : Forest.Heard) (KF : Array Aff) [Good t0 g] [Good t0 KF] :
    FixedUS t0 (Forest.join g KF) := by fixedus
theorem fixedUS_planeClaims (g : Forest.Heard) (lm : ℕ) (bit : ℕ → ℕ → SubM Aff)
    (pin : ℕ → SubM Aff) [Good t0 g] (hb : ∀ e col, FixedUS t0 (bit e col))
    (hp : ∀ col, FixedUS t0 (pin col)) : FixedUS t0 (Forest.planeClaims g lm bit pin) := by fixedus
theorem fixedUS_planeLins (g : Forest.Heard) (lm : ℕ) (bit : ℕ → ℕ → SubM Aff)
    (pin : ℕ → SubM Aff) [Good t0 g] (hb : ∀ e col, FixedUS t0 (bit e col))
    (hp : ∀ col, FixedUS t0 (pin col)) : FixedUS t0 (Forest.planeLins g lm bit pin) := by fixedus

end Fo
