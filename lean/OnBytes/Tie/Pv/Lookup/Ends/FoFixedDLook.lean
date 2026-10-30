-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoFixedDLook.lean.
The lookup's routines: the value and the list of added claims as data.

The statements of OnBytes/Tie/Pv/Lookup/Ends/FoFixedUSLook.lean, one for one, with `FixedD`
(OnBytes/Tie/Pv/Lookup/Ends/FoFixedD.lean) in the place of `FixedUS`: each is a definition, made by
the tactic `fixedd`. What is asked of the records, and the instances, are those of
OnBytes/Tie/Pv/Lookup/Ends/FoFixedULook.lean. The limits of OnBytes/Tie/Pv/Lookup/Ends/FoFixedD.lean
stand here too.

Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed that a run returns.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoFixedD
import OnBytes.Tie.Pv.Lookup.Ends.FoFixedULook

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

variable {t0 : ℕ}

def FixedD.hideRun (first : ℕ) (v : Array E) (f : E) :
    FixedD t0 (SubM.change (·.hideRun first v f)) :=
  FixedD.unit fun F c a G c' hr hs => by
    obtain ⟨G', h1, e⟩ := (change_ok _ _ _ _).1 hr
    have e2 : G = G' := congrArg (fun x : (Unit × Fork) × Ctx => x.1.2) e
    rw [e2]
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hideRun_fields h1
    exact ⟨added_same hs a1 a2 a3 a4 a5 a6, cols_of_trees a1⟩

macro_rules | `(tactic| fixedd_rule) => `(tactic| with_reducible exact FixedD.hideRun _ _ _)

def fixedD_pscRow (p : Psc) (S0 : E) (kept : Aff) [Good t0 p] [Good t0 kept] :
    FixedD t0 (pscRow p S0 kept) := by fixedd
def fixedD_objects (g : Forest.Heard) [Good t0 g] : FixedD t0 (Forest.objects g) := by fixedd
def fixedD_joinAdded (g : Forest.Heard) : FixedD t0 (Forest.joinAdded g) := by fixedd
def fixedD_planesAdded (g : Forest.Heard) : FixedD t0 (Forest.planesAdded g) := by fixedd
def fixedD_paddingLaid (g : Forest.Heard) (l : Array ℕ) :
    FixedD t0 (Forest.paddingLaid g l) := by fixedd
def fixedD_join (g : Forest.Heard) (KF : Array Aff) [Good t0 g] [Good t0 KF] :
    FixedD t0 (Forest.join g KF) := by fixedd
def fixedD_planeClaims (g : Forest.Heard) (lm : ℕ) (bit : ℕ → ℕ → SubM Aff)
    (pin : ℕ → SubM Aff) [Good t0 g] (hb : ∀ e col, FixedD t0 (bit e col))
    (hp : ∀ col, FixedD t0 (pin col)) : FixedD t0 (Forest.planeClaims g lm bit pin) := by fixedd
def fixedD_planeLins (g : Forest.Heard) (lm : ℕ) (bit : ℕ → ℕ → SubM Aff)
    (pin : ℕ → SubM Aff) [Good t0 g] (hb : ∀ e col, FixedD t0 (bit e col))
    (hp : ∀ col, FixedD t0 (pin col)) : FixedD t0 (Forest.planeLins g lm bit pin) := by fixedd

end Fo
