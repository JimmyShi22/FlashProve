-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoFixedULook.lean.
The lookup's routines of the second pass are fixed before the state and read one array alone.

What is asked of the records: of a sumcheck's record Psc: that the form start is InU; of the
lookup's record Forest.Heard: that its rows, the record of its sumcheck on the leaves and the form
cEnd are good.
States: `FixedU.hideRun`; that Psc.rowForm and addSlots keep goodness; Fo.FixedU t0
(OnBytes/Tie/Pv/Lookup/Ends/FoFixedU.lean, with its limits) of pscRow, Forest.objects, joinAdded,
planesAdded, paddingLaid, join (for good key forms), planeClaims and planeLins (for callers'
routines bit and pin that are FixedU t0): each for a record that is good, where it reads one.

Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed that a record which a run of Forest.pad returns is good: no file of this library
shows it.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoFixedU
import OnBytes.Model.Look

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

instance goodPsc : HasGood Psc := ⟨fun t p => InU t p.start⟩
instance goodHeardF : HasGood Forest.Heard :=
  ⟨fun t g => good t g.rows ∧ good t g.leaves ∧ good t g.cEnd⟩

section
variable {t0 : ℕ}

instance (p : Psc) [h : Good t0 p] : Good t0 p.start := ⟨h.out⟩
instance (g : Forest.Heard) [h : Good t0 g] : Good t0 g.rows := ⟨h.out.1⟩
instance (g : Forest.Heard) [h : Good t0 g] : Good t0 g.leaves := ⟨h.out.2.1⟩
instance (g : Forest.Heard) [h : Good t0 g] : Good t0 g.cEnd := ⟨h.out.2.2⟩
instance (p : Psc) (b : Bool) [h : Good t0 p] : Good t0 { p with rowMade := b } := ⟨h.out⟩

instance good_addSlot (s : ℕ × Aff) (x : E) [Good t0 s] : Good t0 (addSlot s x) := by fixedu

instance good_addSlots (a : Aff) (first : ℕ) (form : Array E) [Good t0 a] :
    Good t0 (addSlots a first form) := by
  unfold addSlots
  have : Good t0 (form.foldl addSlot (first, a)) :=
    good_foldlArr _ (fun _ _ _ _ => inferInstance) _ _ inferInstance inferInstance
  exact inferInstance

instance good_rowForm (p : Psc) (S0 : E) (kept : Aff) [Good t0 p] [Good t0 kept] :
    Good t0 (p.rowForm S0 kept) := by fixedu

theorem FixedU.hideRun (first : ℕ) (v : Array E) (f : E) :
    FixedU t0 (SubM.change (·.hideRun first v f)) :=
  FixedU.unit fun F c a G c' hr hs => by
    obtain ⟨G', h1, e⟩ := (change_ok _ _ _ _).1 hr
    have e2 : G = G' := congrArg (fun x : (Unit × Fork) × Ctx => x.1.2) e
    rw [e2]
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hideRun_fields h1
    exact ⟨added_same hs a1 a2 a3 a4 a5 a6, cols_of_trees a1⟩

end

macro_rules | `(tactic| fixedu_rule) => `(tactic| with_reducible exact FixedU.hideRun _ _ _)

section
variable {t0 : ℕ}

theorem fixedU_pscRow (p : Psc) (S0 : E) (kept : Aff) [Good t0 p] [Good t0 kept] :
    FixedU t0 (pscRow p S0 kept) := by fixedu
theorem fixedU_objects (g : Forest.Heard) [Good t0 g] : FixedU t0 (Forest.objects g) := by fixedu
theorem fixedU_joinAdded (g : Forest.Heard) : FixedU t0 (Forest.joinAdded g) := by fixedu
theorem fixedU_planesAdded (g : Forest.Heard) : FixedU t0 (Forest.planesAdded g) := by fixedu
theorem fixedU_paddingLaid (g : Forest.Heard) (l : Array ℕ) :
    FixedU t0 (Forest.paddingLaid g l) := by fixedu
theorem fixedU_join (g : Forest.Heard) (KF : Array Aff) [Good t0 g] [Good t0 KF] :
    FixedU t0 (Forest.join g KF) := by fixedu
theorem fixedU_planeClaims (g : Forest.Heard) (lm : ℕ) (bit : ℕ → ℕ → SubM Aff)
    (pin : ℕ → SubM Aff) [Good t0 g] (hb : ∀ e col, FixedU t0 (bit e col))
    (hp : ∀ col, FixedU t0 (pin col)) : FixedU t0 (Forest.planeClaims g lm bit pin) := by fixedu
theorem fixedU_planeLins (g : Forest.Heard) (lm : ℕ) (bit : ℕ → ℕ → SubM Aff)
    (pin : ℕ → SubM Aff) [Good t0 g] (hb : ∀ e col, FixedU t0 (bit e col))
    (hp : ∀ col, FixedU t0 (pin col)) : FixedU t0 (Forest.planeLins g lm bit pin) := by fixedu

end
end Fo
