-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Port/LookLins.lean: adding a list of claims, and the routine that adds the
three claims on the planes of a lookup (`Forest.planeLins`, OnBytes/Model/Look.lean): what a run
that returns is made of.

Theorems with their proofs.

Main names:
  `forM_lin`: adding the claims of an array one after the other (`Array.forM SubM.lin`) succeeds
    exactly where the steps on the state do (`Fork.lins`, OnBytes/Model/HideLaws.lean); it goes on
    with that state and leaves the channel's context as it was.
  `paid_ok`: marking an owed claim as added.
  `planeLins_ok`: the three claims are made (`Forest.planeClaims`), added, and marked as added.

Limits: nothing on what the three claims are. The three laws say when a run returns; nothing more is
said of a run that fails.


-/
import OnBytes.Model.HideLaws
import OnBytes.Model.Look
import OnBytes.Tie.Pv.Psc.PscRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.LookRun
open OnBytes OnBytes.Model OnBytes.PscRun

/-- Adding the claims of a list, one after the other. -/
theorem forM_linL : ∀ (l : List Aff) (F G : Fork) (c c' : Ctx),
    (l.foldlM (fun (_ : PUnit) a => SubM.lin a) PUnit.unit : SubM PUnit) F c =
      .ok ((PUnit.unit, G), c') ↔ F.lins l = some G ∧ c' = c
  | [], F, G, c, c' => by
    rw [List.foldlM_nil, pure_ok]
    simp only [Fork.lins, List.foldlM_nil, Prod.mk.injEq, true_and]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
    · rintro ⟨h, rfl⟩
      exact ⟨(Option.some.inj h).symm, rfl⟩
  | a :: l, F, G, c, c' => by
    rw [List.foldlM_cons, bind_ok]
    simp only [Fork.lins, List.foldlM_cons]
    constructor
    · rintro ⟨_, F1, c1, h1, h2⟩
      obtain ⟨e1, rfl⟩ := (SubM.lin_run a F F1 c c1).1 h1
      obtain ⟨e2, rfl⟩ := (forM_linL l F1 G _ _).1 h2
      rw [e1]
      exact ⟨e2, rfl⟩
    · rintro ⟨h, rfl⟩
      cases e1 : F.lin a with
      | none => simp [e1] at h
      | some F1 =>
        rw [e1] at h
        exact ⟨(), F1, c', (SubM.lin_run a F F1 c' c').2 ⟨e1, rfl⟩,
          (forM_linL l F1 G _ _).2 ⟨h, rfl⟩⟩

/-- Adding the claims of an array, one after the other. -/
theorem forM_lin (rows : Array Aff) (F G : Fork) (c c' : Ctx) :
    (rows.forM SubM.lin : SubM PUnit) F c = .ok ((PUnit.unit, G), c') ↔
      F.lins rows.toList = some G ∧ c' = c := by
  unfold Array.forM
  rw [← Array.foldlM_toList]
  exact forM_linL _ _ _ _ _

/-- Marking an owed claim as added always succeeds and leaves the context. -/
theorem paid_ok (i : Nat) (F : Fork) (c : Ctx) (r : (Unit × Fork) × Ctx) :
    SubM.paid i F c = .ok r ↔ r = (((), F.paid i), c) := by
  unfold SubM.paid
  rw [change_ok]
  constructor
  · rintro ⟨_, h, rfl⟩
    rw [← Option.some.inj h]
  · rintro rfl
    exact ⟨_, rfl, rfl⟩

/-- The three claims on the planes are made, added, and marked as added. -/
theorem planeLins_ok (g : Forest.Heard) (lm : Nat) (bit : Nat → Nat → SubM Aff)
    (pin : Nat → SubM Aff) (F G : Fork) (c c' : Ctx) :
    Forest.planeLins g lm bit pin F c = .ok (((), G), c') ↔
      ∃ rows F1 H, Forest.planeClaims g lm bit pin F c = .ok ((rows, F1), c') ∧
        F1.lins rows.toList = some H ∧ G = H.paid g.owedPlanes := by
  unfold Forest.planeLins Forest.planesAdded
  rw [bind_ok]
  constructor
  · rintro ⟨rows, F1, c1, h1, h⟩
    rw [bind_ok] at h
    obtain ⟨_, H, c2, h2, h⟩ := h
    obtain ⟨e2, rfl⟩ := (forM_lin rows F1 H c1 c2).1 h2
    rw [paid_ok] at h
    obtain ⟨⟨-, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using h
    exact ⟨rows, F1, H, h1, e2, rfl⟩
  · rintro ⟨rows, F1, H, h1, e2, rfl⟩
    refine ⟨rows, F1, c', h1, ?_⟩
    rw [bind_ok]
    exact ⟨(), H, c', (forM_lin rows F1 H c' c').2 ⟨e2, rfl⟩, (paid_ok _ _ _ _).2 rfl⟩

end OnBytes.LookRun

#print axioms OnBytes.LookRun.forM_lin
#print axioms OnBytes.LookRun.planeLins_ok
