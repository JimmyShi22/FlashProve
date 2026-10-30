-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoSiteOwn.lean.
The lookup on the digits, at the fields of the record with which the smallness test's messages
begin.

`site_Z` (OnBytes/Tie/Pv/Lookup/Ends/FoSite.lean) names the lookup's arguments by the record tl'
that the draw of the matrix
returns.

 * `drawMatrixF_ok`: that draw leaves the sub-proof's state as it is, and the record that it returns
   is tl with the matrix and the first columns filled in.
 * `site_Z_own`: so, under `site_Z`'s premises (the routine returns r from (L, F, c); `Sized F`; c
   is on a view), the lookup's routine has run at tl's own calls, public numbers and bound, from
   (F1, c1) to the state and the context of the routine's result r, and r's record keeps the
   lookup's record g under `heard`. (F1, c1) is where the commitment ended, which ran from (L, F,
   c5); c5 is where the draw ended, which ran from (F, c).

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoSite

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

theorem drawMatrixF_ok (tl tl' : HTailF2) (F F5 : Fork) (c c5 : Ctx)
    (h : tl.drawMatrixF F c = .ok ((tl', F5), c5)) :
    F5 = F ∧ tl' = { tl with cfF := tl'.cfF, cfFirst := tl'.cfFirst } := by
  unfold HTailF2.drawMatrixF at h
  obtain ⟨_, F1, c1, h1, h⟩ := (bind_ok _ _ _ _ _).1 h
  obtain ⟨_, d1, _, e1⟩ := (lift_ok _ _ _ _).1 h1
  cases e1
  obtain ⟨_, F2, c2, h2, h⟩ := (bind_ok _ _ _ _ _).1 h
  obtain ⟨_, d2, _, e2⟩ := (lift_ok _ _ _ _).1 h2
  cases e2
  cases (pure_ok _ _ _ _).1 h
  exact ⟨rfl, rfl⟩

theorem site_Z_own (tl : HTailF2) (L : LinkCtx) (F : Fork) (c : Ctx)
    (r : ((HTailF2 × LinkCtx) × Fork) × Ctx) (h : tl.transcriptF L F c = .ok r) (hF : Sized F)
    (hd : c.ch.dry = false) :
    ∃ (tl' : HTailF2) (F1 : Fork) (c5 c1 : Ctx) (g : Forest.Heard),
      tl.drawMatrixF F c = .ok ((tl', F), c5) ∧
      rootInH [tl.ix.ZZ, tl.ix.BZ] L F c5 = .ok ((((), r.1.1.2), F1), c1) ∧
      Forest.pad #[tl.z1.call, tl.z2.call] tl.f9.pub tl.lidb F1 c1 = .ok ((g, r.1.2), r.2) ∧
      r.1.1.1.heard = some g ∧ Sized F1 ∧ Later F F1 ∧ Clean c1 := by
  obtain ⟨tl', F5, F1, c5, c1, L6, g, a1, a2, a3, a4, a5, a6, a7⟩ := site_Z tl L F c r h hF hd
  obtain ⟨rfl, e⟩ := drawMatrixF_ok _ _ _ _ _ _ a1
  have e1 : tl'.ix = tl.ix := by rw [e]
  have e2 : tl'.z1 = tl.z1 := by rw [e]
  have e3 : tl'.z2 = tl.z2 := by rw [e]
  have e4 : tl'.f9 = tl.f9 := by rw [e]
  have e5 : tl'.lidb = tl.lidb := by rw [e]
  rw [e1] at a2
  rw [e2, e3, e4, e5] at a3
  refine ⟨tl', F1, c5, c1, g, a1, ?_, a3, ?_, a5, a6, a7⟩
  · rw [a4]
    exact a2
  · rw [a4]

end Fo
