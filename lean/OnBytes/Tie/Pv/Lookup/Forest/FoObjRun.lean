-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoObjRun.lean.
The byte-level verifier's routine Forest.objects, run: what it leaves.

Forest.objects (OnBytes/Model/Look.lean) adds the claims of a lookup that read mask entries alone:
the tie's, the key levels', the table's levels', the bits' sumcheck's. It adds them one after the
other with SubM.lin and marks the owed claim as added.

States:
  lins_ok: a run of SubM.lin over a list of forms that returns leaves the context as it was and the
    state that Fork.lins gives (OnBytes/Model/HideLaws.lean).
  objects_ok: if a run of Forest.objects returns, the context is as it was, and the state is the one
    that Fork.lins gives on the record's rows, in their order, with the owed claim marked.
Not claimed: that a run returns. What the added claims do to the one equation is said by
Fork.lins_total (OnBytes/Model/HideLaws.lean).

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoEv

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

theorem lins_ok : ∀ (l : List Aff) (F G : Fork) (c c' : Ctx) (u u' : Unit),
    (l.foldlM (fun _ a => SubM.lin a) u) F c = .ok ((u', G), c') → F.lins l = some G ∧ c' = c
  | [], F, G, c, c', u, u', h => by
    have e := (foldlM_nil_ok _ u F c _).1 h
    have d2 : G = F := congrArg (fun x : (Unit × Fork) × Ctx => x.1.2) e
    have d3 : c' = c := congrArg (fun x : (Unit × Fork) × Ctx => x.2) e
    rw [d2]
    exact ⟨rfl, d3⟩
  | a :: l, F, G, c, c', u, u', h => by
    obtain ⟨s₁, F₁, c₁, h1, h2⟩ := (foldlM_cons_ok _ u a l F c _).1 h
    obtain ⟨e1, e2⟩ := (SubM.lin_run a F F₁ c c₁).1 h1
    obtain ⟨e3, e4⟩ := lins_ok l F₁ G c₁ c' s₁ u' h2
    refine ⟨?_, e4.trans e2⟩
    unfold Fork.lins at e3 ⊢
    rw [List.foldlM_cons, e1]
    exact e3

/-- What a run of Forest.objects leaves. -/
theorem objects_ok (g : Forest.Heard) (F G : Fork) (c c' : Ctx)
    (h : Forest.objects g F c = .ok (((), G), c')) :
    c' = c ∧ ∃ G₁, F.lins g.rows.toList = some G₁ ∧ G = G₁.paid g.owedObjects := by
  unfold Forest.objects at h
  rw [bind_ok] at h
  obtain ⟨u, F1, c1, h1, h⟩ := h
  have h1' : (g.rows.toList.foldlM (fun _ a => SubM.lin a) ()) F c = .ok ((u, F1), c1) := by
    rw [Array.foldlM_toList]
    exact h1
  obtain ⟨e1, e2⟩ := lins_ok _ F F1 c c1 () u h1'
  unfold SubM.paid at h
  obtain ⟨G2, hG, e3⟩ := (change_ok _ F1 c1 _).1 h
  have b0 : F1.paid g.owedObjects = G2 := Option.some.inj hG
  have b1 : G = G2 := congrArg (fun x : (Unit × Fork) × Ctx => x.1.2) e3
  have b2 : c' = c1 := congrArg (fun x : (Unit × Fork) × Ctx => x.2) e3
  exact ⟨b2.trans e2, F1, e1, b1.trans b0.symm⟩

end Fo
