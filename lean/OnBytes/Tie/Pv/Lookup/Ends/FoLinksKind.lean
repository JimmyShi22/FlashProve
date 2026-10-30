-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoLinksKind.lean.
Each link of a request's chain holds one of the three kinds of sub-proof.

`LinksRan` (OnBytes/Tie/Pv/Lookup/Ends/FoLinks.lean) speaks of a link's routine as a field of its
record. Here the field is
opened.

 * `Kind x`: the routine x is that of a group of layers with its value under `some`, or attention's
   with `none` handed on behind it, or the output head's with its value under `some`: the three
   forms of OnBytes/Model/VerifyLinks.lean.
 * `linksOf_kind`, `built_kind`: each link of `Verify.linksOf`, and each link as the verifier runs
   them, holds a routine of one of the three forms.
 * `some_ok`, `none_ok`: "the run returns" for the two forms around a routine: the routine itself
   has returned, from the same three states and to the same three, with the value that stands under
   `some`.

So a run equation of a link's routine in `LinksRan` is a run equation of one of the three routines,
with the same start and the same end.

Not claimed: anything on soundness, completeness or hiding.
Nor does `Kind` say at which arguments the routine stands: the plan, the group and the public
records are bound by "there is" and tied to nothing of the request's public record.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoLinksOf

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

/-- The three forms in which a sub-proof's routine is handed to a link. -/
def Kind (x : LinkM (Option WsForkOut)) : Prop :=
  (∃ P hp g, x = some <$> Layer.runForkHidG2 P hp g) ∨
  (∃ A, x = (Attention.run A >>= fun _ => pure none)) ∨
  (∃ s Y b hp O cov wsLay, x = some <$> Head.runForkHidH2 s Y b hp O cov wsLay)

theorem linksOf_kind (X : Verify.Public) (cov : Head.Covered) (links : Array Stages.LinkH)
    (h : Verify.linksOf X cov = .ok links) : ∀ Y ∈ links.toList, Kind Y.run := by
  unfold Verify.linksOf at h
  refine listLinksH_run Kind _ _ _ _ _ links ?_ ?_ ?_ h
  · intro s hs
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hs
    simp only [Array.getElem_toList, Array.getElem_mapIdx]
    exact Or.inl ⟨_, _, _, rfl⟩
  · intro a ha
    rw [Array.toList_map, List.mem_map] at ha
    obtain ⟨P, _, rfl⟩ := ha
    exact Or.inr (Or.inl ⟨P, rfl⟩)
  · exact Or.inr (Or.inr ⟨_, _, _, _, _, _, _, rfl⟩)

theorem built_kind (X : Verify.Public) (cov : Head.Covered) (links built : Array Stages.LinkH)
    (h : Verify.linksOf X cov = .ok links) :
    ∀ Y ∈ (built.zipWith (fun b l => { b with run := l.run }) links).toList, Kind Y.run := by
  intro Y hY
  rw [Array.toList_zipWith] at hY
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hY
  rw [List.getElem_zipWith]
  have hi' : i < links.toList.length := by
    rw [List.length_zipWith] at hi
    omega
  exact linksOf_kind X cov links h (links.toList[i]) (List.getElem_mem hi')

section
variable {α β : Type}

theorem some_ok (x : LinkM α) (L L' : LinkCtx) (F F' : Fork) (c c' : Ctx) (o : Option α)
    (h : (some <$> x) L F c = .ok (((o, L'), F'), c')) :
    ∃ a, o = some a ∧ x L F c = .ok (((a, L'), F'), c') := by
  rw [← bind_pure_comp] at h
  obtain ⟨a, L1, F1, c1, h1, h2⟩ := (bindL_ok _ _ _ _ _ _).1 h
  obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ : ((o = some a ∧ L' = L1) ∧ F' = F1) ∧ c' = c1 := by
    simpa [Prod.ext_iff] using (pureL_ok _ _ _ _ _).1 h2
  exact ⟨a, rfl, h1⟩

theorem none_ok (x : LinkM α) (L L' : LinkCtx) (F F' : Fork) (c c' : Ctx) (o : Option β)
    (h : (x >>= fun _ => (pure none : LinkM (Option β))) L F c = .ok (((o, L'), F'), c')) :
    ∃ a, o = none ∧ x L F c = .ok (((a, L'), F'), c') := by
  obtain ⟨a, L1, F1, c1, h1, h2⟩ := (bindL_ok _ _ _ _ _ _).1 h
  obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ : ((o = none ∧ L' = L1) ∧ F' = F1) ∧ c' = c1 := by
    simpa [Prod.ext_iff] using (pureL_ok _ _ _ _ _).1 h2
  exact ⟨a, rfl, h1⟩

end

end Fo
