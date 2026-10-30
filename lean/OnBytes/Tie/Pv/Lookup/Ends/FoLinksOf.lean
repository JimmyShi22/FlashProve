-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoLinksOf.lean.
The routines in the links of a request's chain stay on the view, and a run on a whole view begins on
the view with no message open.

Two ends of `run_ran` (OnBytes/Tie/Pv/Lookup/Ends/FoLinks.lean).

 * `viewStart s v`: the context in which a run on a whole view begins, written out;
   `clean_viewStart`: it is on the view and no message is open. `runOn_start`: if the run of a block
   on a whole view gives a value (`Blk.runOn`), the block has returned that value from `viewStart s
   v`.
 * `loop_inv`: a loop over a list in the type of the functions that may refuse under a name: what
   holds of the state before, and is kept by every pass that returns, holds behind the loop.
   `excBind_ok`: "returns" for bind in that type.
 * `listLinksH_run`: each link that `listLinksH` returns holds the routine of one of the plans that
   it was given: what holds of all these routines holds of each link's.
 * `linksOf_stays`: each link of a request's chain (`Verify.linksOf`) holds a routine that stays on
   the view. `built_stays`: so does each link as the verifier runs them
   (OnBytes/Model/VerifyStages.lean): the records that were built before, each with the routine of
   the link at its place in `Verify.linksOf`.
 * `view_ran`: if links whose routines stay on the view run on a whole view and give a value, then
   the chain's calls have started from `viewStart s v`, and `LinksRan`
     (OnBytes/Tie/Pv/Lookup/Ends/FoLinks.lean) holds behind
   that start, to that value. No premise on the channel is left.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoLinks
import OnBytes.Model.VerifyLinks

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

/-- The context in which a run on a whole view begins. -/
def viewStart (s : Start) (v : Fmt.View) : Ctx :=
  { ch := { dry := false, entries := s.entries, samples := s.samples, firstTree := s.firstTree,
            left := v.rounds, opened := v.opened },
    st := s.st, book := s.book, keepNotes := false }

theorem clean_viewStart (s : Start) (v : Fmt.View) : Clean (viewStart s v) := ⟨rfl, rfl⟩

theorem runOn_start {α : Type} (b : Blk α) (s : Start) (v : Fmt.View) (a : α)
    (h : b.runOn s v = .ok a) : ∃ c', b (viewStart s v) = .ok (a, c') := by
  unfold Blk.runOn at h
  cases e : b.runNamed s false v.rounds v.opened with
  | error f =>
    rw [e] at h
    exact absurd h (by intro x; cases x)
  | ok p =>
    obtain ⟨a', c'⟩ := p
    rw [e] at h
    have ha : a' = a := by
      dsimp only at h
      (repeat' split at h) <;> first | (cases h; rfl) | (cases h)
    subst ha
    unfold Blk.runNamed at e
    split at e
    · exact ⟨c', e⟩
    · exact absurd e (by intro x; cases x)

/-- The state that a pass of a loop hands on. -/
def stepVal {σ : Type} : ForInStep σ → σ
  | .done s => s
  | .yield s => s

theorem loop_inv {ε β σ : Type} (Inv : σ → Prop) (f : β → σ → Except ε (ForInStep σ)) :
    ∀ (l : List β) (s s' : σ), Inv s →
      (∀ a ∈ l, ∀ t r, Inv t → f a t = .ok r → Inv (stepVal r)) →
      forIn l s f = .ok s' → Inv s'
  | [], s, s', hs, _, h => by
    rw [List.forIn_nil] at h
    cases h
    exact hs
  | a :: l, s, s', hs, hf, h => by
    rw [List.forIn_cons] at h
    cases e : f a s with
    | error x =>
      rw [e] at h
      exact absurd h (by intro y; cases y)
    | ok r =>
      rw [e] at h
      have hr := hf a (by simp) s r hs e
      cases r with
      | done t =>
        cases h
        exact hr
      | yield t =>
        exact loop_inv Inv f l t s' hr (fun b hb => hf b (List.mem_cons_of_mem _ hb)) h

theorem excBind_ok {ε α β : Type} (x : Except ε α) (f : α → Except ε β) (y : β) :
    (x >>= f) = .ok y ↔ ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e =>
    constructor
    · intro h
      cases h
    · rintro ⟨a, h, _⟩
      cases h
  | ok a =>
    constructor
    · intro h
      exact ⟨a, rfl, h⟩
    · rintro ⟨b, h, k⟩
      cases h
      exact k

theorem listLinksH_run (Q : LinkM (Option WsForkOut) → Prop) (NGr : Nat) (p4 : Bool)
    (G A : Array Stages.SubPlanH) (H : Stages.SubPlanH) (links : Array Stages.LinkH)
    (hG : ∀ s ∈ G.toList, Q s.run) (hA : ∀ a ∈ A.toList, Q a.run) (hH : Q H.run)
    (h : Stages.listLinksH NGr p4 G A H = .ok links) : ∀ X ∈ links.toList, Q X.run := by
  unfold Stages.listLinksH at h
  dsimp only at h
  split at h
  · exact absurd h (by intro x; cases x)
  · obtain ⟨_, _, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨r, hr, h⟩ := (excBind_ok _ _ _).1 h
    cases h
    have inv : ∀ X ∈ r.toList, Q X.run := by
      refine loop_inv (fun ls : Array Stages.LinkH => ∀ X ∈ ls.toList, Q X.run) _ _ _ _
        (by simp) ?_ hr
      rintro ⟨s, g⟩ hs t q ht hq
      have hs' : s ∈ G.toList := (List.mem_zipIdx hs).2.2 ▸ List.getElem_mem _
      have push : ∀ (ls : Array Stages.LinkH) (Y : Stages.LinkH),
          (∀ X ∈ ls.toList, Q X.run) → Q Y.run → ∀ X ∈ (ls.push Y).toList, Q X.run := by
        intro ls Y h1 h2 X hX
        rw [Array.toList_push, List.mem_append, List.mem_singleton] at hX
        rcases hX with hX | rfl
        · exact h1 X hX
        · exact h2
      dsimp only at hq
      split at hq
      · split at hq
        · rename_i a ha
          cases hq
          exact push _ _ (push _ _ ht (hG s hs')) (hA a (by
            have := Array.mem_of_getElem? ha
            exact Array.mem_toList_iff.2 this))
        · cases hq
          exact push _ _ ht (hG s hs')
      · cases hq
        exact push _ _ ht (hG s hs')
    intro X hX
    rw [Array.toList_push, List.mem_append, List.mem_singleton] at hX
    rcases hX with hX | rfl
    · exact inv X hX
    · exact hH

/-- Each link of a request's chain holds a routine that stays on the view. -/
theorem linksOf_stays (X : Verify.Public) (cov : Head.Covered) (links : Array Stages.LinkH)
    (h : Verify.linksOf X cov = .ok links) : ∀ Y ∈ links.toList, DryL Y.run := by
  unfold Verify.linksOf at h
  refine listLinksH_run (fun x => DryL x) _ _ _ _ _ links ?_ ?_ ?_ h
  · intro s hs
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hs
    simp only [Array.getElem_toList, Array.getElem_mapIdx]
    exact staysL_some (staysL_runG _ _ _)
  · intro a ha
    rw [Array.toList_map, List.mem_map] at ha
    obtain ⟨P, _, rfl⟩ := ha
    exact staysL_none (staysL_runA P)
  · exact staysL_some (staysL_runH _ _ _ _ _ _ _)

/-- The links as the verifier runs them: the records that were built before, each with the routine
of the link at its place in `Verify.linksOf`. -/
theorem built_stays (X : Verify.Public) (cov : Head.Covered) (links built : Array Stages.LinkH)
    (h : Verify.linksOf X cov = .ok links) :
    ∀ Y ∈ (built.zipWith (fun b l => { b with run := l.run }) links).toList, DryL Y.run := by
  intro Y hY
  rw [Array.toList_zipWith] at hY
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hY
  rw [List.getElem_zipWith]
  have hi' : i < links.toList.length := by
    rw [List.length_zipWith] at hi
    omega
  exact linksOf_stays X cov links h (links.toList[i]) (List.getElem_mem hi')

/-- Links whose routines stay on the view, run on a whole view. -/
theorem view_ran (links : Array Stages.LinkH) (p : Params.First) (wsLay : WsLay) (s : Start)
    (v : Fmt.View) (a : Proof.LinksResult) (hY : ∀ Y ∈ links.toList, DryL Y.run)
    (h : (Stages.runLinksH links p wsLay).runOn s v = .ok a) :
    ∃ (check check2 : ChainCheck) (c1 c2 c3 : Ctx),
      ChainCheck.start p.shape p.layout (viewStart s v) = .ok (check, c1) ∧
      LinksRan links p wsLay links.toList 0 check {} c1 ((check2, a), c2) ∧
      check2.finish c2 = .ok ((), c3) := by
  obtain ⟨c', hr⟩ := runOn_start _ s v a h
  obtain ⟨k, k2, c1, c2, e1, e2, e3⟩ := run_ran links p wsLay _ _ hY hr rfl
  exact ⟨k, k2, c1, c2, c', e1, e2, e3⟩

end Fo
