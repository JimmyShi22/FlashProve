-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/ReadsLays.lean: kind K5: the step that makes the tables and closes the
list (Johnson/Desc/First/Att/ReadsBlock.lean: readsAtS): where it says yes, the carried record
behind it holds, inside the same attention link, the lookup's record and the four records unturned,
and tables that are Tab.tables of just these.

Main names:
  `Spec.ReadsLays`, `reads_lays`: readsAtS P s = .ok s' → ∃ a a' f, s.here = .att a ∧ s'.here = .att
    a' ∧ Lies a' f ∧ a'.g = a.g ∧ the four records unturned ∧ a'.F = a.F ∧ Tab.tables P.S P.mats
    P.nW f.g f.planes f.scores a'.d a'.x = some f.t.
  `reads_agree`: so Lies a' f and TablesAgree P a' f (Johnson/Desc/First/Att/Claims/Seated.lean)
    holds behind the step.
Limit: that no step between this one and the claims' runs turns g, the four records or t is not said
here: not shown in this file or in what it imports.
Used: plain records. The step calls L3.closeStep and L3.drawFront (Johnson/Top/H0/L3/Frame.lean):
plain functions on records into Except: three tests and the closing of the list; no context, no
round, no challenge. Their results are not opened here: only that the step returned.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.TablesAgree
import Johnson.Desc.First.Att.ReadsBlock

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Attention
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Att

namespace Spec

def ReadsLays : Prop :=
  ∀ (P : Plan) (s s' : S), readsAtS P s = .ok s' →
    ∃ a a' f, s.here = .att a ∧ s'.here = .att a' ∧ Lies a' f ∧ a'.g = a.g ∧ a'.planes = a.planes ∧
      a'.scores = a.scores ∧ a'.d = a.d ∧ a'.x = a.x ∧ a'.F = a.F ∧
      Tab.tables P.S P.mats P.nW f.g f.planes f.scores a'.d a'.x = some f.t

end Spec

theorem except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem reads_lays : Spec.ReadsLays := by
  intro P s s' h
  unfold readsAtS at h
  cases hh : s.here with
  | att a =>
    simp only [hh] at h
    cases hg : a.g with
    | none => simp only [hg] at h; cases h
    | some g =>
      cases hp : a.planes with
      | none => simp only [hg, hp] at h; cases h
      | some planes =>
        cases hsc : a.scores with
        | none => simp only [hg, hp, hsc] at h; cases h
        | some scores =>
          simp only [hg, hp, hsc] at h
          cases hr : readsStepE P a.tl ⟨g, planes, scores, a.d, a.x⟩ a.L s.st a.F with
          | error e => rw [hr] at h; cases h
          | ok r =>
            rw [hr] at h
            have e : s' = { s with here := .att { a with t := some r.1, tl := r.2.1 } } := by
              cases h
              rw [hg, hp, hsc]
            subst e
            refine ⟨a, _, ⟨g, planes, scores, r.1⟩, rfl, rfl, ⟨hg, hp, hsc, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
            unfold readsStepE at hr
            obtain ⟨_, _, hr⟩ := except_bind_ok hr
            obtain ⟨t, ht, hr⟩ := except_bind_ok hr
            obtain ⟨c, _, hr⟩ := except_bind_ok hr
            obtain ⟨_, _, hr⟩ := except_bind_ok hr
            have er : r = (t, c.tl, a.F.next) := by cases hr; rfl
            subst er
            show Tab.tables P.S P.mats P.nW g planes scores a.d a.x = some t
            cases hT : Tab.tables P.S P.mats P.nW g planes scores a.d a.x with
            | none => rw [hT] at ht; cases ht
            | some t' => rw [hT] at ht; cases ht; rfl
  | _ => simp only [hh] at h; cases h

/-- Behind the step, premise (a) of Johnson/Desc/First/Att/Claims/Seated.lean holds. -/
theorem reads_agree (P : Plan) (s s' : S) (h : readsAtS P s = .ok s') :
    ∃ a' f, s'.here = .att a' ∧ Lies a' f ∧ TablesAgree P a' f := by
  obtain ⟨_, a', f, _, h2, hl, _, _, _, _, _, _, ht⟩ := reads_lays P s s' h
  exact ⟨a', f, h2, hl, tablesAgree_of P a' f ht⟩

end K5Law
