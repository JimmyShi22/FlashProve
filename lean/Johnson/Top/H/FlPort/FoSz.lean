-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/FlPort/FoSz.lean: a carried copy, made by a program, not typed by hand.

Of which file: OnBytes/Tie/Pv/Lookup/Forest/FoSz.lean, as it lies in this library.
What is carried: those of its declarations that depend on a context of the verifier program's
channel, and no other:
  SzOn, SzOn.of, SzOn.nil, SzOn.append, SzOn.clean, took_unique, SzOn.view, SzOn.any, foldlM_sz
How: by one swap of names throughout: a context becomes a tape; a routine
of the program becomes the library's flat function of the same text (OnBytes/K/Kc/Flat.lean,
OnBytes/K/Kc/FlatHear.lean). The laws on "returns" are those of Johnson/Top/H/FlPort/Kit.lean. Every
other name is the library's own: plain records, pure functions and lemmas on them, used from where
they lie. Those of OnBytes/Tie/Pv/ that the text names, as far as a program sees them:
  drawnOf, flEv, flEv_sz, rdRV, sentOf, szEv, szEv_append, view
The comments on the declarations are the library's, under the same swap: where they say "run" or
"view", read: on a tape.

Limits. What is proved here is proved of the flat functions alone, and a flat function tests less of
the plan than the program's routine (the paragraph "Not claimed" in the head of
OnBytes/K/Kc/Flat.lean). Nothing is said where a function refuses. A tie: it has no error term. If
the source file turns, this copy does not follow by itself. In the list of names a use by dot
notation on a hypothesis is not seen, and a short name may stand once too often. That no routine
in a context is reached from a statement or a proof here is meant, and is not shown in this
library.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoSz
import Johnson.Top.H.FlPort.Kit
import Johnson.Top.H.FlPort.PscWhole
import Johnson.Top.H.FlPort.PscRun
import Johnson.Top.H.FlPort.FoRds
import Johnson.Top.H.FlPort.FoHeard

set_option autoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open TwV OnBytes OnBytes.Model OnBytes.PscRun

section
variable {K : Type} [CommRing K] (ρ : Reading K)

end

/-- Some row of rounds leads from c to c' and has the sizes p. -/
def SzOn (c c' : Tape) (p : List (ℕ × ℕ)) : Prop := ∃ l, Evs l c c' ∧ Rds l ∧ szEv l = p

theorem SzOn.of {c c' : Tape} {l : List Ev} (he : Evs l c c') (hl : Rds l) : SzOn c c' (szEv l) :=
  ⟨l, he, hl, rfl⟩

theorem SzOn.nil (c : Tape) : SzOn c c [] := ⟨[], rfl, Rds.nil, rfl⟩

theorem SzOn.append {c c₁ c' : Tape} {p q : List (ℕ × ℕ)} (h1 : SzOn c c₁ p) (h2 : SzOn c₁ c' q) :
    SzOn c c' (p ++ q) := by
  obtain ⟨l₁, e1, r1, s1⟩ := h1
  obtain ⟨l₂, e2, r2, s2⟩ := h2
  exact ⟨l₁ ++ l₂, (evs_append _ _ _ _).2 ⟨_, e1, e2⟩, r1.append r2,
    by rw [szEv_append r1, s1, s2]⟩

theorem SzOn.clean {c c' : Tape} {p : List (ℕ × ℕ)} (h : SzOn c c' p) (hc : Clean c) :
    Clean c' := by
  obtain ⟨l, e, r, _⟩ := h
  obtain ⟨_, ht, _⟩ := rds_took Reading.gl r hc e
  exact ht.2.1

/-- On a view the rounds between two contexts are fixed by the contexts. -/
theorem took_unique {c c' : Tape} {rv rv' : List FlatRound} (h : Took c rv c')
    (h' : Took c rv' c') : rv = rv' := List.append_cancel_right (h.2.2.symm.trans h'.2.2)

/-- On a view the rounds that lie between c and c' have the sizes p. -/
theorem SzOn.view {c c' : Tape} {p : List (ℕ × ℕ)} (h : SzOn c c' p) (hc : Clean c)
    {rv : List FlatRound} (ht : Took c rv c') :
    rv.map (fun r => ((sentOf r).length, (drawnOf r).length)) = p := by
  obtain ⟨l, e, r, s⟩ := h
  obtain ⟨rv', ht', hf⟩ := rds_took Reading.gl r hc e
  rw [took_unique ht ht', ← s, ← flEv_sz Reading.gl l, hf, List.map_map]
  refine List.map_congr_left fun x _ => ?_
  simp [rdRV]

/-- On a view every row of rounds from c to c' has the sizes p, under every reading. -/
theorem SzOn.any {K : Type} [CommRing K] (ρ : Reading K) {c c' : Tape} {p : List (ℕ × ℕ)}
    (h : SzOn c c' p) (hc : Clean c) {l : List Ev} (hl : Rds l) (he : Evs l c c') :
    (flEv ρ l).map (fun r => (r.1.length, r.2.length)) = p := by
  obtain ⟨rv, ht, hf⟩ := rds_took ρ hl hc he
  rw [← h.view hc ht, hf, List.map_map]
  refine List.map_congr_left fun x _ => ?_
  simp [rdRV]

/-- A loop's sizes are its steps' sizes, one after the other. -/
theorem foldlM_sz {α σ : Type} (f : σ → α → Fl σ) (p : α → List (ℕ × ℕ))
    (hf : ∀ (s s' : σ) (a : α) (F G : Fork) (c c' : Tape),
      f s a F c = .ok ((s', G), c') → Clean c → SzOn c c' (p a)) :
    ∀ (l : List α) (s s' : σ) (F G : Fork) (c c' : Tape),
      (l.foldlM f s) F c = .ok ((s', G), c') → Clean c → SzOn c c' (l.flatMap p)
  | [], s, s', F, G, c, c', h, _ => by
    have e := (foldlM_nil_ok f s F c _).1 h
    have e3 : c' = c := congrArg (fun x : (σ × Fork) × Tape => x.2) e
    rw [e3]
    exact SzOn.nil c
  | a :: l, s, s', F, G, c, c', h, hc => by
    obtain ⟨s₁, F₁, c₁, h1, h2⟩ := (foldlM_cons_ok f s a l F c _).1 h
    have z1 := hf s s₁ a F F₁ c c₁ h1 hc
    rw [List.flatMap_cons]
    exact z1.append (foldlM_sz f p hf l s₁ s' F₁ G c₁ c' h2 (z1.clean hc))


end Fo.Tp
