-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/FlPort/FoPlaneClaims.lean: a carried copy, made by a program, not typed by hand.

Of which file: OnBytes/Tie/Pv/Lookup/Forest/FoPlaneClaims.lean, as it lies in this library.
What is carried: those of its declarations that depend on a context of the verifier program's
channel, and no other:
  Quiet, got, quiet_ok, fold_quiet, planesAt_ok, planeClaims_run, planeClaims_ok
How: by one swap of names throughout: a context becomes a tape; a routine
of the program becomes the library's flat function of the same text (OnBytes/K/Kc/Flat.lean,
OnBytes/K/Kc/FlatHear.lean). The laws on "returns" are those of Johnson/Top/H/FlPort/Kit.lean. Every
other name is the library's own: plain records, pure functions and lemmas on them, used from where
they lie. Those of OnBytes/Tie/Pv/ that the text names, as far as a program sees them:
  countAff, leaves, planesAff, sBit
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
import OnBytes.Tie.Pv.Lookup.Forest.FoPlaneClaims
import Johnson.Top.H.FlPort.Kit
import Johnson.Desc.First.Look.LookPlanes
import Johnson.Top.H.FlPort.PscWhole
import Johnson.Top.H.FlPort.PscRun

set_option autoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open Cb Cb.Fo Cb.Fo.PlaneClaims VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun _root_.Fo

section
variable {K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K)

end

/-- If the routine returns, it turns neither the state of the sub-proof nor the context. -/
def Quiet (x : Fl Aff) : Prop := ∀ F c r, x F c = .ok r → r.1.2 = F ∧ r.2 = c

/-- The form that the routine returns. -/
def got (x : Fl Aff) (F : Fork) (c : Tape) : Aff :=
  match x F c with
  | some r => r.1
  | none => {}

theorem quiet_ok {x : Fl Aff} (hx : Quiet x) {F : Fork} {c : Tape} {r : (Aff × Fork) × Tape}
    (h : x F c = .ok r) : r = ((got x F c, F), c) := by
  obtain ⟨h1, h2⟩ := hx F c r h
  obtain ⟨⟨a, G⟩, c'⟩ := r
  have e : got x F c = a := by
    unfold got
    rw [h]
    try rfl
  simp only at h1 h2
  rw [e, h1, h2]

/-- A fold over quiet routines is a plain fold. -/
theorem fold_quiet (x : ℕ → Fl Aff) (hx : ∀ col, Quiet (x col)) (step : Aff → ℕ → Aff → Aff) :
    ∀ (l : List ℕ) (s : Aff) (F : Fork) (c : Tape) (r : (Aff × Fork) × Tape),
    (l.foldlM (fun f col => x col >>= fun a => pure (step f col a)) s) F c = .ok r →
    r = ((l.foldl (fun f col => step f col (got (x col) F c)) s, F), c)
  | [], s, F, c, r, h => (foldlM_nil_ok _ s F c r).1 h
  | col :: l, s, F, c, r, h => by
    obtain ⟨s₁, F₁, c₁, h1, h2⟩ := (foldlM_cons_ok _ s col l F c r).1 h
    obtain ⟨a, G, c2, h3, h4⟩ := (bind_ok _ _ F c _).1 h1
    have e3 := quiet_ok (hx col) h3
    have e4 := (pure_ok _ G c2 _).1 h4
    simp only [Prod.mk.injEq] at e3 e4
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e3
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e4
    exact fold_quiet x hx step l _ _ _ r h2

theorem planesAt_ok (g : Heard) (lm e : ℕ) (bit : ℕ → ℕ → Fl Aff) (hb : ∀ col, Quiet (bit e col))
    (F : Fork) (c : Tape) (r : (Aff × Fork) × Tape) (h : planesAtF g lm e bit F c = .ok r) :
    r = ((planesAff g lm e fun col => got (bit e col) F c, F), c) :=
  fold_quiet (bit e) hb (fun f col a => Aff.addMul f a
    (mulE ((eqTab ((g.zb e).extract g.shape.kT (g.shape.kT + g.shape.cK))).getD
        (col / 2 ^ (g.shape.kT + 5 - lm)) zeroE)
      ((eqTab ((g.zb e).extract 0 (g.shape.kT + 5 - lm))).getD
        (col % 2 ^ (g.shape.kT + 5 - lm)) zeroE))) _ _ F c r h

/-- A run of `Forest.planeClaims` that returns is a run of the leaves' claim, from the same state
and context, with the planes' form at the leaves' point kept. -/
theorem planeClaims_run (g : Heard) (lm : ℕ) (bit : ℕ → ℕ → Fl Aff) (pin : ℕ → Fl Aff)
    (hb : ∀ e col, Quiet (bit e col)) (hp : ∀ col, Quiet (pin col))
    (F G : Fork) (c c' : Tape) (rows : Array Aff)
    (h : planeClaimsF g lm bit pin F c = .ok ((rows, G), c')) :
    (planeCols g.shape lm).toBool = true ∧ ∃ row p',
      Fl.pscRow g.leaves oneE
        (Aff.scale (planesAff g lm 0 fun col => got (bit 0 col) F c) g.leavesA) F c =
          .ok (((row, p'), G), c') ∧
      rows = #[row, Aff.slot g.sBit - planesAff g lm 1 fun col => got (bit 1 col) F c,
        countAff g lm fun col => got (pin col) F c] := by
  unfold planeClaimsF at h
  obtain ⟨_, F1, c1, h1, k1⟩ := (bind_ok _ _ F c _).1 h
  obtain ⟨hm, e1⟩ := (must_ok _ F c _).1 h1
  simp only [Prod.mk.injEq] at e1
  obtain ⟨⟨_, hF1⟩, hc1⟩ := e1
  rw [hF1, hc1] at k1
  obtain ⟨at0, F2, c2, h2, k2⟩ := (bind_ok _ _ F c _).1 k1
  have e2 := planesAt_ok g lm 0 bit (hb 0) F c _ h2
  simp only [Prod.mk.injEq] at e2
  obtain ⟨⟨ha0, hF2⟩, hc2⟩ := e2
  rw [hF2, hc2] at k2
  obtain ⟨at1, F3, c3, h3, k3⟩ := (bind_ok _ _ F c _).1 k2
  have e3 := planesAt_ok g lm 1 bit (hb 1) F c _ h3
  simp only [Prod.mk.injEq] at e3
  obtain ⟨⟨ha1, hF3⟩, hc3⟩ := e3
  rw [hF3, hc3] at k3
  obtain ⟨cnt, F4, c4, h4, k4⟩ := (bind_ok _ _ F c _).1 k3
  have e4 := fold_quiet pin hp (fun f _ a => f + a) _ _ F c _ h4
  simp only [Prod.mk.injEq] at e4
  obtain ⟨⟨hcn, hF4⟩, hc4⟩ := e4
  rw [hF4, hc4] at k4
  obtain ⟨⟨row, p'⟩, F5, c5, h5, k5⟩ := (bind_ok _ _ F c _).1 k4
  have e6 := (pure_ok _ F5 c5 _).1 k5
  simp only [Prod.mk.injEq] at e6
  obtain ⟨⟨hr, hG⟩, hc'⟩ := e6
  refine ⟨hm, row, p', ?_, ?_⟩
  · rw [hG, hc', ← ha0]
    exact h5
  · rw [hr, ha1, hcn]
    rfl

/-- **What a run of `Forest.planeClaims` that returns has done.** -/
theorem planeClaims_ok (g : Heard) (lm : ℕ) (bit : ℕ → ℕ → Fl Aff) (pin : ℕ → Fl Aff)
    (hb : ∀ e col, Quiet (bit e col)) (hp : ∀ col, Quiet (pin col))
    (F G : Fork) (c c' : Tape) (rows : Array Aff)
    (h : planeClaimsF g lm bit pin F c = .ok ((rows, G), c')) :
    (planeCols g.shape lm).toBool = true ∧ c' = c ∧
      g.leaves.rowMade = false ∧ g.leaves.started = true ∧ g.leaves.vars.isEmpty = false ∧
      g.leaves.r.size = g.leaves.vars.size ∧
      F.hideRun g.leaves.first (Array.replicate g.leaves.walk.1.length zeroE) (subE zeroE oneE) =
        some G ∧
      rows = #[g.leaves.rowForm oneE
          (Aff.scale (planesAff g lm 0 fun col => got (bit 0 col) F c) g.leavesA),
        Aff.slot g.sBit - planesAff g lm 1 fun col => got (bit 1 col) F c,
        countAff g lm fun col => got (pin col) F c] := by
  obtain ⟨hm, row, p', h5, hr⟩ := planeClaims_run g lm bit pin hb hp F G c c' rows h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, _⟩ := pscRow_ok _ _ _ _ _ _ _ _ _ h5
  exact ⟨hm, a5, a1, a2, a3, a4, a6, by rw [hr, a7]⟩

section
variable {K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K) (W : World K)

end

end Fo.Tp
