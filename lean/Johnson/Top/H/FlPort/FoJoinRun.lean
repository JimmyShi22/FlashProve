-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/FlPort/FoJoinRun.lean: a carried copy, made by a program, not typed by hand.

Of which file: OnBytes/Tie/Pv/Lookup/Forest/FoJoinRun.lean, as it lies in this library.
What is carried: those of its declarations that depend on a context of the verifier program's
channel, and no other:
  join_ok
How: by one swap of names throughout: a context becomes a tape; a routine
of the program becomes the library's flat function of the same text (OnBytes/K/Kc/Flat.lean,
OnBytes/K/Kc/FlatHear.lean). The laws on "returns" are those of Johnson/Top/H/FlPort/Kit.lean. Every
other name is the library's own: plain records, pure functions and lemmas on them, used from where
they lie. Those of OnBytes/Tie/Pv/ that the text names, as far as a program sees them:
  joinForm
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
import OnBytes.Tie.Pv.Lookup.Forest.FoJoinRun
import Johnson.Top.H.FlPort.Kit
import Johnson.Desc.First.Look.LookPlanes
import Johnson.Top.H.FlPort.PscWhole
import Johnson.Top.H.FlPort.PscRun

set_option autoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open VerifiableInference.Desc.First.Look
open TwV FoNums Finset OnBytes OnBytes.Model OnBytes.PscRun

/-- What a run of joinF returns. -/
theorem join_ok (g : Forest.Heard) (KF : Array Aff) (F G : Fork) (c c' : Tape) (r : Aff)
    (h : joinF g KF F c = .ok ((r, G), c')) :
    KF.size = g.shape.calls.size ∧ g.e.size = g.shape.calls.size ∧ c' = c ∧
      G = F.paid g.owedJoin ∧ r = joinForm g KF := by
  unfold joinF at h
  rw [bind_ok] at h
  obtain ⟨_, F1, c1, h1, h⟩ := h
  obtain ⟨hb, e1⟩ := (must_ok _ F c _).1 h1
  have a1 : F1 = F := congrArg (fun x : (Unit × Fork) × Tape => x.1.2) e1
  have a2 : c1 = c := congrArg (fun x : (Unit × Fork) × Tape => x.2) e1
  rw [a1, a2, bind_ok] at h
  obtain ⟨_, F2, c2, h2, h⟩ := h
  unfold joinAddedF paidF at h2
  obtain ⟨G2, hG, e2⟩ := (change_ok _ F c _).1 h2
  have b0 : F.paid g.owedJoin = G2 := Option.some.inj hG
  have b1 : F2 = G2 := congrArg (fun x : (Unit × Fork) × Tape => x.1.2) e2
  have b2 : c2 = c := congrArg (fun x : (Unit × Fork) × Tape => x.2) e2
  rw [b1, ← b0, b2] at h
  have e3 := (pure_ok _ _ _ _).1 h
  have d1 : r = _ := congrArg (fun x : (Aff × Fork) × Tape => x.1.1) e3
  have d2 : G = _ := congrArg (fun x : (Aff × Fork) × Tape => x.1.2) e3
  have d3 : c' = _ := congrArg (fun x : (Aff × Fork) × Tape => x.2) e3
  simp only [Bool.and_eq_true, beq_iff_eq] at hb
  exact ⟨hb.1, hb.2, d3, d2, d1⟩

section
variable {K : Type} [CommRing K] (ρ : Reading K) (W : World K)

end

end Fo.Tp
