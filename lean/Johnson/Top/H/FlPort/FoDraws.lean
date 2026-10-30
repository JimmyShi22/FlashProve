-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/FlPort/FoDraws.lean: a carried copy, made by a program, not typed by hand.

Of which file: OnBytes/Tie/Pv/Lookup/Forest/FoDraws.lean, as it lies in this library.
What is carried: those of its declarations that depend on a context of the verifier program's
channel, and no other:
  draws_ok
How: by one swap of names throughout: a context becomes a tape; a routine
of the program becomes the library's flat function of the same text (OnBytes/K/Kc/Flat.lean,
OnBytes/K/Kc/FlatHear.lean). The laws on "returns" are those of Johnson/Top/H/FlPort/Kit.lean. Every
other name is the library's own: plain records, pure functions and lemmas on them, used from where
they lie. Those of OnBytes/Tie/Pv/ that the text names, as far as a program sees them:
  drawsA, drawsEv
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
import OnBytes.Tie.Pv.Lookup.Forest.FoDraws
import Johnson.Top.H.FlPort.Kit
import Johnson.Top.H.FlPort.PscWhole
import Johnson.Top.H.FlPort.PscRun

set_option autoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open TwV FoNums OnBytes OnBytes.Model OnBytes.PscRun

theorem draws_ok (h : Sh) (F G : Fork) (c c' : Tape) (θ α a : E)
    (hr : lkDraws h F c = .ok (((θ, α, a), G), c')) :
    Evs (drawsEv h θ α) c c' ∧ G = F ∧ (¬ h.NC > 1 → θ = zeroE) ∧ a = drawsA h θ α := by
  unfold lkDraws at hr
  unfold drawsEv
  by_cases hN : h.NC > 1
  · rw [if_pos hN] at hr ⊢
    rw [bind_ok] at hr
    obtain ⟨θ', F1, c1, h1, hr⟩ := hr
    obtain ⟨a1, e1⟩ := (answer_ok _ _ _ _ _ _).1 h1
    rw [bind_ok] at hr
    obtain ⟨α', F2, c2, h2, hr⟩ := hr
    obtain ⟨a2, e2⟩ := (answer_ok _ _ _ _ _ _).1 h2
    rw [pure_ok] at hr
    obtain ⟨⟨⟨t1, t2, t3⟩, t4⟩, t5⟩ : ((θ = θ' ∧ α = α' ∧ a = drawsA h θ' α') ∧ G = F2) ∧ c' = c2 :=
      by
      simpa [Prod.ext_iff, drawsA] using hr
    subst t1 t2 t5
    exact ⟨(evs_append _ _ _ _).2 ⟨c1, a1, a2⟩, t4.trans (e2.trans e1), fun hn => absurd hN hn, t3⟩
  · rw [if_neg hN] at hr ⊢
    rw [bind_ok] at hr
    obtain ⟨θ', F1, c1, h1, hr⟩ := hr
    rw [pure_ok] at h1
    obtain ⟨⟨s1, s2⟩, s3⟩ : (θ' = zeroE ∧ F1 = F) ∧ c1 = c := by simpa [Prod.ext_iff] using h1
    rw [bind_ok] at hr
    obtain ⟨α', F2, c2, h2, hr⟩ := hr
    obtain ⟨a2, e2⟩ := (answer_ok _ _ _ _ _ _).1 h2
    rw [pure_ok] at hr
    obtain ⟨⟨⟨t1, t2, t3⟩, t4⟩, t5⟩ : ((θ = θ' ∧ α = α' ∧ a = drawsA h θ' α') ∧ G = F2) ∧ c' = c2 :=
      by
      simpa [Prod.ext_iff, drawsA] using hr
    subst t1 t2 t5 s3
    exact ⟨a2, t4.trans (e2.trans s2), fun _ => s1, t3⟩

section
variable {K : Type} [CommRing K] (ρ : Reading K)

end

end Fo.Tp
