-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/FlPort/FoTieRun.lean: a carried copy, made by a program, not typed by hand.

Of which file: OnBytes/Tie/Pv/Lookup/Forest/FoTieRun.lean, as it lies in this library.
What is carried: those of its declarations that depend on a context of the verifier program's
channel, and no other:
  tieStep_ok, tie_ok
How: by one swap of names throughout: a context becomes a tape; a routine
of the program becomes the library's flat function of the same text (OnBytes/K/Kc/Flat.lean,
OnBytes/K/Kc/FlatHear.lean). The laws on "returns" are those of Johnson/Top/H/FlPort/Kit.lean. Every
other name is the library's own: plain records, pure functions and lemmas on them, used from where
they lie. Those of OnBytes/Tie/Pv/ that the text names, as far as a program sees them:
  rhoT, tieCT, tiePsc, took
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
import OnBytes.Tie.Pv.Lookup.Forest.FoTieRun
import Johnson.Top.H.FlPort.Kit
import Johnson.Top.H.FlPort.PscWhole
import Johnson.Top.H.FlPort.PscRun

set_option autoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open OnBytes OnBytes.Model OnBytes.PscRun

/-- One step of the tie. -/
theorem tieStep_ok (a : E) (s : Forest.TieStep) (j : Nat) (F G : Fork) (c c' : Tape) (s' :
    Forest.TieStep)
    (h : lkTieStep a s j F c = .ok ((s', G), c')) :
    ∃ target mu eps sent beta v G1 vP vG summand,
      F.publicPart (if j = 0 then Aff.ofConst zeroE else Aff.slot s.sP) = some target ∧
      Evs [.sum mu, .ans .pscEpsilon eps, .read 3 sent, .ansNZ .pscY beta,
        .read (if j = 0 then 3 else 2) v, .empty .pscValues] c c' ∧
      sent.size = 3 ∧ v.size = (if j = 0 then 3 else 2) ∧
      (took (took F 1) (3 + if j = 0 then 3 else 2)).hideRun (F.next + 1 + 3) v beta = some G1 ∧
      G1.shown (if j = 0 then F.next + 1 + 3 + 1 else F.next + 1 + 3) = some vP ∧
      G1.shown ((if j = 0 then F.next + 1 + 3 + 1 else F.next + 1 + 3) + 1) = some vG ∧
      (if j = 0 then ∃ vZ, G1.shown (F.next + 1 + 3) = some vZ ∧ summand = subE vZ (mulE a (mulE
          (mulE vP vP) vG))
        else summand = mulE (mulE vP vP) vG) ∧
      G1.hideRun F.next
        (Array.replicate (tiePsc (if j = 0 then Aff.ofConst zeroE else Aff.slot s.sP) target mu eps
            beta F.next sent).walk.1.length zeroE)
        (subE zeroE oneE) = some G ∧
      s' = { rows := s.rows.push
              ((tiePsc (if j = 0 then Aff.ofConst zeroE else Aff.slot s.sP) target mu eps beta
                  F.next sent).rowForm summand {}),
             sZ := if j = 0 then F.next + 1 + 3 else s.sZ,
             sP := if j = 0 then F.next + 1 + 3 + 1 else F.next + 1 + 3,
             sG := s.sG.push ((if j = 0 then F.next + 1 + 3 + 1 else F.next + 1 + 3) + 1) } := by
  unfold lkTieStep at h
  rw [bind_ok] at h
  obtain ⟨p, F1, c1, h1, h⟩ := h
  obtain ⟨target, mu, eps, hpp, hev1, rfl, rfl⟩ := pscBegin_ok _ _ _ _ _ _ h1
  rw [bind_ok] at h
  obtain ⟨⟨first, p2⟩, F2, c2, h2, h⟩ := h
  obtain ⟨sent, beta, v, -, -, -, hs, hv, hev2, rfl, hG1, rfl⟩ := pscEnds_ok _ _ _ _ _ _ _ _ _ h2
  simp only [] at h
  rw [bind_ok] at h
  obtain ⟨vP, F3, c3, h3, h⟩ := h
  rw [shown_ok] at h3
  obtain ⟨vP', hvP, e3⟩ := h3
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e3
  rw [bind_ok] at h
  obtain ⟨vG, F4, c4, h4, h⟩ := h
  rw [shown_ok] at h4
  obtain ⟨vG', hvG, e4⟩ := h4
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e4
  by_cases hj : j = 0
  · subst hj
    simp only [↓reduceIte] at h hpp hv hG1 hvP hvG hev2 ⊢
    rw [bind_ok] at h
    obtain ⟨vZ, F5, c5, h5, h⟩ := h
    rw [shown_ok] at h5
    obtain ⟨vZ', hvZ, e5⟩ := h5
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e5
    rw [bind_ok] at h
    obtain ⟨y, F6, c6, h6, h⟩ := h
    rw [pure_ok] at h6
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using h6
    rw [bind_ok] at h
    obtain ⟨⟨row, p3⟩, F7, c7, h7, h⟩ := h
    obtain ⟨-, -, -, -, rfl, hG, rfl, rfl⟩ := pscRow_ok _ _ _ _ _ _ _ _ _ h7
    rw [pure_ok] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using h
    exact ⟨target, mu, eps, sent, beta, v, _, vP, vG, _, hpp, Evs.append hev1 hev2, hs, hv, hG1,
        hvP, hvG,
      ⟨vZ, hvZ, rfl⟩, hG, rfl⟩
  · simp only [if_neg hj] at h hpp hv hG1 hvP hvG hev2 ⊢
    rw [bind_ok] at h
    obtain ⟨y, F6, c6, h6, h⟩ := h
    rw [pure_ok] at h6
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using h6
    rw [bind_ok] at h
    obtain ⟨⟨row, p3⟩, F7, c7, h7, h⟩ := h
    obtain ⟨-, -, -, -, rfl, hG, rfl, rfl⟩ := pscRow_ok _ _ _ _ _ _ _ _ _ h7
    rw [pure_ok] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using h
    exact ⟨target, mu, eps, sent, beta, v, _, vP, vG, _, hpp, Evs.append hev1 hev2, hs, hv, hG1,
        hvP, hvG,
      rfl, hG, rfl⟩

/-- The tie: its 31 steps, then the point that joins the planes' roots. -/
theorem tie_ok (a : E) (F G : Fork) (c c' : Tape) (T : Forest.Tie) (h : lkTie a F c = .ok ((T,
    G), c')) :
    ∃ s c1 pt, ((List.range 31).foldlM (lkTieStep a) {}) F c = .ok ((s, G), c1) ∧
      Evs [.point .lkpPlanes 5 pt] c1 c' ∧
      T = { rows := s.rows, sZ := s.sZ, rhoT := pt.reverse, cT := tieCT (s.sG.push s.sP) (eqTab
          pt.reverse) } := by
  unfold lkTie at h
  rw [bind_ok] at h
  obtain ⟨s, F1, c1, h1, h⟩ := h
  rw [bind_ok] at h
  obtain ⟨pt, F2, c2, h2, h⟩ := h
  obtain ⟨hev, rfl⟩ := (point_ok _ _ _ _ _ _ _).1 h2
  rw [pure_ok] at h
  obtain ⟨e1, rfl⟩ := Prod.mk.inj h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e1
  refine ⟨s, c1, pt, h1, hev, ?_⟩
  unfold tieCT
  rfl


end Fo.Tp
