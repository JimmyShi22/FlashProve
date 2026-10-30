-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoTieRun.lean.
The tie of a sub-proof's lookup, as the byte-level verifier runs it (Forest.tieStep, Forest.tie,
OnBytes/Model/Look.lean): what a run that returns has read, drawn and left.

The theorems have the form of OnBytes.PscRun's: if the run returns, then it was made of these calls
of the channel's own routines, with these results, and the value and the state that it leaves are
these.

States:
  tiePsc: the record of a sumcheck without a variable after its round in the further variable.
  tieStep_ok: one step of the tie: a sum, a draw, three scalars, a draw by the routine
    trAnswerNotZero (that the element drawn is not 0 is not said here), the end
    values (three in step 0, two in a later step), a round without a draw;
    the end values are put under the slots behind the sumcheck's four; the summand is Z - a P^2 G in
      step 0 and P^2 G later, on the values shown; the step's claim is Psc.rowForm at that summand.
  tieCT, tie_ok: the tie is its 31 steps, then one round in which five elements are drawn; the point
    is these reversed; the form that joins the planes' roots reads the slots of the 31 roots and of
    the last power.
Limits: nothing is said where a routine fails.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoEv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

/-- A sumcheck without a variable, after its round in the further variable, in which three scalars
are sent. -/
def tiePsc (C : Aff) (target mu eps beta : E) (first : Nat) (sent : Array E) : Psc :=
  { start := C, started := true, target := target, first := first, eps := eps,
    claim := OnBytes.Psc.polyAt ((OnBytes.Psc.Weight.atZero (3 + 1)).complete sent.toList (addE mu
        (mulE eps target))) beta,
    vars := (#[] : Array OnBytes.Psc.Weight).push (OnBytes.Psc.Weight.atZero (3 + 1)), r := (#[] :
        Array E).push beta,
    ended := true }

/-- One step of the tie. -/
theorem tieStep_ok (a : E) (s : Forest.TieStep) (j : Nat) (F G : Fork) (c c' : Ctx) (s' :
    Forest.TieStep)
    (h : Forest.tieStep a s j F c = .ok ((s', G), c')) :
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
  unfold Forest.tieStep at h
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

/-- The form that joins the planes' roots. -/
def tieCT (sG : Array Nat) (ej : Array E) : Aff :=
  (List.range 32).foldl (fun (f : Aff) j => Aff.addMul f (Aff.slot (sG.getD j 0)) (ej.getD j zeroE))
      (Aff.ofConst zeroE)

/-- The tie: its 31 steps, then the point that joins the planes' roots. -/
theorem tie_ok (a : E) (F G : Fork) (c c' : Ctx) (T : Forest.Tie) (h : Forest.tie a F c = .ok ((T,
    G), c')) :
    ∃ s c1 pt, ((List.range 31).foldlM (Forest.tieStep a) {}) F c = .ok ((s, G), c1) ∧
      Evs [.point .lkpPlanes 5 pt] c1 c' ∧
      T = { rows := s.rows, sZ := s.sZ, rhoT := pt.reverse, cT := tieCT (s.sG.push s.sP) (eqTab
          pt.reverse) } := by
  unfold Forest.tie at h
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

end Fo
