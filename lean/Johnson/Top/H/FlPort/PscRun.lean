-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/FlPort/PscRun.lean: a carried copy, made by a program, not typed by hand.

Of which file: OnBytes/Tie/Pv/Psc/PscRun.lean, as it lies in this library.
What is carried: those of its declarations that depend on a context of the verifier program's
channel, and no other:
  pscBeginAt_ok, pscBegin_ok, pscRound_ok, roundIn_ok, pscEnds_ok, pscRow_ok
How: by one swap of names throughout: a context becomes a tape; a routine
of the program becomes the library's flat function of the same text (OnBytes/K/Kc/Flat.lean,
OnBytes/K/Kc/FlatHear.lean). The laws on "returns" are those of Johnson/Top/H/FlPort/Kit.lean. Every
other name is the library's own: plain records, pure functions and lemmas on them, used from where
they lie. Those of OnBytes/Tie/Pv/ that the text names, as far as a program sees them:
  took
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
import OnBytes.Tie.Pv.Psc.PscRun
import Johnson.Top.H.FlPort.Kit


set_option autoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open OnBytes.PscRun
open OnBytes OnBytes.Model

section Ways
variable {α β : Type}

end Ways

/-- The beginning: one slot is taken; the sum is received; eps is drawn. -/
theorem pscBeginAt_ok (target : E) (F G : Fork) (c c' : Tape) (p : Psc)
    (h : Fl.pscBeginAt target F c = .ok ((p, G), c')) :
    ∃ mu eps, Evs [.sum mu, .ans .pscEpsilon eps] c c' ∧ G = took F 1 ∧
      p = { target := target, first := F.next, eps := eps,
            claim := addE mu (mulE eps target) } := by
  unfold Fl.pscBeginAt at h
  rw [bind_ok] at h
  obtain ⟨first, F1, c1, h1, h⟩ := h
  rw [takeSlots_ok] at h1
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ : (first = F.next ∧ F1 = took F 1) ∧ c1 = c := by
    simpa [Prod.ext_iff] using h1
  rw [bind_ok] at h
  obtain ⟨mu, F2, c2, h2, h⟩ := h
  unfold Fl.readSum at h2
  rw [lift_ok] at h2
  obtain ⟨mu', c2', h2, e2⟩ := h2
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ : (mu = mu' ∧ F2 = took F 1) ∧ c2 = c2' := by
    simpa [Prod.ext_iff] using e2
  rw [bind_ok] at h
  obtain ⟨eps, F3, c3, h3, h⟩ := h
  unfold Fl.answer at h3
  rw [lift_ok] at h3
  obtain ⟨eps', c3', h3, e3⟩ := h3
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ : (eps = eps' ∧ F3 = took F 1) ∧ c3 = c3' := by
    simpa [Prod.ext_iff] using e3
  rw [pure_ok] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using h
  exact ⟨mu, eps, ⟨_, h2, _, h3, rfl⟩, rfl, rfl⟩

/-- The beginning, from the form C of the sum: the target is C's public part at the state before. -/
theorem pscBegin_ok (C : Aff) (F G : Fork) (c c' : Tape) (p : Psc)
    (h : Fl.pscBegin C F c = .ok ((p, G), c')) :
    ∃ target mu eps, F.publicPart C = some target ∧ Evs [.sum mu, .ans .pscEpsilon eps] c c' ∧
      G = took F 1 ∧
      p = { start := C, started := true, target := target, first := F.next, eps := eps,
            claim := addE mu (mulE eps target) } := by
  unfold Fl.pscBegin at h
  rw [bind_ok] at h
  obtain ⟨target, F1, c1, h1, h⟩ := h
  unfold Fl.publicPart at h1
  rw [ask_ok] at h1
  obtain ⟨t', ht, e1⟩ := h1
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e1
  rw [bind_ok] at h
  obtain ⟨p0, F2, c2, h2, h⟩ := h
  obtain ⟨mu, eps, hev, rfl, rfl⟩ := pscBeginAt_ok _ _ _ _ _ _ h2
  rw [pure_ok] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using h
  exact ⟨_, mu, eps, ht, hev, rfl, rfl⟩

/-- One round: d - 1 elements are received, the challenge is drawn, d - 1 slots are taken. -/
theorem pscRound_ok (p : Psc) (w : OnBytes.Psc.Weight) (draw : Tape → Option (E × Tape))
    (F G : Fork) (c c' : Tape) (r : E) (p' : Psc)
    (h : Fl.pscRound p w draw F c = .ok (((r, p'), G), c')) :
    ∃ sent c1, (w.fits && weightHeld w) = true ∧ recvN (w.d - 1) c = some (sent, c1) ∧
      sent.size + 1 = w.d ∧ draw c1 = some (r, c') ∧ G = took F (w.d - 1) ∧
      p' = { p with claim := OnBytes.Psc.polyAt (w.complete sent.toList p.claim) r,
                    vars := p.vars.push w, r := p.r.push r } := by
  unfold Fl.pscRound at h
  rw [bind_ok] at h
  obtain ⟨_, F1, c1, h1, h⟩ := h
  rw [must_ok] at h1
  obtain ⟨hw, e1⟩ := h1
  obtain ⟨⟨-, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e1
  rw [bind_ok] at h
  obtain ⟨sent, F2, c2, h2, h⟩ := h
  unfold Fl.read at h2
  rw [lift_ok] at h2
  obtain ⟨sent', c2', h2, e2⟩ := h2
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e2
  rw [bind_ok] at h
  obtain ⟨_, F3, c3, h3, h⟩ := h
  rw [must_ok] at h3
  obtain ⟨hs, e3⟩ := h3
  obtain ⟨⟨-, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e3
  rw [bind_ok] at h
  obtain ⟨r0, F4, c4, h4, h⟩ := h
  rw [lift_ok] at h4
  obtain ⟨r0', c4', h4, e4⟩ := h4
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e4
  rw [bind_ok] at h
  obtain ⟨_, F5, c5, h5, h⟩ := h
  rw [takeSlots_ok] at h5
  obtain ⟨⟨-, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using h5
  rw [pure_ok] at h
  obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using h
  exact ⟨_, _, hw, h2, by simpa using hs, h4, rfl, rfl⟩

/-- One round of a given form. -/
theorem roundIn_ok (form : RoundForm) (p : Psc) (z : E) (degree : Nat) (F G : Fork) (c c' : Tape)
    (r : E) (p' : Psc) (h : Fl.roundIn form p z degree F c = .ok (((r, p'), G), c')) :
    ∃ w sent, p.ended = false ∧ form.weight z degree = some w ∧
      (w.fits && weightHeld w) = true ∧ sent.size + 1 = w.d ∧
      Evs [.read (w.d - 1) sent, .ans .pscRound r] c c' ∧ G = took F (w.d - 1) ∧
      p' = { p with claim := OnBytes.Psc.polyAt (w.complete sent.toList p.claim) r,
                    vars := p.vars.push w, r := p.r.push r } := by
  unfold Fl.roundIn at h
  rw [bind_ok] at h
  obtain ⟨_, F1, c1, h1, h⟩ := h
  rw [must_ok] at h1
  obtain ⟨he, e1⟩ := h1
  obtain ⟨⟨-, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e1
  rw [bind_ok] at h
  obtain ⟨w, F2, c2, h2, h⟩ := h
  rw [get_ok] at h2
  obtain ⟨w', hw, e2⟩ := h2
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e2
  obtain ⟨sent, c3, hf, hr, hs, hd, rfl, rfl⟩ := pscRound_ok _ _ _ _ _ _ _ _ _ h
  exact ⟨_, sent, by simpa using he, hw, hf, hs, ⟨_, hr, _, hd, rfl⟩, rfl, rfl⟩

/-- The round in the further variable Y, and the round of the n end values: degreeInY elements are
received, beta is drawn by the rule that never gives 0, degreeInY slots are taken; n elements are
received and their round is closed; n slots are taken, from e on, and the n elements are put under
them with the factor beta. -/
theorem pscEnds_ok (p : Psc) (degreeInY n : Nat) (F G : Fork) (c c' : Tape) (e : Nat) (p' : Psc)
    (h : Fl.pscEnds p degreeInY n F c = .ok (((e, p'), G), c')) :
    ∃ sent beta v, p.ended = false ∧ 1 ≤ degreeInY ∧ 1 ≤ n ∧ sent.size = degreeInY ∧ v.size = n ∧
      Evs [.read degreeInY sent, .ansNZ .pscY beta, .read n v, .empty .pscValues] c c' ∧
      e = F.next + degreeInY ∧
      (took F (degreeInY + n)).hideRun e v beta = some G ∧
      p' = { p with
        claim := OnBytes.Psc.polyAt
          ((OnBytes.Psc.Weight.atZero (degreeInY + 1)).complete sent.toList p.claim) beta,
        vars := p.vars.push (OnBytes.Psc.Weight.atZero (degreeInY + 1)), r := p.r.push beta,
        ended := true } := by
  unfold Fl.pscEnds at h
  rw [bind_ok] at h
  obtain ⟨_, F1, c1, h1, h⟩ := h
  rw [must_ok] at h1
  obtain ⟨hm, e1⟩ := h1
  obtain ⟨⟨-, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e1
  rw [bind_ok] at h
  obtain ⟨⟨beta, p1⟩, F2, c2, h2, h⟩ := h
  obtain ⟨sent, c3, -, hr, hs, hd, rfl, rfl⟩ := pscRound_ok _ _ _ _ _ _ _ _ _ h2
  simp only [] at h
  rw [bind_ok] at h
  obtain ⟨v, F3, c4, h3, h⟩ := h
  unfold Fl.read at h3
  rw [lift_ok] at h3
  obtain ⟨v', c4', h3, e3⟩ := h3
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e3
  rw [bind_ok] at h
  obtain ⟨_, F4, c5, h4, h⟩ := h
  rw [must_ok] at h4
  obtain ⟨hv, e4⟩ := h4
  obtain ⟨⟨-, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e4
  rw [bind_ok] at h
  obtain ⟨_, F5, c6, h5, h⟩ := h
  unfold Fl.empty at h5
  rw [lift_ok] at h5
  obtain ⟨_, c6', h5, e5⟩ := h5
  obtain ⟨⟨-, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e5
  rw [bind_ok] at h
  obtain ⟨e0, F6, c7, h6, h⟩ := h
  rw [takeSlots_ok] at h6
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using h6
  rw [bind_ok] at h
  obtain ⟨_, F7, c8, h7, h⟩ := h
  rw [change_ok] at h7
  obtain ⟨G', hG, e7⟩ := h7
  obtain ⟨⟨-, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e7
  rw [pure_ok] at h
  obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using h
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hm
  have hd1 : (OnBytes.Psc.Weight.atZero (degreeInY + 1)).d - 1 = degreeInY := rfl
  rw [hd1] at hr
  refine ⟨sent, beta, v, hm.1.1, hm.1.2, hm.2, ?_, by simpa using hv,
    ⟨_, hr, _, hd, _, h3, _, h5, rfl⟩, rfl, ?_, rfl⟩
  · have : sent.size + 1 = degreeInY + 1 := hs
    omega
  · have ht : took (took F ((OnBytes.Psc.Weight.atZero (degreeInY + 1)).d - 1)) n =
        took F (degreeInY + n) := by
      simp only [took, hd1, Nat.add_assoc]
    rw [← ht]
    exact hG

/-- The claim that a sumcheck leaves: nothing is received or drawn; the coefficients of the hiding
polynomial are put under the slots from p.first on: 0 shown, the factor -1. -/
theorem pscRow_ok (p : Psc) (S0 : E) (kept : Aff) (F G : Fork) (c c' : Tape) (row : Aff) (p' : Psc)
    (h : Fl.pscRow p S0 kept F c = .ok (((row, p'), G), c')) :
    p.rowMade = false ∧ p.started = true ∧ p.vars.isEmpty = false ∧ p.r.size = p.vars.size ∧
      c' = c ∧
      F.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE) = some G ∧
      row = p.rowForm S0 kept ∧ p' = { p with rowMade := true } := by
  unfold Fl.pscRow at h
  rw [bind_ok] at h
  obtain ⟨_, F1, c1, h1, h⟩ := h
  rw [must_ok] at h1
  obtain ⟨hm, e1⟩ := h1
  obtain ⟨⟨-, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e1
  rw [bind_ok] at h
  obtain ⟨_, F2, c2, h2, h⟩ := h
  rw [change_ok] at h2
  obtain ⟨G', hG, e2⟩ := h2
  obtain ⟨⟨-, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e2
  rw [pure_ok] at h
  obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using h
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hm
  exact ⟨hm.1.1.1, hm.1.1.2, hm.1.2, hm.2, rfl, hG, rfl, rfl⟩


end Fo.Tp
