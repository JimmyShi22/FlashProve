-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/FlPort/PscWhole.lean: a carried copy, made by a program, not typed by hand.

Of which file: OnBytes/Tie/Pv/Psc/PscWhole.lean, as it lies in this library.
What is carried: those of its declarations that depend on a context of the verifier program's
channel, and no other:
  ran_roundIn2, ran_roundIn, ran_ends
How: by one swap of names throughout: a context becomes a tape; a routine
of the program becomes the library's flat function of the same text (OnBytes/K/Kc/Flat.lean,
OnBytes/K/Kc/FlatHear.lean). The laws on "returns" are those of Johnson/Top/H/FlPort/Kit.lean. Every
other name is the library's own: plain records, pure functions and lemmas on them, used from where
they lie. Those of OnBytes/Tie/Pv/ that the text names, as far as a program sees them:
  ran_push, took, weight_eq, weight_eq2
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
import OnBytes.Tie.Pv.Psc.PscWhole
import Johnson.Top.H.FlPort.Kit
import Johnson.Top.H.FlPort.PscRun

set_option autoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open OnBytes.PscRun
open OnBytes OnBytes.Model OnBytes.PscTie TwV

/-- A round of the form eq2. -/
theorem ran_roundIn2 {p : Psc} {first : Nat} {mu eps : E} {zd : List (E × Nat)}
    {rs : List (List E × E)} (hp : Ran p first mu eps zd rs) (z : E) (degree : Nat) (F G : Fork)
    (c c' : Tape) (g : E) (p' : Psc) (h : Fl.roundIn .eq2 p z degree F c = .ok (((g, p'), G), c')) :
    ∃ sent : Array E, sent.size = 2 ∧ Evs [.read 2 sent, .ans .pscRound g] c c' ∧ G = took F 2 ∧
      p'.target = p.target ∧ p'.start = p.start ∧ p'.started = p.started ∧
      p'.rowMade = p.rowMade ∧ p'.ended = false ∧
      Ran p' first mu eps (zd ++ [(z, 3)]) (rs ++ [(sent.toList, g)]) := by
  obtain ⟨w, sent, he, hw, -, hs, hev, rfl, rfl⟩ := roundIn_ok _ _ _ _ _ _ _ _ _ _ h
  obtain rfl : OnBytes.Psc.Weight.equality z 3 = w :=
    Option.some.inj ((weight_eq2 z degree).symm.trans hw)
  have hs' : sent.size + 1 = 3 := hs
  refine ⟨sent, by omega, hev, rfl, rfl, rfl, rfl, rfl, he, ?_⟩
  exact ran_push hp z 3 sent g hs' _ rfl rfl rfl rfl rfl rfl

/-- A round of the form eq, of a degree that the caller gives. -/
theorem ran_roundIn {p : Psc} {first : Nat} {mu eps : E} {zd : List (E × Nat)}
    {rs : List (List E × E)} (hp : Ran p first mu eps zd rs) (z : E) (degree : Nat) (F G : Fork)
    (c c' : Tape) (g : E) (p' : Psc) (h : Fl.roundIn .eq p z degree F c = .ok (((g, p'), G), c')) :
    ∃ sent : Array E, sent.size = degree ∧ Evs [.read degree sent, .ans .pscRound g] c c' ∧
      G = took F degree ∧ p'.target = p.target ∧ p'.start = p.start ∧ p'.started = p.started ∧
      p'.rowMade = p.rowMade ∧ p'.ended = false ∧
      Ran p' first mu eps (zd ++ [(z, degree + 1)]) (rs ++ [(sent.toList, g)]) := by
  obtain ⟨w, sent, he, hw, -, hs, hev, rfl, rfl⟩ := roundIn_ok _ _ _ _ _ _ _ _ _ _ h
  obtain rfl := weight_eq z degree w hw
  have hs' : sent.size + 1 = degree + 1 := hs
  refine ⟨sent, by omega, hev, rfl, rfl, rfl, rfl, rfl, he, ?_⟩
  exact ran_push hp z (degree + 1) sent g hs' _ rfl rfl rfl rfl rfl rfl

/-- The round in Y and the round of the end values. Y's pair has the coordinate `zeroE`, which every
reading takes to 0. -/
theorem ran_ends {p : Psc} {first : Nat} {mu eps : E} {zd : List (E × Nat)}
    {rs : List (List E × E)} (hp : Ran p first mu eps zd rs) (degreeInY n : Nat) (F G : Fork)
    (c c' : Tape) (e : Nat) (p' : Psc) (h : Fl.pscEnds p degreeInY n F c = .ok (((e, p'), G), c')) :
    ∃ (sent : Array E) (beta : E) (v : Array E), sent.size = degreeInY ∧ v.size = n ∧
      Evs [.read degreeInY sent, .ansNZ .pscY beta, .read n v, .empty .pscValues] c c' ∧
      e = F.next + degreeInY ∧ (took F (degreeInY + n)).hideRun e v beta = some G ∧
      p'.target = p.target ∧ p'.start = p.start ∧ p'.started = p.started ∧
      p'.rowMade = p.rowMade ∧ p'.ended = true ∧
      Ran p' first mu eps (zd ++ [(zeroE, degreeInY + 1)]) (rs ++ [(sent.toList, beta)]) := by
  obtain ⟨sent, beta, v, -, -, -, hs, hv, hev, he, hG, rfl⟩ := pscEnds_ok _ _ _ _ _ _ _ _ _ h
  refine ⟨sent, beta, v, hs, hv, hev, he, hG, rfl, rfl, rfl, rfl, rfl, ?_⟩
  exact ran_push hp zeroE (degreeInY + 1) sent beta (by omega) _ rfl rfl rfl rfl rfl rfl

section Read
variable {K : Type} [CommRing K] (ρ : Reading K)

end Read


end Fo.Tp
