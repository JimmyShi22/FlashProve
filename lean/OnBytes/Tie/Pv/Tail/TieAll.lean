-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Tail/TieAll.lean: the round of the matrix of a smallness test in the one definition
of "a typed round is the round of a plan's entry" that serves all kinds of round.

OnBytes/Tie/Pv/Tail/Rng.lean has a definition for the round RNG alone (RngIs).
OnBytes/G4/RoundIsAll.lean has one for all kinds of round (EntryIsAll, ShapeIsAll): bytes, roots,
field elements, positions and matrix entries. Here the first gives the second, so the list of
rounds of OnBytes/Tie/Pv/Tail/Tie.lean reads in the second. Statements and proofs.

Main names:
  `rngIs_toAll`: a round that is the round RNG of an entry is the round of that entry in the wide
    definition, over any two fields.
  `rounds_areAll`: whatever plan the planner's finish makes of planSmall x 0: the one round that
    draws from D has the shape of that plan's entries (ShapeIsAll, at the library's two fields).
  `round_atAll`: the same from an idle state of a plan in writing.

Limits: as in the two files named; the shape is the one before proof of work is added. Of entries
the wide definition is the wider one: it does not read the number of answers, and a round of 4 ^ n
values also passes at an entry that draws positions in place of some matrix entries, which RngIs
refuses. In the two theorems on plans the entries are the planner's own, so nothing is lost there.
Nothing on soundness.
-/
import OnBytes.Tie.Pv.Tail.Tie
import OnBytes.G4.RoundIsAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail

open Iop OnBytes.Params OnBytes.G4

/-- The narrow definition gives the wide one. -/
theorem rngIs_toAll (E F : Type) [Zero E] {r : Round} {e : Fmt.Entry} (h : RngIs r e) :
    EntryIsAll E F r e := by
  obtain ⟨⟨fP⟩, ⟨fC⟩, hO, h1, h2, _, h4, h5, h6⟩ := h
  refine ⟨⟨0, 0, ⟨fP.trans ((Equiv.ofUnique Unit (Fin 0 → F)).trans
    (Equiv.uniqueProd (Fin 0 → F) (Fin 0 → E)).symm)⟩, by rw [h1, h2]⟩, by rw [h4, h5], ?_,
    ⟨fun _ => h2, fun _ => hO⟩⟩
  rw [h4, h5, h6, Nat.sub_self]
  unfold DrawSet
  exact ⟨fC.trans ((Equiv.uniqueProd _ _).symm.trans
    ((Equiv.prodCongr (Equiv.refl _) (Equiv.uniqueProd _ _).symm).trans
      (Equiv.prodCongr (Equiv.refl _)
        (Equiv.prodCongr (Equiv.refl _) (Equiv.uniqueProd _ _).symm))))⟩

/-- The list of rounds, in the wide definition. -/
theorem rounds_areAll (D : Type) [Fintype D] [Nonempty D] (x : SmallSize)
    (hD : Nonempty (D ≃ (Fin (x.columns * x.tau) → Prob.Coef))) (st : Setting) (P : Planned)
    (h : finish st .request (planSmall x 0) = .ok P) :
    ShapeIsAll Cb.Gl.E Cb.Gl.F [IOR.drawRound D] (P.rounds.map (·.entry)) :=
  (rounds_are D x hD st P h).imp fun _ _ hr => rngIs_toAll Cb.Gl.E Cb.Gl.F hr

/-- The round, in the wide definition, from an idle state of a plan in writing. -/
theorem round_atAll (D : Type) [Fintype D] [Nonempty D] (x : SmallSize)
    (hD : Nonempty (D ≃ (Fin (x.columns * x.tau) → Prob.Coef))) (st : Setting)
    (p q : PlanState) (hp : Idle st p) (h : planSmall x 0 p = .ok ((), q)) :
    Idle st q ∧ q.rounds = p.rounds.push (rngRound st x) ∧
      EntryIsAll Cb.Gl.E Cb.Gl.F (IOR.drawRound D) (rngRound st x).entry := by
  obtain ⟨a, r, i, _⟩ := round_at D x hD st p q hp h
  exact ⟨a, r, rngIs_toAll Cb.Gl.E Cb.Gl.F i⟩

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.rngIs_toAll
#print axioms OnBytes.Tie.Pv.Tail.rounds_areAll
#print axioms OnBytes.Tie.Pv.Tail.round_atAll
