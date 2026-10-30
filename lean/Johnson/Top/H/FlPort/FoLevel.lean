-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/FlPort/FoLevel.lean: a carried copy, made by a program, not typed by hand.

Of which file: OnBytes/Tie/Pv/Lookup/Forest/FoLevel.lean, as it lies in this library.
What is carried: those of its declarations that depend on a context of the verifier program's
channel, and no other:
  LevelLaw
How: by one swap of names throughout: a context becomes a tape; a routine
of the program becomes the library's flat function of the same text (OnBytes/K/Kc/Flat.lean,
OnBytes/K/Kc/FlatHear.lean). The laws on "returns" are those of Johnson/Top/H/FlPort/Kit.lean. Every
other name is the library's own: plain records, pure functions and lemmas on them, used from where
they lie. Those of OnBytes/Tie/Pv/ that the text names, as far as a program sees them:
  Closed, Filled, FormIs, Later, LedAt, RowIs, Same, Sized, flEv, took
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
import OnBytes.Tie.Pv.Lookup.Forest.FoLevel
import Johnson.Top.H.FlPort.Kit
import Johnson.Top.H.FlPort.PscWhole
import Johnson.Top.H.FlPort.PscRun
import Johnson.Top.H.FlPort.FoRds
import Johnson.Top.H.FlPort.FoHeard
import Johnson.Top.H.FlPort.FoLevelRun

set_option autoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open TwV OnBytes OnBytes.Model OnBytes.PscRun OnBytes.PscTie

/-- One level. -/
def LevelLaw {K : Type} [CommRing K] (ρ : Reading K) : Prop :=
  ∀ (s s' : Forest.Descent) (mu : ℕ) (order : List ℕ) (F G : Fork) (c c' : Tape) (pt : List K)
    (tg : K) (inc : List (Pl × K)) (L : Led Pl),
    lkLevel s mu order F c = .ok ((s', G), c') →
    order.Perm (List.range mu) → Sized F → pt.length = mu → rdA ρ s.rho = pt.reverse →
    FormIs ρ F s.form tg inc → LedAt L F.next (List.replicate mu 2 ++ [2]) 2 →
    ∃ (l : List Ev) (sc : Sc K) (τ : K) (row : Aff),
      Evs l c c' ∧ Rds l ∧ Closed ρ l ∧ Later F G ∧ Sized G ∧
      Same (took F (1 + 2 * mu + 4)) G ∧
      (∀ j, Filled G j ↔ Filled F j ∨ (F.next ≤ j ∧ j < F.next + (1 + 2 * mu + 4))) ∧
      (∀ j, (j < F.next ∨ F.next + (1 + 2 * mu + 4) ≤ j) →
        G.vp.getD j zeroE = F.vp.getD j zeroE ∧ G.mf.getD j zeroE = F.mf.getD j zeroE) ∧
      (∀ rest, takeSc (flEv ρ l ++ rest) tg (inRounds order pt ++ [0]) true =
        (sc, ([], [τ]) :: rest)) ∧
      s'.rows = s.rows.push row ∧
      RowIs ρ G row (rowU L (List.replicate mu 2 ++ [2]) sc inc (sc.v 0 * sc.v 1)) ∧
      rdA ρ s'.rho = (byVar order sc.xs ++ [τ]).reverse ∧
      FormIs ρ G s'.form (lineTg sc τ) (lineForm L sc τ)


end Fo.Tp
