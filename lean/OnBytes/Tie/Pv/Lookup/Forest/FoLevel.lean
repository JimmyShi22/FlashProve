-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoLevel.lean.
One level of a product tree: the byte-level routine's run is the flat function's step.

* `LevelLaw ρ`: the statement, for every reading ρ: if Forest.level returns, from a state of
  the walk whose point reads pt backwards and whose form has the public part tg and, on the mask
  row, the form inc,
  then the channel's calls, read as rounds, are what the flat step takeSc takes, followed by the
  line's round; the claim pushed is the flat function's row; the point and the form handed on are
  the flat function's; the state left is a later one that fits, with the level's 1 + 2 mu + 4 slots
  taken and filled and what lies under every other slot as it was.
  Further premises: the order is a permutation of the mu variables; the state fits (Sized); pt has
  mu coordinates; the places of the level's masks lie from the next free slot on (LedAt).
  The proof is levelLaw (OnBytes/Tie/Pv/Lookup/Forest/FoLevelLaw.lean).

-/
import OnBytes.Tie.Pv.Lookup.Port.FoLevelRun
import OnBytes.Tie.Pv.Lookup.Forest.FoRds
import OnBytes.Tie.Pv.Lookup.Forest.FoLedAt
import OnBytes.Tie.Pv.Psc.PscFork

set_option autoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.PscRun OnBytes.PscTie

/-- One level. -/
def LevelLaw {K : Type} [CommRing K] (ρ : Reading K) : Prop :=
  ∀ (s s' : Forest.Descent) (mu : ℕ) (order : List ℕ) (F G : Fork) (c c' : Ctx) (pt : List K)
    (tg : K) (inc : List (Pl × K)) (L : Led Pl),
    Forest.level s mu order F c = .ok ((s', G), c') →
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

end Fo
