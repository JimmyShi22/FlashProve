-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/TreesKOfRounds.lean: THE CORE `TreesK`, AT NAMED VALUES, FROM FOUR TESTS A
CHAIN, which are closed once m's sendings and plans are pinned. General in m. Calls alone. Nothing
is evaluated.

`TreesK` (Core.lean) asks that `treesSent` (Johnson/G/RoundsOfPlan.lean) return at the key file's
three chains, at every words for a refusal. The law `treesSent_at`
(Johnson/Unfolds/TreesAt.lean) gives `treesSent`'s value at every such words from: the
offset; the `mapM` of `sentAt` returns at the empty words; the sorted trees' rounds are a list rs;
two tests on rs. Which list rs is, `sortedW_rounds` says (RoundsOfSent.lean). Here the two are
joined.

  `treesOf c off e`: the value: the chain's trees, sorted by rounds and numbered.
  `ChainFits c P e off`: the four tests: `offset`, an equation of numbers; `sent`: `sentAt`
    returns at every sending (it refuses at a label that `sendTag` does not know, and where
    `layTrees` lays no trees), as a Bool; `roots` and `below`: Bools on a list of numbers.
  `treesSent_of_fits`: `treesSent`'s value at every words. `treesK_of_fits`: `TreesK` at named
    values.
Limits. THAT `ChainFits` HOLDS AT ANY CHAIN IS NOT SHOWN HERE. `treesOf` is a term, not a written
list: its trees' tags and classes are what `sentAt` gives.
Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.RoundsOfSent
import Johnson.Unfolds.TreesAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open OnBytes OnBytes.Params
open Johnson.G (ChainSends Sending)
open Johnson.G.OfPlan
open Johnson.Unfolds (sortedW sentsOf rootsC treesSent_at ok_of_isOk)

/-- A chain's trees, as `treesSent` returns them: sorted by rounds and numbered. -/
abbrev treesOf (c : ChainSends) (off : Nat) (e : List Sent) : List (Sent × Nat) :=
  (sortedW (sentsOf c off) e).zipIdx

/-- What is asked of one chain: the offset; `sentAt` returns at every sending; at every round as
many trees as the entry has roots; every tree's round below the number of rounds. -/
structure ChainFits (c : ChainSends) (P : Fmt.Plan) (e : List Sent) (off : Nat) : Prop where
  offset : P.entries.length - P.rounds.length = off
  sent : (c.sends.mapM (sentAt "" c.codes off)).isOk = true
  roots : rootsC P.rounds (roundsOfChain c off e) = true
  below : ((roundsOfChain c off e).all fun r => decide (r < P.rounds.length)) = true

/-- **`treesSent`'s value at every name, from `ChainFits`.** -/
theorem treesSent_of_fits {c : ChainSends} {P : Fmt.Plan} {e : List Sent} {off : Nat}
    (h : ChainFits c P e off) (a : String) : treesSent a c P e = .ok (treesOf c off e) :=
  treesSent_at rfl h.offset h.sent (sortedW_rounds e (ok_of_isOk [] h.sent)) h.roots rfl h.below a

/-- **The core, at named values.** -/
theorem treesK_of_fits (m : Made) (o₀ o₁ o₂ : Nat) (h₀ : ChainFits m.key.1 (plan₀ m) [] o₀)
    (h₁ : ChainFits m.key.2.1 (plan₁ m) (ownMasks m.key.2.1.codes (shapeK m) (plan₁ m).rounds) o₁)
    (h₂ : ChainFits m.key.2.2 (plan₂ m) [] o₂) :
    TreesK m (treesOf m.key.1 o₀ [])
      (treesOf m.key.2.1 o₁ (ownMasks m.key.2.1.codes (shapeK m) (plan₁ m).rounds))
      (treesOf m.key.2.2 o₂ []) :=
  ⟨treesSent_of_fits h₀, treesSent_of_fits h₁, treesSent_of_fits h₂⟩

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.treesSent_of_fits
#print axioms Johnson.AtFull.KeyBack.treesK_of_fits
