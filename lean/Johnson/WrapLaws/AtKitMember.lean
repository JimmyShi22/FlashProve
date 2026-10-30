-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/WrapLaws/AtKitMember.lean: the bound on the reduction's game (gameAtW,
Johnson/WrapLaws/AtKit.lean) at a small member of its premises. One statement with its proof. A toy:
nothing here is about the protocol of the release. This file states no goal of the release.

At the letters of Johnson/WholeKey/Member2.lean (three indices, two of them in range; each protocol
with a real round; a test with a cap; a shared round; two copies, two sessions each) all premises of
gameAtW hold together, and its bound is 0: against the reduction's kit, bounds, honest sides and
simulators, the real game on either index IN RANGE and the simulated game at ANY fixed index, the
one out of range too, show an adversary THE SAME, whatever the number of its calls for a session.

  game_pad2   (namespace OnBytes.WrapLaws) the two laws are equal.

Limits. The game refuses beyond its bounds by itself, alike on both sides. Where a search of the dry
pass runs out nothing of a run is shown on either side; how often that is, is not said here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.WrapLaws.AtKit
import Johnson.WholeKey.Member2

set_option autoImplicit false

noncomputable section

namespace OnBytes.WrapLaws
open TypedOracleCompiler.Compile.Batch Rom Prob OnBytes.WholeKey OnBytes.WholeKey.Member2 Hiop.Seeded
open Hiop.Seeded.Two (pad2)
open scoped ENNReal

theorem game_pad2 (r₀ : pad2.Rec) (Ryes : Option Bool → Unit → Prop) (i : Option Bool) (hi : ok2 i)
    (i₀ : Option Bool) (n : ℕ) (α : Type)
    (E : Adv (typedOracleFamily 32 W2.K C2) (GOut pad2 (kitW W2 r₀ at2.side).form)
      (GIn pad2 (kitW W2 r₀ at2.side).form) α)
    (hE : E.CallsOK (okCall (Ryes i))) (hn : SessLe E n) :
    (interact (gameReal pad2 (kitW W2 r₀ at2.side) (recsG at2) i (boundsW at2.side nu2.s1)
        (fun _ => True) _) E (none, Table.empty _)).map Prod.fst =
      (interact (gameSim pad2 (kitW W2 r₀ at2.side) (simsG at2.side sm2) i₀
        (boundsW at2.side nu2.s1) (fun _ => True) _) E (none, Table.empty _)).map Prod.fst := by
  have h := gameAtW (Option Bool) Unit 32 pad2 Bool aT aL W2 S2 cA2 r₀ p2 at2 sm2 ok2
    (fun _ => True) Ryes cn2 nu2 (premW_pad2 Ryes) i hi i₀ n α E hE hn
  have h0 : ((nu2.zT + ((at2.M + 1 : ℕ) : ℝ≥0∞) * nu2.zL + (n : ℝ≥0∞) * nu2.zO) +
      (nu2.hT + ((at2.M + 1 : ℕ) : ℝ≥0∞) * nu2.hL + (n : ℝ≥0∞) * nu2.hO)) = 0 := by
    show ((0 : ℝ≥0∞) + ((1 + 1 : ℕ) : ℝ≥0∞) * 0 + (n : ℝ≥0∞) * 0) +
      (0 + ((1 + 1 : ℕ) : ℝ≥0∞) * 0 + (n : ℝ≥0∞) * 0) = 0
    simp
  rw [h0] at h
  exact tv_eq_zero_iff.1 (le_antisymm h (zero_le _))

end OnBytes.WrapLaws

#print axioms OnBytes.WrapLaws.game_pad2
