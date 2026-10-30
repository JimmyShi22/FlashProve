-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/TellsNothing.lean: A BLOCK THAT DECLARES NO ROOT TELLS NO TREE; AND K4's BLOCK
DECLARES NONE. Three theorems.
Why. The table's test `k4ToldFit` (Johnson/Desc/First/K4PlanFit.lean) asks that at every place of
K4's the block tells no tree. At the description's own telling (for each block `b.oracles.flatMap
id`) that is a fact on the description: it follows from the block's own test of shape
(`Block.shaped`, a clause of `blocksOk`: as many oracles beneath a round as the round declares
roots) and from what K4's block declares.
  `tells_nothing`: a shaped block all of whose declared rounds have no root tells nothing: by
  `zip_len` (Johnson/Desc/Sound/ToldCount.lean). General: no kind is named.
  `declares_no_root`: a block that declares K4's rounds (`Declares`,
  Johnson/Road/K4/PieceTiled.lean) declares no root.
  `k4_tells_nothing`: so a shaped block that declares K4's rounds tells nothing.
Silly members. A block without a round tells nothing.
Limits. That a description's block at a place of K4's declares K4's rounds, and that it is shaped,
is not said here. No probability: no soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Road.K4.PieceAtCut
import Johnson.Desc.Sound.ToldCount

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat
open OnBytes.Desc.First.K4
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound

variable {T Cl : Type}

/-- **A shaped block all of whose declared rounds have no root tells nothing.** -/
theorem tells_nothing (b : Block T Cl) (hs : b.shaped = true)
    (h0 : ∀ r ∈ b.rounds, r.entry.roots = 0) : b.oracles.flatMap id = [] := by
  unfold Block.shaped at hs
  rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hs
  have e := zip_len b.rounds b.oracles hs.1 fun x hx => by
    have t := hs.2 x hx
    rw [Bool.and_eq_true, beq_iff_eq] at t
    exact t.1
  have z : (b.rounds.map (·.entry.roots)).sum = 0 := by
    refine List.sum_eq_zero fun n hn => ?_
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hn
    exact h0 r hr
  exact List.eq_nil_of_length_eq_zero (e.trans z)

/-- A block that declares K4's rounds declares no root. -/
theorem declares_no_root {b : Block T Cl} {par : Par} (hd : Declares b par) :
    ∀ r ∈ b.rounds, r.entry.roots = 0 := by
  intro r hr
  rw [hd] at hr
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hr
  have he' : e ∈ (rounds par.P par.hp par.g).map entryOf := he
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp he'
  rfl

/-- **A shaped block that declares K4's rounds tells nothing.** -/
theorem k4_tells_nothing {b : Block T Cl} {par : Par} (hs : b.shaped = true)
    (hd : Declares b par) : b.oracles.flatMap id = [] :=
  tells_nothing b hs (declares_no_root hd)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.tells_nothing
#print axioms OnBytes.Road.K4.declares_no_root
#print axioms OnBytes.Road.K4.k4_tells_nothing
