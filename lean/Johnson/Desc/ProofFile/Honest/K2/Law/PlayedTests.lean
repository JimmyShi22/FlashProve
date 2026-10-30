-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/PlayedTests.lean: the kind "the code switch" (K2): THE FRAME's
LAW ON A PLAYED HALF (`fits_played`, Honest/Law/Cut.lean), READ AT A SUB-PROTOCOL THAT HAS THE
KIND's TWO ROUNDS. One statement with its proof; no definition.

  `played_tests`    where a half has played such a sub-protocol's rounds and the columns that it
                    reads are laid: two rounds were played; the challenges are theirs; shown without
                    the digest they pass `roundsFit`; the columns are, in key, position and width,
                    those that are read

Limits. That a half plays and that the columns are laid are premises. General in the half and in the
sub-protocol's decision. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Law.Cut
import Johnson.Top.H0.Tw.K2C.Kind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (roundsFit groupsOf noDigest Block Place OpenedColumn)
open VerifiableInference.Desc.First.K2 (P2 rounds)

variable {S' Cl' V W X : Type}

/-- **The frame's law on a played half, read at the kind's two rounds.** -/
theorem played_tests {g : Placed V W X} {b : Block S' Cl'} {v : Option V} {c : RowCoins g.parts}
    {ds : List Fmt.Drawn} {m : Mid W X} {y : List Played × Mid W X} {chain ft : Nat}
    {stored : Nat → Nat → Option (List UInt64)} {tree : Fmt.TreeSource → Option (Place × Table)}
    {cols : List OpenedColumn} (q : P2) (hb : b.rounds = rounds q)
    (hr : g.rounds = b.rounds.length) (ho : b.oracles.length = b.rounds.length)
    (hy : play (g.steps b v c) ds [] m = .ok y) (hd : drawsFit b.rounds ds = true)
    (hc : fillCols (readsOf chain ft stored tree b.rounds ds) [] = .ok cols) :
    ∃ R₁ R₂ : Fmt.RoundView, roundsOf y.1 = [R₁, R₂] ∧ ds = [R₁.drawn, R₂.drawn] ∧
      roundsFit (rounds q) [noDigest R₁, noDigest R₂] = true ∧
      cols.map (fun z => (z.1, z.2.1, z.2.2.length)) =
        (groupsOf ft (rounds q) [R₁.drawn, R₂.drawn]).flatMap id := by
  obtain ⟨⟨hf1, hf2⟩, hl, -⟩ := fits_played hr ho hy hd hc
  have hdr : (roundsOf y.1).map (·.drawn) = ds :=
    yields_drawn _ _ _ _ (play_yields _ _ _ _ _ hy)
  rw [hl, List.take_length] at hf2
  have hf2' := beq_iff_eq.1 hf2
  unfold Block.want at hf2'
  rw [hb] at hf1 hf2'
  rcases hR : roundsOf y.1 with _ | ⟨R₁, _ | ⟨R₂, _ | ⟨R₃, t⟩⟩⟩
  · rw [hR] at hf1
    simp [rounds, roundsFit] at hf1
  · rw [hR] at hf1
    simp [rounds, roundsFit] at hf1
  · rw [hR] at hf1 hf2' hdr
    exact ⟨R₁, R₂, rfl, hdr.symm, hf1, hf2'⟩
  · rw [hR] at hf1
    simp [rounds, roundsFit] at hf1

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.played_tests
