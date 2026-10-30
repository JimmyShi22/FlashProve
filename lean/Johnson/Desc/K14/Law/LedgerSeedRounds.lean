-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerSeedRounds.lean: THE FIRST WRITTEN ROUND OF EACH OF THE SHARED CHAIN's
TWO SENDINGS, WHERE TWO WRITTEN ROUNDS GO ALONG THE BLOCK's DECLARED ROUNDS: its entry is K1's
entry of the round of the seeds, its kind is "seeds", and it sends as many trees as the sending's
layout has: the statement that Johnson/Desc/K14/Law/LedgerSeedRoundsOwed.lean names as owed
(SeedRoundsOwed), proved.

  two_sendings   the kind's blocks 2 and 5 are sendAt at the two sendings' parameters. (The
                 statement and the proof of blocks_two, Johnson/Desc/Sound/FenceK14Named.lean, which
                 stands over the fence and is no import here.)
  sendAt_rounds  a sending's declared rounds are K1's two (by rfl).
  seed_round     what RoundIs says at K1's declared round of the seeds.
  seedRounds     THE STATEMENT.
What is not claimed. That a piece's written rounds go along the block's. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.LedgerSeedRoundsOwed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound (RoundIs Along)
open VerifiableInference.Desc.K1 (seedEntry)

/-- The two sendings, to the letter. -/
theorem two_sendings (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    ∃ sentU, withU P.S = some sentU ∧
      b2 = sendAt P "send o_u" (parK1 P 2 "o_u and the first mask" sentU) (entries P)[0]? [[0], []]
        (behindU P.par) ∧
      b5 = sendAt P "send o_omega" (parK1 P 5 "o_omega and o_sp" (withOmega P.S)) (entries P)[1]?
        [[1], [1, 0]] (behindOmega P.par) := by
  unfold blocks at hbl
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hbl
  obtain ⟨sentU, hU, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hbl
  exact ⟨sentU, hU, rfl, rfl⟩

/-- A sending's declared rounds are K1's two. -/
theorem sendAt_rounds (P : P14) (n : String) (K : VerifiableInference.Desc.K1.Par)
    (inFront : Option Fmt.Entry) (groups : List (List Nat)) (behind : St → Array Nat → Option St) :
    (sendAt P n K inFront groups behind).rounds = VerifiableInference.Desc.K1.rounds K := rfl

/-- What RoundIs says at K1's declared round of the seeds. -/
theorem seed_round (K : VerifiableInference.Desc.K1.Par) (num : Fmt.TreeSource → ℕ) (d : RDT)
    (h : RoundIs num { entry := seedEntry K } d) :
    d.entry = seedEntry K ∧ d.kind = .seeds ∧ d.trees.length = K.trees.length := by
  obtain ⟨h1, h2, _, _, _, h6⟩ := h
  have hk : Fmt.kindOf "SEND seed" = some Fmt.Kind.seeds := by decide
  have h2' : Fmt.kindOf "SEND seed" = some d.kind := h2
  exact ⟨h1, (Option.some.inj (hk.symm.trans h2')).symm, h6⟩

/-- **The statement.** -/
theorem seedRounds : SeedRoundsOwed := by
  intro Q b1 b2 b3 b4 b5 b6 b7 b8 sentU hbl hU num d₁ d₂
  obtain ⟨s, hs, rfl, rfl⟩ := two_sendings Q b1 b2 b3 b4 b5 b6 b7 b8 hbl
  obtain rfl := Option.some.inj (hs.symm.trans hU)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [sendAt_rounds] at h
    exact seed_round _ num d₁ h.1
  · rw [sendAt_rounds] at h
    exact seed_round _ num d₁ h.1

end Desc.K14.Law
