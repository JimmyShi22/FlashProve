-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/ScriptLotsAtL.lean: CLOSED FACTS beside ScriptLots.lean: public
numbers of the kind's lots at the library's written record of the last group's test
(`H2K.Member.piLFull`, Johnson/Desc/K12/Law/PlacesFull.lean). Four theorems; three are evaluations
in Lean's kernel at written values.

  `stages_LFull`   the record has six stages
  `seedRound_LFull`   the five trees' own rounds: 3, 10, 16, 22, 29
  `seedRound_bite`   a control: at the list without its first stage the five numbers are others
  `lots_count_L`   ten lots of messages and five of pads, at every job whose parameters are the
                 record

Limits.
- All that binds whoever builds on ScriptLots.lean (its head) binds here.
- The control shows that `seedRound` reads its list. It is none on «these are the rounds that send»:
  no statement here ties the five numbers to the record's oracles.
- At the written record alone; that a seated place or a job's parameters are that record is other
  files' matter.
- It moves no count. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.ScriptLots
import Johnson.Desc.K12.Law.PlacesFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12

/-- The written record has six stages. -/
theorem stages_LFull : H2K.Member.piLFull.nums.stages.length = 6 := by
  decide +kernel

/-- **The five trees' own rounds at the written record.** -/
theorem seedRound_LFull :
    (List.range 5).map (seedRound H2K.Member.piLFull.nums.stages) = [3, 10, 16, 22, 29] := by
  decide +kernel

/-- A control: at the same list without its first stage the numbers are others. -/
theorem seedRound_bite :
    (List.range 5).map (seedRound H2K.Member.piLFull.nums.stages.tail) = [6, 12, 18, 25, 28] := by
  decide +kernel

/-- **Ten lots of messages and five of pads**, at every job whose parameters are the written
record. -/
theorem lots_count_L {Bk : ProverCoinCounts} {W X : Type} (ch : ℕ) (J : TestJob W X)
    (hJ : J.p = H2K.Member.piLFull) (own₀ : X) (n₀ t₀ : ℕ) (arr : ℕ → ℕ → ℕ)
    (ok : W → List Fmt.Drawn → (ℕ → Stretch) → Bool) (codes : OnBytes.Codes)
    (sh : ℕ → OnBytes.OracleShape) :
    (testMsgLots (Bk := Bk) ch J own₀ n₀ t₀ arr ok).length = 10 ∧
      (testPadLots (Bk := Bk) ch J codes sh t₀).length = 5 := by
  rw [testMsgLots_length, testPadLots_length, hJ, stages_LFull]
  exact ⟨rfl, rfl⟩

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.stages_LFull
#print axioms ProofFile.Honest.K12.seedRound_LFull
#print axioms ProofFile.Honest.K12.seedRound_bite
#print axioms ProofFile.Honest.K12.lots_count_L
