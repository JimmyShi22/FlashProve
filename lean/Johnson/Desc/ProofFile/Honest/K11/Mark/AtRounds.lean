-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K11/Mark/AtRounds.lean: the proofs of the three statements of
Honest/K11/Mark/AtRoundsStatement.lean, to the letter, with two helpers. Lemmas; none of the
library's goals.

How. `forall2_at`: two lists that stand in a relation pair by pair do so at each number. The merge's
declared round number 1 is the round "PSC epsilon", the numbers 2 to lk + 1 are rounds "PSC round"
(`mergeEntries`, Johnson/Desc/First/Fork/MergeKind.lean): each draws one element, no position and no
trit, none by the rule that never gives 0; the format gives none of the twelve rounds' names the
kind of a sealing or of seeds (`kind_of_name`, Johnson/Desc/First/K4/DsTail.lean): so what such a
round draws is one field element and nothing else, by the text of `Fmt.dsOf` (`oneElem_named`). Then
`headMergeMarkDebt` (Proofs.lean of this folder). The seated block's rounds are the kind's by the
text of `IM.seatedAs`.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Mark.AtRoundsStatement
import Johnson.Desc.ProofFile.Honest.K11.Mark.Proofs
import Johnson.Desc.First.K4.DsTail

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Maker (RDT)
open OnBytes.Model (RoundName)
open VerifiableInference.Desc.First.K8.Honest (OneElem)
open Johnson.Desc.First.ForkMerge (mergeEntries)

/-- Two lists that stand in a relation pair by pair do so at each number. -/
theorem forall2_at {α β : Type} {R : α → β → Prop} : ∀ {l₁ : List α} {l₂ : List β},
    List.Forall₂ R l₁ l₂ → ∀ (i : Nat) (a : α), l₁[i]? = some a → ∃ b, l₂[i]? = some b ∧ R a b
  | _, _, .nil, _, _, h => by cases h
  | _, _, .cons hab _, 0, _, h => by
    cases h
    exact ⟨_, rfl, hab⟩
  | _, _, .cons _ ht, i + 1, a, h => forall2_at ht i a h

/-- A round that bears one of the twelve names, draws one element, none by the rule that never gives
0, no position and no trit, draws one field element and nothing else. -/
theorem oneElem_named (n : RoundName) (e : Fmt.Entry) (k : Fmt.Kind)
    (hk : Fmt.kindOf n.name = some k) (h1 : e.drawE = 1) (h2 : e.drawNZ = 0) (h3 : e.poss = 0)
    (h4 : e.trits = 0) : OneElem e k := by
  unfold OneElem Fmt.dsOf Fmt.dsElems
  rw [h1, h2, h3, h4]
  rcases OnBytes.Desc.First.K4.kind_of_name n with c | c | c <;>
  · rw [c] at hk
    rw [← Option.some.inj hk]
    rfl

/-- **The listed rounds draw one element each.** -/
theorem mergeListedFit : MergeListedFit := by
  intro lk work dsb hF i d hd hi
  obtain ⟨z, hz, he, hk⟩ := forall2_at hF i d hd
  have hi' : 1 ≤ i ∧ i < 1 + (lk + 1) := by
    unfold mergeListed at hi
    exact List.mem_range'_1.1 hi
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  cases j with
  | zero =>
    obtain rfl := Option.some.inj hz
    rw [he]
    exact ⟨oneElem_named RoundName.pscEpsilon _ _ hk rfl rfl rfl rfl, Nat.zero_le _⟩
  | succ j =>
    have hj : j < lk := by omega
    unfold mergeEntries at hz
    rw [List.map_cons, List.map_cons, List.getElem?_cons_succ, List.getElem?_cons_succ,
      List.getElem?_map, List.getElem?_append_left (by rw [List.length_replicate]; exact hj),
      List.getElem?_replicate, if_pos hj] at hz
    obtain rfl := Option.some.inj hz
    rw [he]
    exact ⟨oneElem_named RoundName.pscRound _ _ hk rfl rfl rfl rfl, Nat.zero_le _⟩

/-- **The mark's sentence at the merge's declared rounds.** -/
theorem headMergeMarkDebtAt : HeadMergeMarkDebtAt := by
  intro P dsb Q hF
  exact headMergeMarkDebt P dsb Q (mergeListedFit P.lay.lk P.work dsb hF)

/-- **The mark's sentence at the seated block's rounds.** -/
theorem headMergeMarkDebtSeat : HeadMergeMarkDebtSeat := by
  intro P name pl dsb Q hF
  exact headMergeMarkDebtAt P dsb Q hF

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.forall2_at
#print axioms ProofFile.Honest.K11.oneElem_named
#print axioms ProofFile.Honest.K11.mergeListedFit
#print axioms ProofFile.Honest.K11.headMergeMarkDebtAt
#print axioms ProofFile.Honest.K11.headMergeMarkDebtSeat
