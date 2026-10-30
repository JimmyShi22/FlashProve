-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K14/HalvesAmong.lean: the linear claim's shared rounds (kind K14): the
two facts on the list of the shared chain's prover's sides that the kind's statements ask (HalvesIn
and SendsIn, Honest/K14/AcceptedAll.lean), for a list that holds MORE than this kind's six sides.

Why. halves_now and halves_shared (Honest/K14/AtFilling.lean) show the two facts for a list that is
this kind's six sides and nothing else. A filling that lays the sides of the shared chain's two
proximity tests behind the six (AtFullSide/K14/SixAtBase.lean: base_shared) has a longer list, so
these two theorems do not apply to it.

  sixPlaces       the six places: "LIN point", "LOC", "LIN zeta", "SPLIT", and the two sendings
  six_apart       the places of the kind's own sides and of the two sendings' sides are among them,
                  each once
  halves_among    **HalvesIn and SendsIn** for a list that begins with the six sides, where the rest
                  of the list stands at places that differ from each other and from the six

What is assumed in halves_among: the equation on the list (hs), and the two facts on the rest of the
list (apart, off). Nothing is asked of what the rest plays.

What is not claimed. That any prover's list has this form. Nothing on what a side plays. Nothing on
completeness, soundness or hiding.
Terms. A side is the prover's list of parts at one place (Placed, Honest/Frame.lean).
-/
import Johnson.Desc.ProofFile.Honest.K14.AcceptedAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (TableKey)
open VerifiableInference.Desc (Place)
open Desc.K14 (P14)

/-- The six places at which this kind's sides and the two sendings' sides stand. -/
def sixPlaces : List Place :=
  [place 1, place 4, place 7, place 8, sendPlace 2, sendPlace 5]

variable {W₀ Rc Ky X : Type}

/-- **The places of the six sides**: each is one of the six places, and none stands twice. Where the
shape does not split there are five sides: "SPLIT" has none. -/
theorem six_apart (A : Data) (B : SendPub) (weights : W₀ → Weights) (rand : Rc → TableRand) :
    (((proverSidesOfSharedRounds A weights ++ proverSidesOfSharedSendings B weights rand :
        List (Placed Empty (Common W₀ Rc Ky) X))).map (·.place)).Nodup ∧
      ∀ g ∈ (proverSidesOfSharedRounds A weights ++ proverSidesOfSharedSendings B weights rand :
        List (Placed Empty (Common W₀ Rc Ky) X)), g.place ∈ sixPlaces := by
  rw [halves_eq, sendHalves_eq]
  by_cases h : A.S.sharedSplitNeeded = true
  · rw [if_pos h]
    refine ⟨?_, ?_⟩
    · show ([place 1, place 4, place 7, place 8, sendPlace 2, sendPlace 5] : List Place).Nodup
      decide
    · intro g hg
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [sixPlaces]
  · rw [if_neg h]
    refine ⟨?_, ?_⟩
    · show ([place 1, place 4, place 7, sendPlace 2, sendPlace 5] : List Place).Nodup
      decide
    · intro g hg
      simp only [List.cons_append, List.nil_append, List.append_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp [sixPlaces]

variable {Bk : ProverCoinCounts} {X₀ P₁ Wt : Type} {Q : P14} {O : Others Bk W₀ Rc X₀ P₁ Wt} {A : Data}
  {weights : W₀ → Weights} {rand : Rc → TableRand}
  {more : List (Placed Empty (Common W₀ Rc TableKey) X₀)}

/-- **HalvesIn and SendsIn for a list that begins with the six sides.** hS: the public data has the
plan's shape. hs: the list is the kind's own sides, the two sendings' sides, then `more`. apart: no
two sides of `more` stand at one place. off: no side of `more` stands at one of the six places. -/
theorem halves_among (hS : A.S = Q.S)
    (hs : O.hs = proverSidesOfSharedRounds A weights ++ proverSidesOfSharedSendings ⟨Q, A.atPoint⟩ weights rand ++ more)
    (apart : (more.map (·.place)).Nodup) (off : ∀ g ∈ more, g.place ∉ sixPlaces) :
    HalvesIn Q O A weights ∧ SendsIn Q O A weights rand := by
  obtain ⟨nd, among⟩ := six_apart (Ky := TableKey) (X := X₀) A ⟨Q, A.atPoint⟩ weights rand
  refine ⟨⟨hS, ?_, fun h hh => ?_⟩, fun g hg => ?_⟩
  · rw [hs, List.map_append]
    refine List.pairwise_append.2 ⟨nd, apart, fun a ha b hb e => ?_⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
    have e' : x.place = y.place := e
    exact off y hy (e' ▸ among x hx)
  · rw [hs]
    exact List.mem_append_left _ (List.mem_append_left _ hh)
  · rw [hs]
    exact List.mem_append_left _ (List.mem_append_right _ hg)

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.six_apart
#print axioms ProofFile.Honest.K14.halves_among
