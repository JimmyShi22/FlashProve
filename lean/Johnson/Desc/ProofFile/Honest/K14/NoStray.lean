-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/NoStray.lean: kind K14: NO HALF THAT sixOf (Honest/K14/Six.lean)
RETURNS STANDS AT NO PLACE OF THE LIST THAT IT WAS HANDED. The frame's strays (Honest/Frame.lean)
lists the places of halves at which no sub-protocol of a chain stands; a maker of an honest prover
rejects a filling where that list is not empty. Statements with their proofs; no definition.

  strays_nil      where every half stands at the place of a member of the list, strays is empty.
                  General: no kind is named. (Kin: strays_of_mem in the kind K5's
                  Honest/K5/Law/LotClean.lean says the same through List.mem_map; that file does not
                  lie beneath this one)
  six_places      each of the kind's halves (six; five where the shape does not split) stands at
                  one of the eight places of the sub-protocols that the library makes of a plan
  tied_of_pass    where sixOf's three tests in a row reject nothing, the list has passed tiedTo
  tied_places     where the list passes sixOf's own test tiedTo, each of the eight places is the
                  place of a member of the list. By the library's Desc.K14.Law.eight
                  (Johnson/Desc/K14/Law/SplitGiven.lean) and own_places
                  (Johnson/Desc/K14/Law/PlacesAtChain.lean)
  six_no_strays   **strays of the list and of what sixOf returns is empty, AT EVERY PLAN AND EVERY
                  LIST; NO PREMISE**: where sixOf rejects there is no half; where it returns, the
                  list has passed tiedTo. IT SERVES A FILLING THAT ASKS strays OF THE VERY LIST THAT
                  IT HANDS TO sixOf

What is not claimed. That sixOf returns anywhere (at the small shape it does: two #guard lines in
Honest/K14/SixToy.lean). That a half stands at EVERY place that sends something: strays tests halves
without a place, not places without a half. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.Six
import Johnson.Desc.K14.Law.PlacesAtChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block Place)

variable {S Cl V W X W₀ Rc Ky : Type}

/-- Where every half stands at the place of a member of the list, strays is empty. -/
theorem strays_nil (bs : List (Block S Cl)) (hs : List (Placed V W X))
    (h : ∀ g ∈ hs, ∃ b ∈ bs, b.place = g.place) : strays bs hs = [] := by
  unfold strays
  rw [List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro g hg hc
  obtain ⟨b, hb, e⟩ := h g hg
  have h1 : (bs.any fun b => b.place == g.place) = true :=
    List.any_eq_true.2 ⟨b, hb, by rw [e]; exact beq_self_eq_true _⟩
  rw [h1] at hc
  cases hc

/-- Each of the kind's halves stands at one of the eight places. d and A are any. -/
theorem six_places (d : Data) (A : SendPub) (weights : W₀ → Weights) (rand : Rc → TableRand) :
    ∀ g ∈ (proverSidesOfSharedRounds d weights ++ proverSidesOfSharedSendings A weights rand :
        List (Placed Empty (Common W₀ Rc Ky) X)),
      g.place ∈
        [place 1, sendPlace 2, place 3, place 4, sendPlace 5, place 6, place 7, place 8] := by
  intro g hg
  rcases List.mem_append.1 hg with h | h
  · unfold proverSidesOfSharedRounds at h
    rcases List.mem_append.1 h with h | h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl <;> simp
    · split at h
      · obtain rfl := List.mem_singleton.1 h
        simp
      · cases h
  · unfold proverSidesOfSharedSendings at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> simp

/-- Where the three public tests in a row reject nothing, the list has passed tiedTo. -/
theorem tied_of_pass (P : Desc.K14.P14) (bs : List (Block S Cl)) (hr : rejection P bs = none) :
    tiedTo P bs = true := by
  unfold rejection at hr
  split at hr
  · cases hr
  · split at hr
    · cases hr
    · split at hr
      · cases hr
      · rename_i h3
        simpa using h3

/-- Where the list passes tiedTo, each of the eight places is the place of a member of it. -/
theorem tied_places (P : Desc.K14.P14) (bs : List (Block S Cl)) (h : tiedTo P bs = true) :
    ∀ a ∈ [place 1, sendPlace 2, place 3, place 4, sendPlace 5, place 6, place 7, place 8],
      ∃ b ∈ bs, b.place = a := by
  unfold tiedTo at h
  cases hb : Desc.K14.blocks P with
  | none =>
    rw [hb] at h
    cases h
  | some l =>
    rw [hb] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    have e : ((bs.drop 1).take l.length).map (·.place) = l.map (·.place) := by
      have e1 := congrArg (List.map Prod.fst) h.2
      rw [List.map_map, List.map_map] at e1
      exact e1
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, rfl⟩ := Desc.K14.Law.eight P l hb
    have e8 : [b1, b2, b3, b4, b5, b6, b7, b8].map (·.place) =
        [place 1, sendPlace 2, place 3, place 4, sendPlace 5, place 6, place 7, place 8] :=
      Desc.K14.Law.own_places P b1 b2 b3 b4 b5 b6 b7 b8 hb
    rw [e8] at e
    intro a ha
    rw [← e] at ha
    obtain ⟨b, hb', rfl⟩ := List.mem_map.1 ha
    exact ⟨b, List.mem_of_mem_drop (List.mem_of_mem_take hb'), rfl⟩

/-- **No half that sixOf returns stands at no place of the list that it was handed.** -/
theorem six_no_strays (P : Desc.K14.P14) (bs : List (Block S Cl)) (weights : W₀ → Weights)
    (rand : Rc → TableRand) :
    strays bs ((sixOf P bs weights rand :
      Except String (List (Placed Empty (Common W₀ Rc Ky) X))).toOption.getD []) = [] := by
  unfold sixOf
  cases hr : rejection P bs with
  | some e => rfl
  | none =>
    cases dataOf P.S bs with
    | none => rfl
    | some d =>
      exact strays_nil bs _ fun g hg =>
        tied_places P bs (tied_of_pass P bs hr) g.place (six_places d _ weights rand g hg)

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.strays_nil
#print axioms ProofFile.Honest.K14.six_places
#print axioms ProofFile.Honest.K14.tied_of_pass
#print axioms ProofFile.Honest.K14.tied_places
#print axioms ProofFile.Honest.K14.six_no_strays
