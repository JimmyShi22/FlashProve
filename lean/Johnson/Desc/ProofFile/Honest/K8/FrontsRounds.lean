-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/FrontsRounds.lean: WHAT AN ENTRY OF `frontsOf`
(Johnson/Desc/ProofFile/Honest/Fall.lean) SAYS OF THE MEMBER THAT IT STANDS FOR: ITS ROUNDS WERE AT
HAND; ITS PLACE; ITS OWN CHALLENGES. AND WHOSE TEST SPEAKS WHERE `fallOf`
(Johnson/Desc/ProofFile/Honest/Side.lean) SPEAKS. Statements and proofs. General in the state, the
claims and the description: no run, no prover, no kind. LEMMAS; NONE OF THE LIBRARY's GOALS.

  **`frontsOf_rounds`**   where there is an entry i, the rounds of the first i + 1 members are at
      most the rounds that were handed in: every listed member has had its rounds
  `frontsOf_place`   entry i bears the place of member i
  `frontsOf_first`   entry 0: the first member's place, the state handed in, and the challenges of
      its rounds
  `fallOf_mem`   where `fallOf` says something at a place, a fall of the list is seated there and
      its test says it
By: `frontsOf_drop` (Johnson/Desc/ProofFile/Honest/K8/FrontsBetween.lean) · `frontsOf_reach₀`
(FrontsReach.lean).
Limits. Nothing on which entries there are.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K8.FrontsBetween
import Johnson.Desc.ProofFile.Honest.K8.FrontsReach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open VerifiableInference.Desc

variable {S Cl : Type}

/-- **Every listed member has had its rounds.** -/
theorem frontsOf_rounds (ft : Nat) : ∀ (bs : List (Block S Cl)) (s : S) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (i : Nat) (e : Place × S × List Fmt.Drawn),
    (frontsOf ft bs s rs cols)[i]? = some e → rnds (bs.take (i + 1)) ≤ rs.length
  | [], _, _, _, _, _, he => by
    simp [frontsOf] at he
  | b :: l, s, rs, cols, i, e, he => by
    have hu : frontsOf ft (b :: l) s rs cols =
        if (rs.take b.rounds.length).length != b.rounds.length then [] else
        (b.place, s, (rs.take b.rounds.length).map (·.drawn)) ::
          match b.step ft s (rs.take b.rounds.length) cols with
          | .error _ => []
          | .ok (s', k) => frontsOf ft l s' (rs.drop b.rounds.length) (cols.drop k) := by
      conv_lhs => unfold frontsOf
      rfl
    rw [hu] at he
    split at he
    · simp at he
    · rename_i hg
      have hlen : b.rounds.length ≤ rs.length := by
        have h1 : (rs.take b.rounds.length).length = b.rounds.length := by
          simpa using hg
        rw [List.length_take] at h1
        omega
      have hc : rnds ((b :: l).take (i + 1)) = b.rounds.length + rnds (l.take i) := by
        rw [List.take_succ_cons]
        show rnds ([b] ++ l.take i) = _
        rw [rnds_append]
        simp [rnds]
      rw [hc]
      cases i with
      | zero =>
        rw [List.take_zero]
        simpa [rnds] using hlen
      | succ i =>
        rw [List.getElem?_cons_succ] at he
        cases hst : b.step ft s (rs.take b.rounds.length) cols with
        | error x =>
          rw [hst] at he
          simp at he
        | ok y =>
          obtain ⟨s', k⟩ := y
          rw [hst] at he
          have ih := frontsOf_rounds ft l s' _ _ i e he
          rw [List.length_drop] at ih
          omega

/-- Entry i bears the place of member i. -/
theorem frontsOf_place (ft : Nat) (bs : List (Block S Cl)) (s : S) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (i : Nat) (e : Place × S × List Fmt.Drawn)
    (he : (frontsOf ft bs s rs cols)[i]? = some e) : (bs[i]?).map (·.place) = some e.1 :=
  (frontsOf_reach₀ ft bs (fun _ : Unit => s) () rs cols i e he).2

/-- Entry 0. -/
theorem frontsOf_first (ft : Nat) (b : Block S Cl) (l : List (Block S Cl)) (s : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (e : Place × S × List Fmt.Drawn)
    (he : (frontsOf ft (b :: l) s rs cols)[0]? = some e) :
    e = (b.place, s, (rs.take b.rounds.length).map (·.drawn)) := by
  have hu : frontsOf ft (b :: l) s rs cols =
      if (rs.take b.rounds.length).length != b.rounds.length then [] else
      (b.place, s, (rs.take b.rounds.length).map (·.drawn)) ::
        match b.step ft s (rs.take b.rounds.length) cols with
        | .error _ => []
        | .ok (s', k) => frontsOf ft l s' (rs.drop b.rounds.length) (cols.drop k) := by
    conv_lhs => unfold frontsOf
    rfl
  rw [hu] at he
  split at he
  · simp at he
  · rw [List.getElem?_cons_zero] at he
    exact (Option.some.inj he).symm

/-- Whose test speaks. -/
theorem fallOf_mem (fs : List (Fall S)) (a : Place) (s : S) (ds : List Fmt.Drawn) (u : String)
    (h : fallOf fs a s ds = some u) : ∃ f ∈ fs, f.place = a ∧ f.test s ds = some u := by
  unfold fallOf at h
  obtain ⟨f, hf, ht⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨h1, h2⟩ := List.mem_filter.1 hf
  exact ⟨f, h1, by simpa using h2, ht⟩

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.frontsOf_rounds
#print axioms ProofFile.Honest.K8.frontsOf_place
#print axioms ProofFile.Honest.K8.frontsOf_first
#print axioms ProofFile.Honest.K8.fallOf_mem
