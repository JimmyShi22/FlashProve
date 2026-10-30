-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/TiePlace.lean: `FieldAt` and `FieldFit` at the state that `midInW`
(MidW.lean) returns before the first part of a place, stated by the place: in the letters of the
statement `Tie2` (Ties.lean): `roundsBefore` of the chain's list and `roundsAhead` of the whole
walk's rounds. One chain. The form that a file's three chains can call.

  `split_at_place`   a list of sub-protocols, cut at the first one at a place
  `fieldAt_place`   **the statement.** Its hypotheses: the lay's trees are `envOf`'s at `taken`
     (`hL`); the places of the chain's list differ; `chainSteps` returns the steps; the chain's
     start and the walk over all steps return; `midInW` returns a state at `⟨p, 0⟩`. That a round
     stands at that address is read off `midInW` itself, which returns an error otherwise; that the
     start was handed two states, off `start_live` and `walk_live` (WalkLive.lean)

By what: `fieldAt_chain` (TieChain.lean), `chainSteps_split`, `steps_place_mem` (StepsFront.lean).

Limits.
  * One chain. What a run's parts and the three chains' starts are is not treated here.
  * Conditional: nothing shows that `midInW` returns a state.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.TieChain
import Johnson.Desc.ProofFile.Honest.WalkLive

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block OpenedColumn Place)

/-- A list of sub-protocols, cut at the first one that stands at `p`. -/
theorem split_at_place {S Cl : Type} (p : Place) : ∀ (bs : List (Block S Cl)),
    (∃ b ∈ bs, b.place = p) →
    ∃ pre b t, bs = pre ++ b :: t ∧ pre = bs.takeWhile (fun b => b.place != p) ∧ b.place = p ∧
      ∀ b' ∈ pre, b'.place ≠ p
  | [], ⟨_, hb, _⟩ => by cases hb
  | c :: bs, ⟨b, hb, e⟩ => by
    by_cases hc : c.place = p
    · refine ⟨[], c, bs, rfl, ?_, hc, fun _ h => by cases h⟩
      rw [List.takeWhile_cons_of_neg]
      rw [hc]
      simp
    · have hb' : b ∈ bs := by
        rcases List.mem_cons.1 hb with rfl | h
        · exact absurd e hc
        · exact h
      obtain ⟨pre, b₀, t, e1, e2, e3, e4⟩ := split_at_place p bs ⟨b, hb', e⟩
      refine ⟨c :: pre, b₀, t, by rw [List.cons_append, ← e1], ?_, e3, ?_⟩
      · rw [List.takeWhile_cons_of_pos (by rw [bne_iff_ne]; exact hc), ← e2]
      · intro b' h'
        rcases List.mem_cons.1 h' with rfl | h''
        · exact hc
        · exact e4 b' h''

/-- **At the state that `midInW` returns before the first part of a place, by the place.** -/
theorem fieldAt_place {S Cl V W Y : Type} (L : Lay)
    {taken : Nat → Nat → Option (Place × Table)}
    (hL : ∀ ps, L.tree ps = (envOf L.stored taken ps).tree) (bs : List (Block S Cl))
    (hnd : (bs.map (·.place)).Nodup) (mo : Option (Mid W Y)) (vo : Option S) (front : List OpenedColumn)
    {a₀ z : ChainProgress S Cl W Y} {steps : List (Step W Y)} {ds : List Fmt.Drawn}
    {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d} {v : Option V}
    {hs : List (Placed V W Y)} (hc : chainSteps B rows look v bs hs = .ok steps)
    (ha : ChainProgress.start L bs mo vo front = .ok a₀) (hw : walk L steps ds a₀ = .ok z) {p : Place}
    {m : Mid W Y} (hm : midInW L steps ds a₀ ⟨p, 0⟩ = .ok (some m)) :
    ∃ m₀, mo = some m₀ ∧
      FieldAt L.chain L.firstTree (roundsBefore bs p) front m₀.st.heard.length m
        (envOf L.stored taken (roundsAhead z.laid p)) ∧
      FieldFit (roundsBefore bs p) m₀.st.heard.length m
        (envOf L.stored taken (roundsAhead z.laid p)) := by
  have hany : steps.any (fun s => s.addr == ⟨p, 0⟩) = true := by
    unfold midInW at hm
    simp only at hm
    split at hm
    · cases hm
    · rename_i hn
      simpa using hn
  have hlive : a₀.mid.isSome = true := by
    unfold midInW at hm
    simp only at hm
    split at hm
    · cases hm
    · obtain ⟨z₁, h1, e⟩ := map_ok hm
      exact walk_live L _ _ a₀ z₁ m h1 e
  obtain ⟨m₀, v₀, rfl, rfl⟩ := start_live ha hlive
  obtain ⟨s, hs', es⟩ := List.any_eq_true.1 hany
  have es' : s.addr = ⟨p, 0⟩ := beq_iff_eq.1 es
  obtain ⟨b₁, hb₁, eb₁⟩ := steps_place_mem hc s hs'
  obtain ⟨pre, b, t, e1, e2, rfl, e4⟩ := split_at_place p bs ⟨b₁, hb₁, by rw [← eb₁, es']⟩
  have er : roundsBefore bs b.place = pre.flatMap (·.rounds) := by
    unfold roundsBefore
    rw [← e2]
  subst e1
  have ht : ∀ b' ∈ t, b'.place ≠ b.place := by
    intro b' hb' eq
    rw [List.map_append, List.map_cons] at hnd
    have h2 := (List.nodup_cons.1 hnd.of_append_right).1
    exact h2 (by rw [← eq]; exact List.mem_map.2 ⟨b', hb', rfl⟩)
  obtain ⟨_, _, _, -, -, -, -, hb⟩ := chainSteps_split hc e4 ht hany
  rw [er]
  exact ⟨m₀, rfl, fieldAt_chain L hL pre b t hb m₀ v₀ front hc e4 ht hany ha hw hm⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.split_at_place
#print axioms ProofFile.Honest.fieldAt_place
