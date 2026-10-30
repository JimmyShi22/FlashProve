-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Tie2File.lean: the statement `Tie2` (Ties.lean) is a theorem: at every
description, book and prover: at every run of `runC` that returns, before the first part of every
place at which a round was played, chain by chain: `FieldAt` and `FieldFit` (Field.lean,
FieldLaw.lean) hold at the state that `midAtW` or `midSharedAtW` (MidW.lean) returns, at the run's
own letters.

  1  `placesOk_of_tests`   `readyTests` (Frame.lean) tests the description's places
     `place_of_played`, `place_of_mid`   where a played round stands at a place, or `midInW` returns
     at it, it is the place of one of the chain's sub-protocols
     `heard_len`   how many challenges the state at a walk's end has heard
  2  `tie2`   **the theorem**

By what. `fieldAt_place` (TiePlace.lean), three times. Of others: `runC_parts`
(Law/Rule/WalkLaw.lean), `ready_ok` (Law/Run.lean), `orderOf_nodup`, `chain_first`, `chain_second`
(Law/Rule/Tests.lean), `envOf_tree` (Law/Cut.lean), `K12.walk_lengths` (K12/LiveField.lean).

Limits.
  * Conditional in each clause: a round was played at the address, and `midAtW` returns a state. It
    is not shown that it does.
  * Before the first part of a place alone.
  * `Tie1` (the field against `Good.exact`'s hypothesis at the run's own `front`) is not treated.
  * The theorem is about the frame's own bookkeeping. It proves no property of a prover or a
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.TiePlace
import Johnson.Desc.ProofFile.Honest.Law.Rule.Tests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place OpenedColumn)

/-! ## 1 Small steps -/

section
variable {Xi W₀ Rc Ky Tr X₀ X : Type}

/-- `readyTests` tests the description's places. -/
theorem placesOk_of_tests {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀}
    (h : readyTests F B H w₀ = .ok ()) : F.placesOk = true := by
  unfold readyTests at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i hp
        simpa using hp

end

section
variable {S Cl V W Y : Type} {L : Lay} {bs : List (Block S Cl)} {B : ProverCoinCounts}
  {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d} {v : Option V}
  {hs : List (Placed V W Y)} {steps : List (Step W Y)} {ds : List Fmt.Drawn}
  {a₀ z : ChainProgress S Cl W Y} {p : Place}

/-- Where a played round stands at a place, it is the place of one of the chain's sub-protocols. -/
theorem place_of_played {mo : Option (Mid W Y)} {vo : Option S} {front : List OpenedColumn} {j : Nat}
    (hc : chainSteps B rows look v bs hs = .ok steps)
    (ha : ChainProgress.start L bs mo vo front = .ok a₀) (hw : walk L steps ds a₀ = .ok z)
    (hp : z.laid.any (·.isAt ⟨p, j⟩) = true) : p ∈ bs.map (·.place) := by
  obtain ⟨q, hq, eq⟩ := List.any_eq_true.1 hp
  have eq' : q.place = p := by
    unfold Played.isAt at eq
    simp only [Bool.and_eq_true, beq_iff_eq] at eq
    exact eq.1
  have e := walk_laid_places L steps ds a₀ z hw
  rw [start_laid ha, List.map_nil, List.nil_append] at e
  have hm : q.place ∈ z.laid.map (·.place) := List.mem_map.2 ⟨q, hq, rfl⟩
  rw [e] at hm
  obtain ⟨s, hs', es⟩ := List.mem_map.1 hm
  obtain ⟨b, hb, eb⟩ := steps_place_mem hc s hs'
  exact List.mem_map.2 ⟨b, hb, by rw [← eb, es, eq']⟩

/-- Where `midInW` returns at an address, its place is that of one of the chain's sub-protocols. -/
theorem place_of_mid {j : Nat} {o : Option (Mid W Y)}
    (hc : chainSteps B rows look v bs hs = .ok steps)
    (hm : midInW L steps ds a₀ ⟨p, j⟩ = .ok o) : p ∈ bs.map (·.place) := by
  have hany : steps.any (fun s => s.addr == ⟨p, j⟩) = true := by
    unfold midInW at hm
    simp only at hm
    split at hm
    · cases hm
    · rename_i hn
      simpa using hn
  obtain ⟨s, hs', es⟩ := List.any_eq_true.1 hany
  have es' : s.addr = ⟨p, j⟩ := beq_iff_eq.1 es
  obtain ⟨b, hb, eb⟩ := steps_place_mem hc s hs'
  exact List.mem_map.2 ⟨b, hb, by rw [← eb, es']⟩

/-- The state at a walk's end has heard as many challenges as its start and the walk's together. -/
theorem heard_len {m₀ m : Mid W Y} {vo : Option S} {front : List OpenedColumn}
    (ha : ChainProgress.start L bs (some m₀) vo front = .ok a₀) (hw : walk L steps ds a₀ = .ok z)
    (hm : z.mid = some m) : m.st.heard.length = m₀.st.heard.length + ds.length := by
  have h := walk_hears L _ steps ds a₀ z (start_hears ha) hw m hm
  have e1 := walk_laid_length L steps ds a₀ z hw
  have e2 := K12.walk_lengths L steps ds a₀ z hw
  rw [start_laid ha] at e1
  rw [h, List.length_append, List.length_map, e1, e2]
  simp

end

/-! ## 2 The theorem -/

variable {Xi W₀ Rc Ky Tr X₀ X : Type}

/-- **`Tie2` holds**, at every description, book and prover. -/
theorem tie2 (F : FileDescription Xi) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) : Tie2 F B H := by
  intro w₀ rc x c ρ r hr p
  obtain ⟨R, a₁, z₁, a₂, z₂, a₃, z₃, hR, ha₁, hz₁, hq, ha₂, hz₂, ha₃, hz₃, rfl⟩ := runC_parts hr
  obtain ⟨hT, tr, -, -, -, hc₁, hc₂, hc₃⟩ := ready_ok hR
  have hp := placesOk_of_tests hT
  have hn := orderOf_nodup hp
  unfold orderOf at hn
  have n₁ := hn.of_append_left.of_append_left
  have n₂ := hn.of_append_left.of_append_right
  have n₃ := hn.of_append_right
  have hLo : ∀ ps, treeOwn ps = (envOf (H.storedWords w₀ rc) (fun _ _ => none) ps).tree :=
    fun ps => (envOf_tree (H.storedWords w₀ rc) ps [] []).1.symm
  have hL₃ : ∀ ps, treeThird z₁.laid z₂.laid ps =
      (envOf (H.storedWords w₀ rc) (takenOf z₁.laid z₂.laid) ps).tree :=
    fun ps => (envOf_tree (H.storedWords w₀ rc) z₁.laid z₂.laid ps).2.symm
  have apart : p ∈ F.first.blocksInOrder.map (·.place) → p ∈ F.second.blocksInOrder.map (·.place) → False := by
    intro h1 h3
    have e1 := chain_first hp p h1
    have e3 := chain_second hp p h3
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro h₁ m hm
    have hp₁ : p ∈ F.first.blocksInOrder.map (·.place) := place_of_played hc₁ ha₁ hz₁ h₁
    unfold midAtW at hm
    simp only [hR, ha₁, Except.bind] at hm
    split at hm
    · obtain ⟨m₀, e, f1, f2⟩ := fieldAt_place ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ hLo
        F.first.blocksInOrder n₁ _ _ [] hc₁ ha₁ hz₁ hm
      obtain rfl := Option.some.inj e
      exact ⟨f1, f2⟩
    · exfalso
      simp only [hz₁, hq, ha₂, hz₂, ha₃, Bool.not_true, Bool.false_eq_true, if_false] at hm
      exact apart hp₁ (place_of_mid hc₃ hm)
  · intro _ m hm
    unfold midSharedAtW at hm
    simp only [hR, ha₂, Except.bind] at hm
    obtain ⟨m₀, e, f1, f2⟩ := fieldAt_place ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ hLo
      F.shared.blocksInOrder n₂ _ _ [] hc₂ ha₂ hz₂ hm
    obtain rfl := Option.some.inj e
    exact ⟨f1, f2⟩
  · intro h₃ m hm
    have hp₃ : p ∈ F.second.blocksInOrder.map (·.place) := place_of_played hc₃ ha₃ hz₃ h₃
    unfold midAtW at hm
    simp only [hR, ha₁, Except.bind] at hm
    split at hm
    · exact absurd hp₃ fun h3 => apart (place_of_mid hc₁ hm) h3
    · simp only [hz₁, hq, ha₂, hz₂, ha₃, Bool.not_true, Bool.false_eq_true, if_false] at hm
      obtain ⟨m₀, e, f1, f2⟩ := fieldAt_place
        ⟨2, F.lastChainFirstTreeNumber, H.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩ hL₃
        F.second.blocksInOrder n₃ _ _ (z₁.cols ++ z₂.cols) hc₃ ha₃ hz₃ hm
      cases h1 : z₁.mid with
      | none =>
        rw [h1] at e
        cases e
      | some m₁ =>
        cases h2 : z₂.mid with
        | none =>
          rw [h1, h2] at e
          cases e
        | some m₂ =>
          rw [h1, h2] at e
          obtain rfl : R.start₃ H m₁ m₂ = m₀ := Option.some.inj e
          have l₁ := heard_len ha₁ hz₁ h1
          have l₂ := heard_len ha₂ hz₂ h2
          have el : (R.start₃ H m₁ m₂).st.heard.length = ρ.first.length + ρ.shared.length := by
            show (m₁.st.heard ++ m₂.st.heard).length = _
            rw [List.length_append, l₁, l₂]
            show 0 + ρ.first.length + (0 + ρ.shared.length) = _
            omega
          rw [el] at f1 f2
          exact ⟨f1, f2⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.placesOk_of_tests
#print axioms ProofFile.Honest.place_of_played
#print axioms ProofFile.Honest.place_of_mid
#print axioms ProofFile.Honest.heard_len
#print axioms ProofFile.Honest.tie2
