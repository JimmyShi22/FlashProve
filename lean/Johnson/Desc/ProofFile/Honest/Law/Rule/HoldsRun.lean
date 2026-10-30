-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/HoldsRun.lean: `Before.holds`, at a run. Where a run of the
prover of Honest/Walk.lean goes through, what has been produced before a part holds a column for
every read that the part's own rounds make (Honest/Law/Rule/Holds.lean: `holds_at`). The main lemma
is stated at `RunOk` (Honest/Law/Rule/Reads.lean), which a run that goes through satisfies
(`runOk_of`); no lemma of this file is stated at `runC` but `run_src`. It is the thirteenth piece of
the proof of `rowOk_of` (Honest/Law/Rule/Bridge.lean: from `Owed` to `RowOk`).

  1  `src_of`, `run_src`   a read of the first or the shared chain has its source in its own chain
  2  `tabs_front`   a table that is listed among a chain's first rounds is listed among all
  3  `holds_run`   the main lemma. `l₀`, `l₁`, `l₂`: the rounds produced so far: of the part's chain
     an initial stretch of the run's rounds; of the chains that the part is shown beside it, all

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.Holds
import Johnson.Desc.ProofFile.Honest.Law.Rule.Reads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place)

variable {Xi W₀ Rc Ky Tr X₀ X : Type}

/-! ## 1 Where a read's source is -/

theorem src_of {S Cl W Y : Type} {L : Lay} {bs : List (Block S Cl)} {ss : List (Step W Y)}
    {ds : List Fmt.Drawn} {c c' : Core S W Y} (hC : Chained L bs ss ds c c') (hr : c.reads = [])
    (hl : ss.length = (bs.map (·.rounds.length)).sum) (hd : ds.length = ss.length)
    (vis : ∀ a o pT, L.tree a o = some pT → (srcOf L.chain o).1 = L.chain) :
    ∀ q ∈ c'.reads, ∀ c₀ j, q.src = some (c₀, j) → c₀ = L.chain := by
  obtain ⟨new, h1, -, h3⟩ := chained_reads bs ss ds c c' hC hl hd
  rw [hr, List.nil_append] at h1
  rw [h1]
  intro q hq c₀ j hs
  obtain ⟨w1, a, b, blk, own, -, -, e3⟩ := h3 q hq
  rcases readsOf_form _ _ _ _ _ _ q e3 with ⟨i, -, g2, -⟩ | ⟨o, -, g2, g3⟩
  · rw [g2] at hs
    cases hs
  · cases ht : L.tree a o with
    | none =>
      rw [g3, ht] at w1
      cases w1
    | some pT =>
      have := vis a o pT ht
      rw [g2] at hs
      have e : srcOf L.chain o = (c₀, j) := Option.some.inj hs
      rw [e] at this
      exact this

theorem run_src {F : FileDescription Xi} {Bk : ProverCoinCounts} {P : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀} {rc : Rc}
    {x : Xi} {k : Coins Bk} {ρ : Draws} {r : RunC F} (hrun : runC F Bk P w₀ rc x k ρ = .ok r) :
    (∀ q ∈ r.run.reads.1, ∀ c j, q.src = some (c, j) → c = 0) ∧
      ∀ q ∈ r.run.reads.2.1, ∀ c j, q.src = some (c, j) → c = 1 := by
  obtain ⟨R, a₁, z₁, a₂, z₂, a₃, z₃, hR, ha₁, hz₁, -, ha₂, hz₂, -, -, rfl⟩ := runC_parts hrun
  obtain ⟨-, tr, -, -, -, hs₁, hs₂, -⟩ := ready_ok hR
  have l1 := chainSteps_length _ _ hs₁
  have l2 := chainSteps_length _ _ hs₂
  have C1 := chained_of_start ha₁ hz₁ l1
  have C2 := chained_of_start ha₂ hz₂ l2
  exact ⟨src_of C1 rfl l1 (walk_length _ _ _ _ hz₁) fun a o pT h => by
      obtain ⟨n, rfl, -⟩ := own_tab a o pT h
      rfl,
    src_of C2 rfl l2 (walk_length _ _ _ _ hz₂) fun a o pT h => by
      obtain ⟨n, rfl, -⟩ := own_tab a o pT h
      rfl⟩

/-! ## 2 The tables of an initial stretch -/

theorem tabs_front (a b : List Played) (j : Nat) (T : Option Table)
    (h : (allTabs a)[j]? = some T) : (allTabs (a ++ b))[j]? = some T := by
  rw [allTabs_append]
  have hlt : j < (allTabs a).length := by
    cases hj : (allTabs a)[j]? with
    | none =>
      rw [hj] at h
      cases h
    | some _ => exact (List.getElem?_eq_some_iff.1 hj).1
  rw [List.getElem?_append_left hlt]
  exact h

/-! ## 3 The main lemma -/

/-- **`Before.holds`, at a run.** `ch`: the part's chain, at most 2. `l₀`, `l₁`, `l₂`: the rounds
produced so far; `t₀`, `t₁`, `t₂`: those still to come. `hq`: the reads in question are among that
chain's reads, without what depends on a table. `h`: `RunOk` of the run's rounds: those produced so
far with those still to come. `hown`: in the first and the shared chain each read's source is in its
own chain (`run_src`). `hall`: for the second chain the other two have nothing still to come. -/
theorem holds_run {F : FileDescription Xi} {ρ : Draws} {stored : Nat → Nat → Option (List UInt64)}
    {l₀ l₁ l₂ t₀ t₁ t₂ : List Played} {q₀ q₁ q₂ : List Read}
    (h : RunOk F ρ stored (l₀ ++ t₀) (l₁ ++ t₁) (l₂ ++ t₂) q₀ q₁ q₂) (ch ft : Nat) (hch : ch ≤ 2)
    (hown : ch ≠ 2 → ∀ q ∈ pick3 q₀ q₁ q₂ ch, ∀ c j, q.src = some (c, j) → c = ch)
    (hall : ch = 2 → ∀ c, c ≤ 2 → c ≠ ch → pick3 t₀ t₁ t₂ c = [])
    (decls : List Fmt.DeclaredRound) (ds : List Fmt.Drawn)
    (hq : ∀ q ∈ readsOf ch ft (fun _ _ => none) (fun _ => none) decls ds,
      q ∈ (pick3 q₀ q₁ q₂ ch).map Read.bare) :
    ((laidOf F ρ l₀ l₁ l₂).front ch (storedShown stored (storedAsks F ρ))).holds ch ft decls ds =
      true := by
  refine holds_at F ρ stored l₀ l₁ l₂ ch ft decls ds fun q hq' => ?_
  obtain ⟨q', hm, rfl⟩ := List.mem_map.1 (hq q hq')
  have hmem : q' ∈ q₀ ++ q₁ ++ q₂ := by
    have hc3 : ch = 0 ∨ ch = 1 ∨ ch = 2 := by omega
    rcases hc3 with rfl | rfl | rfl
    · exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl hm)))
    · exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hm)))
    · exact List.mem_append.2 (Or.inr hm)
  have hbare : q'.bare ∈ allBare F ρ := by
    rw [← h.bare]
    exact List.mem_map.2 ⟨q', hmem, rfl⟩
  obtain ⟨w1, hw⟩ := h.words q' hmem
  have pk : ∀ c, pick3 (l₀ ++ t₀) (l₁ ++ t₁) (l₂ ++ t₂) c = pick3 l₀ l₁ l₂ c ++ pick3 t₀ t₁ t₂ c :=
      by
    intro c
    unfold pick3
    split
    · rfl
    · split <;> rfl
  refine ⟨hbare, fun i hi => ?_, fun c j hi hs => ?_⟩
  · have hi' : q'.item = some i := hi
    rcases hw with ⟨i', g1, -, g3⟩ | ⟨c, j, T, g1, -⟩
    · rw [g1] at hi'
      have e : i' = i := Option.some.inj hi'
      subst e
      show (stored i' q'.pos).isSome = true
      rw [← g3]
      exact w1
    · rw [g1] at hi'
      cases hi'
  · have hs' : q'.src = some (c, j) := hs
    rcases hw with ⟨i', g1, -, -⟩ | ⟨c', j', T, -, g2, g3, g4, -⟩
    · have hi' : q'.item = none := hi
      rw [g1] at hi'
      cases hi'
    · rw [g2] at hs'
      have e : (c', j') = (c, j) := Option.some.inj hs'
      have ec : c' = c := (Prod.mk.inj e).1
      have ej : j' = j := (Prod.mk.inj e).2
      subst ec
      subst ej
      rw [pk c'] at g4
      have hv : c' = ch ∨ ch = 2 := by
        by_cases h2 : ch = 2
        · exact Or.inr h2
        · exact Or.inl (hown h2 q' hm c' j' g2)
      refine ⟨g3, hv, fun T' hT' => ?_, fun hne => ?_⟩
      · have := tabs_front _ (pick3 t₀ t₁ t₂ c') j' T' hT'
        rw [this] at g4
        cases T' with
        | none => cases g4
        | some _ => rfl
      · have h2 : ch = 2 := by
          rcases hv with e | e
          · exact absurd e hne
          · exact e
        rw [hall h2 c' g3 hne, List.append_nil] at g4
        cases hg : (allTabs (pick3 l₀ l₁ l₂ c'))[j']? with
        | none =>
          rw [hg] at g4
          cases g4
        | some _ => rfl

end ProofFile.Honest

#print axioms ProofFile.Honest.src_of
#print axioms ProofFile.Honest.run_src
#print axioms ProofFile.Honest.tabs_front
#print axioms ProofFile.Honest.holds_run
