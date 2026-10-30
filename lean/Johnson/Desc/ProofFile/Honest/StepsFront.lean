-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/StepsFront.lean: how many rounds of a chain stand in front of the
first part of a place: where `chainSteps` (Frame.lean) returns, the places of the chain's
sub-protocols differ from that of one sub-protocol `b`, and a round stands at the address
`⟨b.place, 0⟩`: the rounds in front of that address are as many as the sub-protocols in front of `b`
declare. It is a step on the way from `midInW` (MidW.lean), which counts by the address, to
`fieldAt_walk` (FieldWalk.lean), which counts by the declared rounds.

  1  `Part.steps_addr`, `rowSteps_addr`   a part's rounds stand at its address; a list of parts'
     rounds stand at the place, at parts' numbers from `j` on
     `rowSteps_head`   **where a round stands at part number `j`, the first round does**: the parts'
     rounds come in the parts' order
  2  `steps_one_head`   the like for one sub-protocol, with a prover's side at its place or without
     `steps_place_mem`   each round stands at the place of one of the sub-protocols
  3  `chainSteps_split`   **a chain's rounds, cut at the first part of a place**
     `chainSteps_front`   the count, from it

By what, of others: `chainSteps_append` (Law/Cut.lean), `chainSteps_rows` (Law/Steps.lean),
`steps_one_none`, `steps_one_half` (Law/Thread.lean), `steps_decl` (Law/Run.lean), `exBind_ok`,
`exMap_ok` (Law/Play.lean).

Limits.
  * That the places differ is a hypothesis here; the description's own test on its places is not
    called.
  * The lemmas are about lists of rounds. They prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Cut
import Johnson.Desc.ProofFile.Honest.Law.Steps
import Johnson.Desc.ProofFile.Honest.Law.Thread
import Johnson.Desc.ProofFile.Honest.Law.Run

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place Oracle)

variable {S Cl V W X : Type}

/-! ## 1 A list of parts -/

theorem Part.steps_addr (p : Part V W X) (name : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (v : Option V) (c : p.Coins) :
    ∀ s ∈ p.steps name a rs v c, s.addr = a := by
  intro s hs
  unfold Part.steps at hs
  obtain ⟨r, -, rfl⟩ := List.mem_map.1 hs
  rfl

theorem rowSteps_addr (name : String) (a : Place) (v : Option V) :
    ∀ (ps : List (Part V W X)) (j : Nat) (rs : List (Fmt.DeclaredRound × List Oracle))
      (c : RowCoins ps), ∀ s ∈ rowSteps name a v ps j rs c, s.addr.place = a ∧ j ≤ s.addr.part
  | [], _, _, _, s, hs => by simp [rowSteps] at hs
  | p :: ps, j, rs, c, s, hs => by
    rw [rowSteps] at hs
    rcases List.mem_append.1 hs with h | h
    · rw [Part.steps_addr p name ⟨a, j⟩ _ v c.1 s h]
      exact ⟨rfl, Nat.le_refl j⟩
    · obtain ⟨h1, h2⟩ := rowSteps_addr name a v ps (j + 1) _ c.2 s h
      exact ⟨h1, by omega⟩

/-- **Where a round stands at part number `j`, the first round does.** -/
theorem rowSteps_head (name : String) (a : Place) (v : Option V) :
    ∀ (ps : List (Part V W X)) (j : Nat) (rs : List (Fmt.DeclaredRound × List Oracle))
      (c : RowCoins ps), (∃ s ∈ rowSteps name a v ps j rs c, s.addr = ⟨a, j⟩) →
      ∃ s₀ l, rowSteps name a v ps j rs c = s₀ :: l ∧ s₀.addr = ⟨a, j⟩
  | [], _, _, _, ⟨s, hs, _⟩ => by simp [rowSteps] at hs
  | p :: ps, j, rs, c, ⟨s, hs, e⟩ => by
    rw [rowSteps] at hs ⊢
    cases hL : p.steps name ⟨a, j⟩ (rs.take p.moves.length) v c.1 with
    | nil =>
      rw [hL, List.nil_append] at hs
      have h2 := (rowSteps_addr name a v ps (j + 1) _ c.2 s hs).2
      rw [e] at h2
      have h3 : j + 1 ≤ j := h2
      omega
    | cons s₀ l =>
      refine ⟨s₀, l ++ rowSteps name a v ps (j + 1) (rs.drop p.moves.length) c.2, rfl, ?_⟩
      exact Part.steps_addr p name ⟨a, j⟩ _ v c.1 s₀ (by rw [hL]; simp)

/-! ## 2 One sub-protocol; a chain's places -/

section
variable {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d} {v : Option V}
  {hs : List (Placed V W X)}

/-- Where a round of one sub-protocol stands at its first part, its first round does. -/
theorem steps_one_head {b : Block S Cl} {l : List (Step W X)}
    (h : chainSteps B rows look v [b] hs = .ok l) (ha : ∃ s ∈ l, s.addr = ⟨b.place, 0⟩) :
    ∃ s₀ l', l = s₀ :: l' ∧ s₀.addr = ⟨b.place, 0⟩ := by
  cases hf : hs.find? (fun g => g.place == b.place) with
  | none =>
    obtain rfl := steps_one_none hf h
    obtain ⟨s, hm, -⟩ := ha
    unfold bareSteps at hm ⊢
    cases hz : b.rounds.zip b.oracles with
    | nil =>
      rw [hz] at hm
      simp at hm
    | cons r rs => exact ⟨_, _, rfl, rfl⟩
  | some g =>
    obtain ⟨c, -, rfl⟩ := steps_one_half hf h
    exact rowSteps_head b.name b.place v g.parts 0 _ c ha

/-- Each round that `chainSteps` prepares stands at the place of one of the sub-protocols. -/
theorem steps_place_mem {bs : List (Block S Cl)} {ss : List (Step W X)}
    (h : chainSteps B rows look v bs hs = .ok ss) :
    ∀ s ∈ ss, ∃ b ∈ bs, s.addr.place = b.place := by
  intro s hm
  have e := (chainSteps_rows bs hs ss h).2
  have hm' : (s.decl, s.oracles, s.addr.place, s.move.isSome) ∈
      ss.map (fun s => (s.decl, s.oracles, s.addr.place, s.move.isSome)) :=
    List.mem_map.2 ⟨s, hm, rfl⟩
  rw [e] at hm'
  obtain ⟨b, hb, hz⟩ := List.mem_flatMap.1 hm'
  obtain ⟨z, -, ez⟩ := List.mem_map.1 hz
  exact ⟨b, hb, (congrArg (fun y => y.2.2.1) ez).symm⟩

/-! ## 3 The count -/

/-- **A chain's rounds, cut at the first part of a place**: first the rounds of the sub-protocols in
front of `b`, as many as these declare, none at `b`'s place; then a round at `⟨b.place, 0⟩`. And
`b` declares a round.
CONDITIONAL: `chainSteps` returns; no other sub-protocol of the list stands at `b`'s place; a round
stands at `⟨b.place, 0⟩`. -/
theorem chainSteps_split {pre t : List (Block S Cl)} {b : Block S Cl} {ss : List (Step W X)}
    (h : chainSteps B rows look v (pre ++ b :: t) hs = .ok ss)
    (hp : ∀ b' ∈ pre, b'.place ≠ b.place) (ht : ∀ b' ∈ t, b'.place ≠ b.place)
    (ha : ss.any (fun s => s.addr == ⟨b.place, 0⟩) = true) :
    ∃ l₁ s₀ l', ss = l₁ ++ s₀ :: l' ∧ l₁.length = (pre.flatMap (·.rounds)).length ∧
      (∀ s ∈ l₁, s.addr.place ≠ b.place) ∧ s₀.addr = ⟨b.place, 0⟩ ∧ 0 < b.rounds.length := by
  rw [chainSteps_append] at h
  obtain ⟨l₁, h1, h⟩ := exBind_ok h
  obtain ⟨l₂, h2, rfl⟩ := exMap_ok h
  have h2' : chainSteps B rows look v ([b] ++ t) hs = .ok l₂ := h2
  rw [chainSteps_append] at h2'
  obtain ⟨lb, hb, h2'⟩ := exBind_ok h2'
  obtain ⟨lt, hlt, rfl⟩ := exMap_ok h2'
  have n1 : ∀ s ∈ l₁, s.addr.place ≠ b.place := by
    intro s hm ea
    obtain ⟨b', hb', e⟩ := steps_place_mem h1 s hm
    exact hp b' hb' (by rw [← e, ea])
  have nt : ∀ s ∈ lt, s.addr.place ≠ b.place := by
    intro s hm ea
    obtain ⟨b', hb', e⟩ := steps_place_mem hlt s hm
    exact ht b' hb' (by rw [← e, ea])
  obtain ⟨s, hm, es⟩ := List.any_eq_true.1 ha
  have es' : s.addr = ⟨b.place, 0⟩ := beq_iff_eq.1 es
  have ep : s.addr.place = b.place := by rw [es']
  have hin : s ∈ lb := by
    rcases List.mem_append.1 hm with h' | h'
    · exact absurd ep (n1 s h')
    · rcases List.mem_append.1 h' with h'' | h''
      · exact h''
      · exact absurd ep (nt s h'')
  obtain ⟨s₀, l', rfl, e0⟩ := steps_one_head hb ⟨s, hin, es'⟩
  have hl : l₁.length = (pre.flatMap (·.rounds)).length := by
    rw [← steps_decl h1, List.length_map]
  have hd := congrArg List.length (steps_decl hb)
  simp only [List.length_map, List.length_cons, List.flatMap_cons, List.flatMap_nil,
    List.append_nil] at hd
  exact ⟨l₁, s₀, l' ++ lt, rfl, hl, n1, e0, by omega⟩

/-- **The rounds in front of the first part of a place are as many as the sub-protocols in front of
it declare.** CONDITIONAL: as `chainSteps_split`. -/
theorem chainSteps_front {pre t : List (Block S Cl)} {b : Block S Cl} {ss : List (Step W X)}
    (h : chainSteps B rows look v (pre ++ b :: t) hs = .ok ss)
    (hp : ∀ b' ∈ pre, b'.place ≠ b.place) (ht : ∀ b' ∈ t, b'.place ≠ b.place)
    (ha : ss.any (fun s => s.addr == ⟨b.place, 0⟩) = true) :
    (ss.takeWhile fun s => s.addr != ⟨b.place, 0⟩).length = (pre.flatMap (·.rounds)).length := by
  obtain ⟨l₁, s₀, l', rfl, hl, n1, e0, -⟩ := chainSteps_split h hp ht ha
  have n1' : ∀ s ∈ l₁, (s.addr != ⟨b.place, 0⟩) = true := by
    intro s hm
    rw [bne_iff_ne]
    intro ea
    exact n1 s hm (by rw [ea])
  have hz : ((s₀ :: l').takeWhile fun s => s.addr != ⟨b.place, 0⟩) = [] := by
    rw [List.takeWhile_cons_of_neg]
    rw [e0]
    simp
  rw [List.takeWhile_append_of_pos n1', hz, List.append_nil, hl]

end

end ProofFile.Honest

#print axioms ProofFile.Honest.Part.steps_addr
#print axioms ProofFile.Honest.rowSteps_addr
#print axioms ProofFile.Honest.rowSteps_head
#print axioms ProofFile.Honest.steps_one_head
#print axioms ProofFile.Honest.steps_place_mem
#print axioms ProofFile.Honest.chainSteps_split
#print axioms ProofFile.Honest.chainSteps_front
