-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/Stands.lean: where a part's rounds are in its chain, counted,
without a coin, from a `Member` of a list that is at a place: the chain's sub-protocols are those
before, the list's own, those after; the part's keys are one section of the chain's keys (`SegAt`,
Honest/Law/Rule/RowHere.lean), after as many keys as the sub-protocols before have rounds and the
list's parts before have moves; and the part's rounds are that section of its sub-protocol's.

  1  `flatMap_len`, `drop_take_mid`   on lists
  2  `row_stands`   a list of parts
  3  `keys_len`, `member_stands`   a chain
  4  `steps_stand`   the same of the chain's `Step`s, where they are prepared at a run's coins

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.OnTools
import Johnson.Desc.ProofFile.Honest.Law.Rule.CellLaws
import Johnson.Desc.ProofFile.Honest.Law.Rule.Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place Oracle)

variable {S Cl V W Y Pb : Type}

/-! ## 1 On lists -/

theorem flatMap_len {α β γ : Type} (f : α → List β) (g : α → List γ) : ∀ (l : List α),
    (∀ a ∈ l, (f a).length = (g a).length) → (l.flatMap f).length = (l.flatMap g).length
  | [], _ => rfl
  | a :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, List.length_append, List.length_append,
      h a (List.mem_cons.2 (Or.inl rfl)), flatMap_len f g l fun b hb => h b (List.mem_cons_of_mem _
          hb)]

/-- A section of the middle one of three concatenated lists. -/
theorem drop_take_mid {α : Type} (p m t : List α) (n len : Nat) (h : n + len ≤ m.length) :
    ((p ++ m ++ t).drop (p.length + n)).take len = (m.drop n).take len := by
  rw [List.append_assoc, List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
    show p.length + n - p.length = n by omega, List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by rw [List.length_drop]; omega)]

/-! ## 2 A list of parts -/

theorem row_stands (a : Place) : ∀ (row : List (Part V W Y × Sim Pb)) (j : Nat)
    (rs : List (Fmt.DeclaredRound × List Oracle)), (row.map (·.1.moves.length)).sum = rs.length →
    ∀ u ∈ membersOf row j rs, ∃ (n : Nat) (K₁ K₂ : List (Addr × Option (State W Y → Y))),
      rowKeys a (row.map (·.1)) j rs = K₁ ++ (u.rounds.zip u.part.moves).map
        (fun z => ((⟨a, u.number⟩ : Addr), some z.2.hand)) ++ K₂ ∧
      K₁.length = n ∧ (∀ q ∈ K₁, q.1 ≠ ⟨a, u.number⟩) ∧ (∀ q ∈ K₂, q.1 ≠ ⟨a, u.number⟩) ∧
      u.rounds = (rs.drop n).take u.part.moves.length ∧ n + u.part.moves.length ≤ rs.length ∧
      j ≤ u.number ∧ n = ((row.take (u.number - j)).map (·.1.moves.length)).sum
  | [], _, _, _, u, hu => by cases hu
  | q :: row, j, rs, hsum, u, hu => by
    simp only [List.map_cons, List.sum_cons] at hsum
    have hle : q.1.moves.length ≤ rs.length := by omega
    have htk : (rs.take q.1.moves.length).length = q.1.moves.length := by
      rw [List.length_take]
      omega
    have hkl : (((rs.take q.1.moves.length).zip q.1.moves).map fun z =>
        ((⟨a, j⟩ : Addr), some z.2.hand)).length = q.1.moves.length := by
      rw [List.length_map, List.length_zip, htk, Nat.min_self]
    have hk : rowKeys a ((q :: row).map (·.1)) j rs =
        ((rs.take q.1.moves.length).zip q.1.moves).map
          (fun z => ((⟨a, j⟩ : Addr), some z.2.hand)) ++
        rowKeys a (row.map (·.1)) (j + 1) (rs.drop q.1.moves.length) := by
      show rowKeys a (q.1 :: row.map (·.1)) j rs = _
      rw [rowKeys]
    rcases List.mem_cons.1 hu with e | e
    · subst e
      refine ⟨0, [], _, (by rw [hk]; rfl), rfl, (fun z hz => by cases hz), fun z hz e' => ?_, ?_,
        (by show 0 + q.1.moves.length ≤ rs.length; omega), Nat.le_refl j, ?_⟩
      · have := (rowKeys_mem a _ _ _ z hz).2
        rw [e'] at this
        exact Nat.lt_irrefl _ this
      · show rs.take q.1.moves.length = (rs.drop 0).take q.1.moves.length
        rw [List.drop_zero]
      · show 0 = (((q :: row).take (j - j)).map (·.1.moves.length)).sum
        rw [Nat.sub_self]
        rfl
    · obtain ⟨n, K₁, K₂, h1, h2, h3, h4, h5, h6, h7, h8⟩ := row_stands a row (j + 1)
        (rs.drop q.1.moves.length) (by rw [List.length_drop]; omega) u e
      rw [List.length_drop] at h6
      refine ⟨q.1.moves.length + n, ((rs.take q.1.moves.length).zip q.1.moves).map
        (fun z => ((⟨a, j⟩ : Addr), some z.2.hand)) ++ K₁, K₂, ?_, ?_, ?_, h4, ?_, (by omega),
        (by omega), ?_⟩
      · rw [hk, h1]
        simp only [List.append_assoc]
      · rw [List.length_append, hkl, h2]
      · intro z hz e'
        rcases List.mem_append.1 hz with hz | hz
        · obtain ⟨w, -, rfl⟩ := List.mem_map.1 hz
          have : j = u.number := congrArg Addr.part e'
          omega
        · exact h3 z hz e'
      · rw [h5, List.drop_drop]
      · have e1 : u.number - j = (u.number - (j + 1)) + 1 := by omega
        rw [e1, List.take_succ_cons, List.map_cons, List.sum_cons, ← h8]

/-! ## 3 A chain -/

/-- As many keys as rounds. -/
theorem keys_len {hs : List (Placed V W Y)} : ∀ (bs : List (Block S Cl)),
    (∀ b ∈ bs, (chainKeys [b] hs).length = b.rounds.length) →
    (chainKeys bs hs).length = (bs.flatMap (·.rounds)).length
  | [], _ => rfl
  | b :: bs, h => by
    rw [chainKeys_cons, List.length_append, List.flatMap_cons, List.length_append,
      h b (List.mem_cons.2 (Or.inl rfl)), keys_len bs fun b' hb' => h b' (List.mem_cons_of_mem _
          hb')]

/-- **From a `Member` of a side whose sub-protocol is in the chain and whose prover's side is the
chain's at that place.** -/
theorem member_stands {hs : List (Placed V W Y)} {bs : List (Block S Cl)}
    (hnd : (bs.map (·.place)).Nodup)
    (hkl : ∀ b ∈ bs, (chainKeys [b] hs).length = b.rounds.length) (σ : Side S Cl V W Y Pb)
    (hb : σ.block ∈ bs) {g : Placed V W Y}
    (hg : (hs.find? fun g => g.place == σ.block.place) = some g)
    (hparts : g.parts = σ.row.map (·.1))
    (hsum : (σ.row.map (·.1.moves.length)).sum = (σ.block.rounds.zip σ.block.oracles).length)
    (u : Member V W Y Pb) (hu : u ∈ σ.members) (hpos : u.part.moves.length ≠ 0) :
    ∃ (pre t : List (Block S Cl)) (n : Nat) (kp kq : List (Addr × Option (State W Y → Y))),
      bs = pre ++ σ.block :: t ∧
      SegAt (chainKeys bs hs) ⟨σ.block.place, u.number⟩ kp ((u.rounds.zip u.part.moves).map
        fun z => ((⟨σ.block.place, u.number⟩ : Addr), some z.2.hand)) kq ∧
      kp.length = (pre.flatMap (·.rounds)).length + n ∧
      u.rounds = ((σ.block.rounds.zip σ.block.oracles).drop n).take u.part.moves.length ∧
      n + u.part.moves.length ≤ (σ.block.rounds.zip σ.block.oracles).length ∧
      u.rounds.length = u.part.moves.length ∧
      n = ((σ.row.take u.number).map (·.1.moves.length)).sum := by
  obtain ⟨pre, t, rfl⟩ := List.append_of_mem hb
  obtain ⟨n, K₁, K₂, h1, h2, h3, h4, h5, h6, -, h8⟩ :=
    row_stands σ.block.place σ.row 0 _ hsum u hu
  have hkeys : chainKeys [σ.block] hs = rowKeys σ.block.place (σ.row.map (·.1)) 0
      (σ.block.rounds.zip σ.block.oracles) := by
    unfold chainKeys
    rw [List.flatMap_cons, hg, List.flatMap_nil, List.append_nil]
    show rowKeys σ.block.place g.parts 0 _ = _
    rw [hparts]
  have hlen : u.rounds.length = u.part.moves.length := by
    rw [h5, List.length_take, List.length_drop]
    omega
  rw [List.map_append, List.map_cons] at hnd
  have hnd' := List.nodup_append.1 hnd
  have hoff₁ : ∀ q ∈ chainKeys pre hs, q.1 ≠ ⟨σ.block.place, u.number⟩ := fun q hq e => by
    have h := chainKeys_mem hs pre q hq
    rw [e] at h
    exact hnd'.2.2 _ h _ (List.mem_cons.2 (Or.inl rfl)) rfl
  have hoff₂ : ∀ q ∈ chainKeys t hs, q.1 ≠ ⟨σ.block.place, u.number⟩ := fun q hq e => by
    have h := chainKeys_mem hs t q hq
    rw [e] at h
    exact (List.nodup_cons.1 hnd'.2.1).1 h
  refine ⟨pre, t, n, chainKeys pre hs ++ K₁, K₂ ++ chainKeys t hs, rfl, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_,
    h5, h6, hlen, h8⟩
  · rw [chainKeys_append, chainKeys_cons, hkeys, h1]
    simp only [List.append_assoc]
  · intro q hq
    rcases List.mem_append.1 hq with hq | hq
    · exact hoff₁ q hq
    · exact h3 q hq
  · intro q hq
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hq
    rfl
  · intro q hq
    rcases List.mem_append.1 hq with hq | hq
    · exact h4 q hq
    · exact hoff₂ q hq
  · intro e
    have := congrArg List.length e
    rw [List.length_map, List.length_zip, hlen, Nat.min_self] at this
    exact hpos this
  · rw [List.length_append, h2, keys_len pre fun b' hb' =>
      hkl b' (List.mem_append.2 (Or.inl hb'))]

/-! ## 4 The chain's `Step`s -/

/-- **The same of the chain's `Step`s.** -/
theorem steps_stand {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {v : Option V} {hs : List (Placed V W Y)} {bs : List (Block S Cl)} {ss : List (Step W Y)}
    (hss : chainSteps B rows look v bs hs = .ok ss) (hnd : (bs.map (·.place)).Nodup)
    (σ : Side S Cl V W Y Pb) (hb : σ.block ∈ bs) {g : Placed V W Y}
    (hg : (hs.find? fun g => g.place == σ.block.place) = some g)
    (hparts : g.parts = σ.row.map (·.1))
    (hsum : (σ.row.map (·.1.moves.length)).sum = (σ.block.rounds.zip σ.block.oracles).length)
    (u : Member V W Y Pb) (hu : u ∈ σ.members) (hpos : u.part.moves.length ≠ 0) :
    ∃ (pre t : List (Block S Cl)) (n : Nat), bs = pre ++ σ.block :: t ∧
      n + u.rounds.length ≤ σ.block.rounds.length ∧ 0 < u.rounds.length ∧
      InStretch ss ⟨σ.block.place, u.number⟩ ((pre.flatMap (·.rounds)).length + n)
        u.rounds.length ∧
      (((ss.drop ((pre.flatMap (·.rounds)).length + n)).take u.rounds.length).map
        fun s => (s.decl, s.oracles)) = u.rounds ∧
      n = ((σ.row.take u.number).map (·.1.moves.length)).sum := by
  have hf := chain_facts bs ss hss
  obtain ⟨pre, t, n, kp, kq, e, hseg, h1, h2, h3, h4, h5⟩ := member_stands hnd
    (fun b hb' => (hf b hb').2.1) σ hb hg hparts hsum u hu hpos
  obtain ⟨hin, -, -, -⟩ := hseg.steps (chainSteps_keys _ _ _ hss)
  have hzl : (σ.block.rounds.zip σ.block.oracles).length = σ.block.rounds.length := by
    rw [List.length_zip, (hf _ hb).1, Nat.min_self]
  have hkul : ((u.rounds.zip u.part.moves).map fun z =>
      ((⟨σ.block.place, u.number⟩ : Addr), some z.2.hand)).length = u.rounds.length := by
    rw [List.length_map, List.length_zip, h4, Nat.min_self]
  rw [h1, hkul] at hin
  refine ⟨pre, t, n, e, (by omega), (by omega), hin, ?_, h5⟩
  have hst := chain_states bs ss hss
  rw [List.map_take, List.map_drop, hst, e, List.flatMap_append, List.flatMap_cons,
    ← List.append_assoc]
  have hpl : (pre.flatMap (·.rounds)).length =
      (pre.flatMap fun b => b.rounds.zip b.oracles).length :=
    flatMap_len _ _ pre fun b hb' => by
      rw [List.length_zip, (hf b (by rw [e]; exact List.mem_append.2 (Or.inl hb'))).1,
        Nat.min_self]
  rw [hpl, drop_take_mid _ _ _ _ _ (by omega), h4]
  exact h2.symm

end ProofFile.Honest

#print axioms ProofFile.Honest.flatMap_len
#print axioms ProofFile.Honest.drop_take_mid
#print axioms ProofFile.Honest.row_stands
#print axioms ProofFile.Honest.keys_len
#print axioms ProofFile.Honest.member_stands
#print axioms ProofFile.Honest.steps_stand
