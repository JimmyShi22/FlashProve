-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/OpenedWalk.lean: `OpenedAt` (Honest/Law/Rule/OpenedAt.lean)
at the state that `midInW` (Honest/MidW.lean) returns in front of a part: the walk's own state. One
chain; general in the chain, in what `chainSteps` is given, and in the challenges
(`opened_at_chain`).

  1  `takeWhile_lt`, `prefix_eq`   on lists
  2  `chainSteps_count`   the rounds in front of a part are those of the sub-protocols in front of
     its place and fewer than its own sub-protocol has; beside `chainSteps_front`
     (Honest/StepsFront.lean): any part, not the first alone
  3  `opened_at_chain`   **the statement**

By what. What the field holds at a round of a sub-protocol: `live_field` (Honest/K12/LiveField.lean,
by that file's authors). What has been produced holds these columns: `HeldAt.grow`, `HeldAt.more`
(Honest/Law/Rule/OpenedStep.lean, OpenedAt.lean), `colsOff_fill` (Honest/Law/Rule/Faith.lean). The
proof's first lines go as those of `fieldAt_place` (Honest/TiePlace.lean).

Limits.
  * ONE CHAIN. Hypotheses that are paid in Honest/Law/Rule/OpenedRun.lean, not here: `hT` (`TieAt`
    at the chain's start) and `hW` (each read's words are found in what a simulator of the chain is
    given). Paid there too: `hL`, `hnd`, `hc`, `ha`, and `hw`: the walk over all the chain's steps
    returns, not only the one up to the part.
  * CONDITIONAL: nothing shows that `midInW` returns a state.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.OpenedStep
import Johnson.Desc.ProofFile.Honest.TiePlace
import Johnson.Desc.ProofFile.Honest.WalkHeard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block OpenedColumn Place)

/-! ## 1 On lists -/

theorem takeWhile_lt {α : Type} (p : α → Bool) : ∀ (l l' : List α), (∃ x ∈ l, p x = false) →
    ((l ++ l').takeWhile p).length < l.length
  | [], _, ⟨_, hx, _⟩ => by cases hx
  | y :: l, l', ⟨x, hx, hpx⟩ => by
    by_cases hy : p y = true
    · rw [List.cons_append, List.takeWhile_cons_of_pos hy, List.length_cons, List.length_cons]
      rcases List.mem_cons.1 hx with e | e
      · rw [e, hy] at hpx
        cases hpx
      · exact Nat.succ_lt_succ (takeWhile_lt p l l' ⟨x, e, hpx⟩)
    · rw [List.cons_append, List.takeWhile_cons_of_neg hy]
      exact Nat.succ_pos _

/-- Two stretches from the start of one list, equally long, are one. -/
theorem prefix_eq {α : Type} {l₁ l₂ l : List α} (h₁ : l₁ <+: l) (h₂ : l₂ <+: l)
    (hl : l₁.length = l₂.length) : l₁ = l₂ := by
  obtain ⟨r₁, e₁⟩ := h₁
  obtain ⟨r₂, e₂⟩ := h₂
  exact (List.append_inj (e₁.trans e₂.symm) hl).1

/-! ## 2 The count -/

section
variable {S Cl V W X : Type} {B : ProverCoinCounts} {rows : List (Addr × Due)}
  {look : Addr → (d : Due) × Cs d} {v : Option V} {hs : List (Placed V W X)}

/-- **The rounds in front of a part of `b`**: those of the sub-protocols in front of `b`, and fewer
than `b` declares. CONDITIONAL: `chainSteps` returns; no other sub-protocol of the list stands at
`b`'s place; a round stands at the address. -/
theorem chainSteps_count {pre t : List (Block S Cl)} {b : Block S Cl} {ss : List (Step W X)}
    (h : chainSteps B rows look v (pre ++ b :: t) hs = .ok ss)
    (hp : ∀ b' ∈ pre, b'.place ≠ b.place) (ht : ∀ b' ∈ t, b'.place ≠ b.place) {j : Nat}
    (ha : ss.any (fun s => s.addr == ⟨b.place, j⟩) = true) :
    ∃ i, i < b.rounds.length ∧ (ss.takeWhile fun s => s.addr != ⟨b.place, j⟩).length =
      (pre.flatMap (·.rounds)).length + i := by
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
  have es' : s.addr = ⟨b.place, j⟩ := beq_iff_eq.1 es
  have ep : s.addr.place = b.place := by rw [es']
  have hin : s ∈ lb := by
    rcases List.mem_append.1 hm with h' | h'
    · exact absurd ep (n1 s h')
    · rcases List.mem_append.1 h' with h'' | h''
      · exact h''
      · exact absurd ep (nt s h'')
  have hl : l₁.length = (pre.flatMap (·.rounds)).length := by
    rw [← steps_decl h1, List.length_map]
  have hd := congrArg List.length (steps_decl hb)
  simp only [List.length_map, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hd
  have n1' : ∀ s ∈ l₁, (s.addr != ⟨b.place, j⟩) = true := by
    intro s hm
    rw [bne_iff_ne]
    intro ea
    exact n1 s hm (by rw [ea])
  refine ⟨((lb ++ lt).takeWhile fun s => s.addr != ⟨b.place, j⟩).length, ?_, ?_⟩
  · rw [← hd]
    exact takeWhile_lt _ lb lt ⟨s, hin, by rw [es']; simp⟩
  · rw [List.takeWhile_append_of_pos n1', List.length_append, hl]

end

/-! ## 3 The statement -/

/-- **At the state that `midInW` returns in front of a part, the field is what that which has been
produced holds for the reads of the earlier chains and of the sub-protocols in front of the part's
place.** `earlier`: the earlier chains' declared rounds, as `preOf` (Honest/Rule.lean) takes them.
`st`, `tree`: the stored columns and the positions read, tree by tree. `Z₀`: what has been produced
before the chain. `lp`: the chain's rounds in front of the part. `hT`: `TieAt` at the chain's start.
`hW`: the words of each read of the sub-protocols from the chain's start on are found in what a
simulator of the chain is given, whatever rounds l the chain has produced. -/
theorem opened_at_chain {S Cl V W Y : Type} (L : Lay)
    {taken : Nat → Nat → Option (Place × Table)}
    (hL : ∀ ps, L.tree ps = (envOf L.stored taken ps).tree) (bs : List (Block S Cl))
    (hnd : (bs.map (·.place)).Nodup) (mo : Option (Mid W Y)) (vo : Option S) (front : List OpenedColumn)
    {a₀ z : ChainProgress S Cl W Y} {steps : List (Step W Y)} {ds : List Fmt.Drawn}
    {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d} {v : Option V}
    {hs : List (Placed V W Y)} (hc : chainSteps B rows look v bs hs = .ok steps)
    (ha : ChainProgress.start L bs mo vo front = .ok a₀) (hw : walk L steps ds a₀ = .ok z) {a : Addr}
    {m : Mid W Y} (hm : midInW L steps ds a₀ a = .ok (some m))
    (earlier : List (Nat × Nat × List Fmt.DeclaredRound)) (Z₀ : Laid)
    (st : List (Nat × Nat × List UInt64)) (tree : Nat → List Nat)
    (hT : ∀ m₀, mo = some m₀ → TieAt earlier L.chain L.firstTree []
      (some { m₀ with opened := some front }) (Z₀.front L.chain st))
    (hW : ∀ (l : List Played) (D rest : List Fmt.DeclaredRound), bs.flatMap (·.rounds) = D ++ rest →
      D.length ≤ ds.length →
      ∀ q ∈ readsOf L.chain L.firstTree L.stored (L.tree l) D (ds.take D.length), ∀ w,
        q.words = some w →
        ((Z₀.add L.chain (pairsBy tree l 0)).front L.chain st).wordsAt q.bare = some w)
    (lp : List Played) (hlp : lp <+: z.laid)
    (hll : lp.length = (steps.takeWhile fun s => s.addr != a).length) :
    OpenedAt (preOf L.chain L.firstTree earlier bs a.place) m
      ((Z₀.add L.chain (pairsBy tree lp 0)).front L.chain st) := by
  obtain ⟨p, j⟩ := a
  have hany : steps.any (fun s => s.addr == ⟨p, j⟩) = true := by
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
  have es' : s.addr = ⟨p, j⟩ := beq_iff_eq.1 es
  obtain ⟨b₁, hb₁, eb₁⟩ := steps_place_mem hc s hs'
  obtain ⟨pre, b, t, e1, -, rfl, e4⟩ := split_at_place p bs ⟨b₁, hb₁, by rw [← eb₁, es']⟩
  subst e1
  have ht : ∀ b' ∈ t, b'.place ≠ b.place := by
    intro b' hb' eq
    rw [List.map_append, List.map_cons] at hnd
    have h2 := (List.nodup_cons.1 hnd.of_append_right).1
    exact h2 (by rw [← eq]; exact List.mem_map.2 ⟨b', hb', rfl⟩)
  obtain ⟨i, hi, hn⟩ := chainSteps_count hc e4 ht hany
  -- the walk up to the part
  unfold midInW at hm
  simp only at hm
  split at hm
  · cases hm
  obtain ⟨z₁, h1, e⟩ := map_ok hm
  rw [hn] at h1 hll
  have hsl : (pre.flatMap (·.rounds)).length + i ≤ steps.length := by
    rw [← hn]
    exact (List.takeWhile_prefix _).length_le
  have hlen : (steps.take ((pre.flatMap (·.rounds)).length + i)).length =
      (pre.flatMap (·.rounds)).length + i := by
    rw [List.length_take, Nat.min_eq_left hsl]
  obtain ⟨sv, cols, -, -, -, -, ho, -, hf⟩ :=
    K12.live_field L hL pre b t i hi m₀ v₀ front ha h1 hlen e
  have hdl := K12.walk_lengths L _ _ a₀ z₁ h1
  rw [hlen, List.length_take] at hdl
  have hdr : z₁.laid.map (·.drawn) = ds.take ((pre.flatMap (·.rounds)).length + i) := by
    have h := walk_laid_drawn L _ _ a₀ z₁ h1
    rw [start_laid ha] at h
    exact h
  have hRs : (z₁.laid.take (pre.flatMap (·.rounds)).length).map (·.drawn) =
      ds.take (pre.flatMap (·.rounds)).length := by
    rw [List.map_take, hdr, List.take_take]
    congr 1
    omega
  rw [hRs] at hf
  -- the chain's rounds in front of the part are the walk's
  have hz : lp = z₁.laid := by
    obtain ⟨z₁', h1', hp'⟩ := walk_take hw ((pre.flatMap (·.rounds)).length + i)
    have ez : z₁' = z₁ := Except.ok.inj (h1'.symm.trans h1)
    rw [ez] at hp'
    refine prefix_eq hlp hp' ?_
    rw [hll, walk_laid_length L _ _ a₀ z₁ h1, start_laid ha, hlen]
    exact (Nat.zero_add _).symm
  rw [hz]
  -- what has been produced holds the columns: at the sub-protocol's start
  obtain ⟨cs, hcs, h0⟩ := (hT m₀ rfl).held _ rfl
  obtain rfl : front = cs := Option.some.inj hcs
  have hlev := (hT m₀ rfl).level
  have hgrow : HeldAt (earlier ++ [(L.chain, L.firstTree, [] ++ pre.flatMap (·.rounds))])
      ((Z₀.front L.chain st).more ((pairsBy tree (z₁.laid.take (pre.flatMap (·.rounds)).length)
          0).map
        fun y => (L.chain, y.1, y.2))) (front ++ cols) := by
    refine h0.grow _ (ds.take (pre.flatMap (·.rounds)).length) (hT m₀ rfl).early hlev ?_ ?_
    · rw [Before.drawnOf_own, pairs_drawn, hRs]
    · rw [← Laid.front_add, ← readsOf_bare L.chain L.firstTree L.stored
        (L.tree (z₁.laid.take (pre.flatMap (·.rounds)).length))]
      exact colsOff_fill _ _ _ hf (hW _ _ (b.rounds ++ t.flatMap (·.rounds)) (by simp) (by omega))
  rw [List.nil_append, ← Laid.front_add] at hgrow
  -- and at the part
  have h1' : ∀ y ∈ earlier ++ [(L.chain, L.firstTree, pre.flatMap (·.rounds))], y.2.2.length ≤
      (((Z₀.add L.chain (pairsBy tree (z₁.laid.take (pre.flatMap (·.rounds)).length) 0)).front
          L.chain
        st).drawnOf y.1).length := by
    intro y hy
    rw [Laid.front_add]
    rcases List.mem_append.1 hy with hy | hy
    · exact Nat.le_trans ((hT m₀ rfl).early y hy) (Before.drawnOf_more _ _ _).length_le
    · obtain rfl := List.mem_singleton.1 hy
      show (pre.flatMap (·.rounds)).length ≤ (((Z₀.front L.chain st).more _).drawnOf L.chain).length
      rw [Before.drawnOf_own, pairs_drawn, hRs, List.length_append, List.length_take]
      omega
  have hmore := hgrow.more ((pairsBy tree (z₁.laid.drop (pre.flatMap (·.rounds)).length)
    (0 + ((z₁.laid.take (pre.flatMap (·.rounds)).length).map (·.tables.length)).sum)).map
      fun y => (L.chain, y.1, y.2)) h1'
  rw [← Laid.front_add, Laid.add_add, ← pairsBy_append, List.take_append_drop] at hmore
  show OpenedAt (preOf L.chain L.firstTree earlier (pre ++ b :: t) b.place) m _
  rw [preOf_at L.chain L.firstTree earlier pre b t e4]
  exact OpenedAt.of_halves ho hmore

end ProofFile.Honest

#print axioms ProofFile.Honest.takeWhile_lt
#print axioms ProofFile.Honest.prefix_eq
#print axioms ProofFile.Honest.chainSteps_count
#print axioms ProofFile.Honest.opened_at_chain
