-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/StandsFile.lean: `PartsStand` (Honest/Law/OwedRule.lean) is
proved, once, generally; and the rule for `Owed` at a file without that hypothesis. Where `ready`
(Honest/Frame.lean) has returned, the description passes its tests on the plan, the book its own
(`ProverCoinCounts.word … = none`), every list of parts is at a place and every side fits: every part of every
list is in one section of its chain's `Step`s, after the rounds of the sub-protocols and of the
list's parts before it, and the book gives it its carried blocks. By `steps_stand`
(Honest/Law/Rule/Stands.lean) and `row_lent` (Honest/Law/Rule/Lends.lean).

What this is. Conditional lemmas on this folder's own functions, at parameters. The conclusion of
`owed_rule` is a definition of this folder, a structure of hypotheses: no property, and none of the
library's goals. The seven ways to meet it trivially are in the head of Honest/Law/OwedRule.lean,
and hold of it as of `owed_of_threads`.

  1  `find_row`, `members_part`   small lemmas
  2  `parts_stand_chain`   one chain
  3  `parts_stand`   a file
  4  `owed_rule`, `owed_rule_one`   the rule; the same where `ready` has returned once

Limits.
  * Among the hypotheses that the prose above does not name: `sealPlain` (the first chain's last
    declared round declares no item except roots, and no root): `owed_rule`, `owed_rule_one`.
  * `good` is asked in the plain form, at `earlierOf F` of each chain (Honest/Owed.lean), as in
    `owed_of_threads`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.OwedRule
import Johnson.Desc.ProofFile.Honest.Law.ReadyAny
import Johnson.Desc.ProofFile.Honest.Law.Cuts
import Johnson.Desc.ProofFile.Honest.Law.Rule.Stands
import Johnson.Desc.ProofFile.Honest.Law.Rule.Lends
import Johnson.Desc.ProofFile.Honest.Law.Rule.FileCells
import Johnson.Desc.ProofFile.Honest.Law.Rule.FileOkOf
import Johnson.Desc.ProofFile.Honest.Law.Rule.Has

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {Xi W₀ Rc Ky Tr X₀ X S Cl V W Y Pb : Type}

/-! ## 1 Small ones -/

theorem find_row {Bk : ProverCoinCounts} : ∀ (Ls : List (Lettered Bk S Cl V W Y Pb)),
    (Ls.map (·.place)).Nodup → ∀ L ∈ Ls,
    ((Ls.map fun M => (⟨M.place, M.row.map (·.1)⟩ : Placed V W Y)).find?
      fun g => g.place == L.place) = some ⟨L.place, L.row.map (·.1)⟩
  | [], _, _, hL => by cases hL
  | M :: Ls, hn, L, hL => by
    have hn' : (M.place :: Ls.map (·.place)).Nodup := hn
    obtain ⟨n1, n2⟩ := List.nodup_cons.1 hn'
    show (((⟨M.place, M.row.map (·.1)⟩ : Placed V W Y) ::
      Ls.map fun M => (⟨M.place, M.row.map (·.1)⟩ : Placed V W Y)).find?
      fun g => g.place == L.place) = _
    rcases List.mem_cons.1 hL with rfl | g
    · rw [List.find?_cons_of_pos (by exact beq_self_eq_true _)]
    · have hne : M.place ≠ L.place := fun e => n1 (by
        rw [e]
        exact List.mem_map.2 ⟨L, g, rfl⟩)
      rw [List.find?_cons_of_neg (by
        show ¬ ((M.place == L.place) = true)
        exact fun e => hne (beq_iff_eq.1 e))]
      exact find_row Ls n2 L g

theorem members_part : ∀ (row : List (Part V W Y × Sim Pb)) (j : Nat)
    (rs : List (Fmt.DeclaredRound × List Oracle)), ∀ u ∈ membersOf row j rs, (u.part, u.sim) ∈ row
  | [], _, _, _, hu => by cases hu
  | x :: row, j, rs, u, hu => by
    have hu' : u ∈ (⟨j, rs.take x.1.moves.length, x.1, x.2⟩ : Member V W Y Pb) ::
        membersOf row (j + 1) (rs.drop x.1.moves.length) := hu
    rcases List.mem_cons.1 hu' with rfl | g
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (members_part row (j + 1) _ u g)

/-! ## 2 One chain -/

/-- **Every part of every list of one chain is in one section of the chain's `Step`s, and is given
its carried blocks.** -/
theorem parts_stand_chain {Bk : ProverCoinCounts} {ch : Nat} {k : Coins Bk} {v : Option V}
    {bs : List (Block S Cl)} {Ls : List (Lettered Bk S Cl V W Y Pb)} {ss : List (Step W Y)}
    (hss : chainSteps Bk (Bk.rowsOf ch) (k.look ch) v bs
      (Ls.map fun M => (⟨M.place, M.row.map (·.1)⟩ : Placed V W Y)) = .ok ss)
    (hnd : (bs.map (·.place)).Nodup) (hLs : (Ls.map (·.place)).Nodup)
    (hseat : ∀ L ∈ Ls, ∃ σ, L.side bs = some σ ∧ σ.fits = true)
    (hcuts : ∀ a cs, Bk.cuts.lookup a = some cs → ∀ n ∈ cs, n ≠ 0) :
    ∀ L ∈ Ls, ∀ σ, L.side bs = some σ → ∀ u ∈ σ.members,
      (∃ pre t, StandsAt bs ss σ u pre t (σ.roundsTo u.number)) ∧
        ∃ ca, carriedAt Bk k ch ⟨L.place, u.number⟩ u.part = .ok ca := by
  intro L hL σ hσ u hu
  obtain ⟨hb, hpl, hrow, hso⟩ := seat_of_row hLs hL hσ
  have hg := find_row Ls hLs L hL
  rw [← hpl] at hg
  have hparts : (⟨σ.block.place, L.row.map (·.1)⟩ : Placed V W Y).parts = σ.row.map (·.1) := by
    rw [hrow]
  have hsum := row_sum hseat hso rfl
  have hmem : (u.part, u.sim) ∈ σ.row := members_part σ.row 0 _ u hu
  have hpos : u.part.moves.length ≠ 0 := by
    have hc := (chain_facts bs ss hss σ.block hb).2.2 _ hg
    refine hcuts _ _ hc _ ?_
    show u.part.moves.length ∈ (L.row.map (·.1)).map (·.moves.length)
    rw [← hrow]
    exact List.mem_map.2 ⟨u.part, List.mem_map.2 ⟨_, hmem, rfl⟩, rfl⟩
  obtain ⟨pre, t, n, hcut, hle, hp0, hstr, hown, hn⟩ :=
    steps_stand hss hnd σ hb hg hparts hsum u hu hpos
  have hn' : n = σ.roundsTo u.number := hn
  subst hn'
  refine ⟨⟨pre, t, hcut, hle, hp0, ?_, hstr, hown⟩, ?_⟩
  · have e := congrArg List.length hown
    rw [List.length_map, List.length_take, List.length_drop] at e
    omega
  · subst hcut
    have hss' : chainSteps Bk (Bk.rowsOf ch) (k.look ch) v (pre ++ ([σ.block] ++ t))
        (Ls.map fun M => (⟨M.place, M.row.map (·.1)⟩ : Placed V W Y)) = .ok ss := hss
    rw [chainSteps_append] at hss'
    obtain ⟨l₁, -, hss'⟩ := exBind_ok hss'
    obtain ⟨l₂, hl₂, -⟩ := exMap_ok hss'
    rw [chainSteps_append] at hl₂
    obtain ⟨lb, hlb, -⟩ := exBind_ok hl₂
    obtain ⟨c, hc, -⟩ := steps_one_half hg hlb
    have hu' : u ∈ membersOf L.row 0 (σ.block.rounds.zip σ.block.oracles) := by
      rw [← hrow]
      exact hu
    obtain ⟨c', hc'⟩ := row_lent L.row 0 (σ.block.rounds.zip σ.block.oracles) c hc u hu'
    refine ⟨c'.2.2, ?_⟩
    unfold carriedAt
    rw [← hpl, hc']
    rfl

/-! ## 3 A file -/

/-- **`PartsStand`, of what `ready` has prepared.** -/
theorem parts_stand {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    {G : Sides F Bk W₀ Rc Ky Tr X₀ X} (plan : F.planOk = true) (book : Bk.word F = none)
    (seats : G.seated = true)
    (good : (∀ L ∈ G.first,
        L.goodAt (earlierOf F 0) .own F.first.blocksInOrder (orderOf F) 0 0 G.falls₁) ∧
      (∀ L ∈ G.shared,
        L.goodAt (earlierOf F 1) .shared F.shared.blocksInOrder (orderOf F) 1 0 G.falls₂) ∧
      ∀ L ∈ G.second,
        L.goodAt (earlierOf F 2) .own F.second.blocksInOrder (orderOf F) 2 F.lastChainFirstTreeNumber G.falls₃)
    {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (hR : ready F Bk (G.prover H) w₀ rc x k = .ok R) : PartsStand G k R := by
  obtain ⟨ht, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  obtain ⟨t1, t2, t3⟩ := tests_twice ht
  obtain ⟨n1, n2, n3⟩ := places_nodup ((F.planOk_ok).1 plan).places
  have r1 : (G.first.map (·.place)).Nodup := by
    have e := nodup_of_twice t1
    have e' : ((G.first.map fun L => (⟨L.place, L.row.map (·.1)⟩ :
        Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)).map (·.place)).Nodup := e
    rw [List.map_map] at e'
    exact e'
  have r2 : (G.shared.map (·.place)).Nodup := by
    have e := nodup_of_twice t2
    have e' : ((G.shared.map fun L => (⟨L.place, L.row.map (·.1)⟩ :
        Placed Empty (Common W₀ Rc Ky) X₀)).map (·.place)).Nodup := e
    rw [List.map_map] at e'
    exact e'
  have r3 : (G.second.map (·.place)).Nodup := by
    have e := nodup_of_twice t3
    have e' : ((G.second.map fun L => (⟨L.place, L.row.map (·.1)⟩ :
        Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)).map (·.place)).Nodup := e
    rw [List.map_map] at e'
    exact e'
  unfold Sides.seated at seats
  simp only [Bool.and_eq_true, List.all_eq_true] at seats
  obtain ⟨⟨q1, q2⟩, q3⟩ := seats
  have hc := cuts_of book
  exact
    { at₁ := parts_stand_chain s1 n1 r1 (fun L hL => seat_fits (good.1 L hL) (q1 L hL)) hc
      at₂ := parts_stand_chain s2 n2 r2 (fun L hL => seat_fits (good.2.1 L hL) (q2 L hL)) hc
      at₃ := parts_stand_chain s3 n3 r3 (fun L hL => seat_fits (good.2.2 L hL) (q3 L hL)) hc }

/-! ## 4 The rule -/

/-- **The rule for `Owed` at a file**, with `PartsStand` proved. A conditional lemma on this
folder's own functions, at parameters. Its conclusion is a definition of this folder, a structure of
hypotheses: no property, and none of the library's goals. The seven ways to meet it trivially are in
the head of Honest/Law/OwedRule.lean. -/
theorem owed_rule {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    {G : Sides F Bk W₀ Rc Ky Tr X₀ X} {Rel : W₀ → Rc → Xi → Prop}
    (plan : F.planOk = true) (book : Bk.word F = none) (seats : G.seated = true)
    (hq : sealPlain F = true) (hroot : rootedAll F (G.prover H) = true)
    (good : (∀ L ∈ G.first,
        L.goodAt (earlierOf F 0) .own F.first.blocksInOrder (orderOf F) 0 0 G.falls₁) ∧
      (∀ L ∈ G.shared,
        L.goodAt (earlierOf F 1) .shared F.shared.blocksInOrder (orderOf F) 1 0 G.falls₂) ∧
      ∀ L ∈ G.second,
        L.goodAt (earlierOf F 2) .own F.second.blocksInOrder (orderOf F) 2 F.lastChainFirstTreeNumber G.falls₃)
    (input : ∀ w₀ rc x, Rel w₀ rc x → H.inRange w₀ = true ∧ (H.trace w₀ x).isSome = true)
    (hst : ∀ w₀ rc x, Rel w₀ rc x → ∀ d ∈ F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2, ∀ t ∈ d.stored,
      ∀ y, y < 2 ^ t.sh.a → ∃ u, H.storedWords w₀ rc t.item y = some u ∧ u.length = t.sh.W)
    (hready : ∀ w₀ rc x, Rel w₀ rc x → ∀ k, ∃ R, ready F Bk (G.prover H) w₀ rc x k = .ok R)
    (T : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      ThreadsP F Bk (G.prover H) w₀ rc x k R)
    (hbud : BudDebts F Bk G)
    (hon : ∀ w₀ rc x (hrel : Rel w₀ rc x) k R
      (hR : ready F Bk (G.prover H) w₀ rc x k = .ok R), OnDebts (T w₀ rc x hrel k R hR)) :
    Owed F Bk H G Rel :=
  owed_of_threads plan book seats hq hroot good input hst hready T
    (fun _ _ _ _ _ _ hR => parts_stand plan book seats good hR) hbud hon

/-- **The same, where `ready` has returned once**: at any one input and any one run's coins. -/
theorem owed_rule_one {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    {G : Sides F Bk W₀ Rc Ky Tr X₀ X} {Rel : W₀ → Rc → Xi → Prop}
    (plan : F.planOk = true) (book : Bk.word F = none) (seats : G.seated = true)
    (hq : sealPlain F = true) (hroot : rootedAll F (G.prover H) = true)
    (good : (∀ L ∈ G.first,
        L.goodAt (earlierOf F 0) .own F.first.blocksInOrder (orderOf F) 0 0 G.falls₁) ∧
      (∀ L ∈ G.shared,
        L.goodAt (earlierOf F 1) .shared F.shared.blocksInOrder (orderOf F) 1 0 G.falls₂) ∧
      ∀ L ∈ G.second,
        L.goodAt (earlierOf F 2) .own F.second.blocksInOrder (orderOf F) 2 F.lastChainFirstTreeNumber G.falls₃)
    (input : ∀ w₀ rc x, Rel w₀ rc x → H.inRange w₀ = true ∧ (H.trace w₀ x).isSome = true)
    (hst : ∀ w₀ rc x, Rel w₀ rc x → ∀ d ∈ F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2, ∀ t ∈ d.stored,
      ∀ y, y < 2 ^ t.sh.a → ∃ u, H.storedWords w₀ rc t.item y = some u ∧ u.length = t.sh.W)
    {w₁ : W₀} {rc₁ : Rc} {x₁ : Xi} {k₁ : Coins Bk} {R₁ : Ready W₀ Rc Xi Ky Tr X₀ X}
    (hone : ready F Bk (G.prover H) w₁ rc₁ x₁ k₁ = .ok R₁)
    (T : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      ThreadsP F Bk (G.prover H) w₀ rc x k R)
    (hbud : BudDebts F Bk G)
    (hon : ∀ w₀ rc x (hrel : Rel w₀ rc x) k R
      (hR : ready F Bk (G.prover H) w₀ rc x k = .ok R), OnDebts (T w₀ rc x hrel k R hR)) :
    Owed F Bk H G Rel :=
  owed_rule plan book seats hq hroot good input hst
    (fun w₀ rc x hrel k => ready_any hone (input w₀ rc x hrel).1 (input w₀ rc x hrel).2 k)
    T hbud hon

end ProofFile.Honest

#print axioms ProofFile.Honest.find_row
#print axioms ProofFile.Honest.members_part
#print axioms ProofFile.Honest.parts_stand_chain
#print axioms ProofFile.Honest.parts_stand
#print axioms ProofFile.Honest.owed_rule
#print axioms ProofFile.Honest.owed_rule_one
