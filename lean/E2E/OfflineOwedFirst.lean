-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineOwedFirst.lean: what `Lettered.owedAt` (Johnson/Desc/ProofFile/Honest/Rule.lean) asks of a list
of the first chain at a run of `runC` that has returned, WITHOUT the invariants of a thread. General in
the description, the book, the prover and the lists. Conditional lemmas on the frame's own functions.

  `steps_half_rounds`   where `chainSteps` has returned, a half at a sub-protocol's place has that
                        sub-protocol's number of rounds
  `stands_of_steps`     `parts_stand_chain` (Honest/Law/StandsFile.lean) without its premise that every side
                        fits: of that premise it spends the number of rounds alone, which the steps give
  `first_stands`        every part of every list of the first chain is in one section of the chain's
                        steps and is given its carried blocks, at what `ready` has prepared
  `first_part_at_run`   at a run that has returned, at one part: the run's challenges and the positions
                        read of its tables are their closed forms in the draws; and where the part was
                        called, the book gives its carried blocks and `midAtW` returns a state
                        (`mid_first`, Honest/Law/RunMidFile.lean)
  `owedAt_first_of`     so `owedAt` at a list whose On holds everywhere comes to its `bud` at the run

Why. `owed_part_first` (Honest/Law/OwedParts.lean) takes `ThreadsP`, which it spends on On alone. At a list
whose On says nothing the thread is not needed.

Premises. The description's test on its plan; the book's own tests; the run has returned. No premise on any
simulator, and none on `Side.fits`. That a run returns is not shown here.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Law.StandsFile
import Johnson.Desc.ProofFile.Honest.Law.Rule.WalkLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open VerifiableInference.Desc

variable {Xi W₀ Rc Ky Tr X₀ X : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
  {H : Prover W₀ Rc Xi Ky Tr X₀ X} {G : Sides F Bk W₀ Rc Ky Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : Xi}
  {k : Coins Bk} {ρ : Draws} {r : RunC F}

section Chain
variable {S Cl V W Y Pb : Type}

/-- **Where `chainSteps` has returned, a half at a sub-protocol's place has its number of rounds**, and
the sub-protocol a list of oracle messages for each round. -/
theorem steps_half_rounds {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {v : Option V} {hs : List (Placed V W Y)} : ∀ (bs : List (Block S Cl)) (ss : List (Step W Y)),
    chainSteps B rows look v bs hs = .ok ss → ∀ b ∈ bs, ∀ g,
    (hs.find? fun g => g.place == b.place) = some g →
    g.rounds = b.rounds.length ∧ b.oracles.length = b.rounds.length
  | [], _, _, b, hb => by cases hb
  | b₀ :: bs, ss, h, b, hb => by
    obtain ⟨ho, l, hl, hcase⟩ := chainSteps_cons_ok h
    rcases List.mem_cons.1 hb with e | e
    · subst e
      intro g hg
      rcases hcase with ⟨h1, -⟩ | ⟨g', c, h1, h2, -⟩
      · rw [h1] at hg
        cases hg
      · obtain rfl : g' = g := Option.some.inj (h1.symm.trans hg)
        exact ⟨h2, ho⟩
    · exact steps_half_rounds bs l hl b e

/-- **Every part of every list of one chain is in one section of the chain's `Step`s, and is given its
carried blocks.** The text of `parts_stand_chain` (Honest/Law/StandsFile.lean), with the number of rounds
taken from the steps. -/
theorem stands_of_steps {Bk : ProverCoinCounts} {ch : Nat} {k : Coins Bk} {v : Option V}
    {bs : List (Block S Cl)} {Ls : List (Lettered Bk S Cl V W Y Pb)} {ss : List (Step W Y)}
    (hss : chainSteps Bk (Bk.rowsOf ch) (k.look ch) v bs
      (Ls.map fun M => (⟨M.place, M.row.map (·.1)⟩ : Placed V W Y)) = .ok ss)
    (hnd : (bs.map (·.place)).Nodup) (hLs : (Ls.map (·.place)).Nodup)
    (hcuts : ∀ a cs, Bk.cuts.lookup a = some cs → ∀ n ∈ cs, n ≠ 0) :
    ∀ L ∈ Ls, ∀ σ, L.side bs = some σ →
      ((σ.row.map (·.1.moves.length)).sum = σ.block.rounds.length ∧
        σ.block.oracles.length = σ.block.rounds.length) ∧
      ∀ u ∈ σ.members,
        (∃ pre t, StandsAt bs ss σ u pre t (σ.roundsTo u.number)) ∧
          ∃ ca, carriedAt Bk k ch ⟨L.place, u.number⟩ u.part = .ok ca := by
  intro L hL σ hσ
  obtain ⟨hb, hpl, hrow, -⟩ := seat_of_row hLs hL hσ
  have hg := find_row Ls hLs L hL
  rw [← hpl] at hg
  have hparts : (⟨σ.block.place, L.row.map (·.1)⟩ : Placed V W Y).parts = σ.row.map (·.1) := by
    rw [hrow]
  obtain ⟨hr, ho⟩ := steps_half_rounds bs ss hss σ.block hb _ hg
  have hr' : (σ.row.map (·.1.moves.length)).sum = σ.block.rounds.length := by
    unfold Placed.rounds at hr
    rw [foldl_moves, Nat.zero_add, List.map_map] at hr
    rw [hrow]
    exact hr
  have hsum : (σ.row.map (·.1.moves.length)).sum = (σ.block.rounds.zip σ.block.oracles).length := by
    rw [List.length_zip, ho, Nat.min_self]
    exact hr'
  refine ⟨⟨hr', ho⟩, fun u hu => ?_⟩
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

end Chain

/-- **Where the parts of the first chain's lists stand, and that they are given their carried
blocks**, of what `ready` has prepared; and each list has one move for each round of its sub-protocol. -/
theorem first_stands (plan : F.planOk = true) (book : Bk.word F = none)
    {R : Ready W₀ Rc Xi Ky Tr X₀ X} (hR : ready F Bk (G.prover H) w₀ rc x k = .ok R) :
    ∀ L ∈ G.first, ∀ σ, L.side F.first.blocksInOrder = some σ →
      ((σ.row.map (·.1.moves.length)).sum = σ.block.rounds.length ∧
        σ.block.oracles.length = σ.block.rounds.length) ∧
      ∀ u ∈ σ.members,
        (∃ pre t, StandsAt F.first.blocksInOrder R.first σ u pre t (σ.roundsTo u.number)) ∧
          ∃ ca, carriedAt Bk k 0 ⟨L.place, u.number⟩ u.part = .ok ca := by
  obtain ⟨ht, tr, -, -, -, s1, -, -⟩ := ready_ok hR
  obtain ⟨t1, -, -⟩ := tests_twice ht
  obtain ⟨n1, -, -⟩ := places_nodup ((F.planOk_ok).1 plan).places
  have r1 : (G.first.map (·.place)).Nodup := by
    have e := nodup_of_twice t1
    have e' : ((G.first.map fun L => (⟨L.place, L.row.map (·.1)⟩ :
        Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)).map (·.place)).Nodup := e
    rw [List.map_map] at e'
    exact e'
  exact stands_of_steps s1 n1 r1 (cuts_of book)

/-- **One part of a list of the first chain, at a run that has returned.** No invariant is taken. -/
theorem first_part_at_run (plan : F.planOk = true) (book : Bk.word F = none)
    (h : runC F Bk (G.prover H) w₀ rc x k ρ = .ok r)
    {L : Lettered Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi} (hL : L ∈ G.first)
    {σ : Side F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    (hσ : L.side F.first.blocksInOrder = some σ) {u : Member (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    (hu : u ∈ σ.members) :
    ((σ.row.map (·.1.moves.length)).sum = σ.block.rounds.length ∧
      σ.block.oracles.length = σ.block.rounds.length) ∧
    (∃ pre t, F.first.blocksInOrder = pre ++ σ.block :: t ∧
      r.run.drawnAt ⟨L.place, u.number⟩ =
        (ρ.first.drop ((pre.flatMap (·.rounds)).length + σ.roundsTo u.number)).take
          u.rounds.length ∧
      r.run.askedAt ⟨L.place, u.number⟩ =
        asksFrom (treeAsks F ρ 0) (u.rounds.map (·.2.length))
          (((rowsOfChain F.first.blocksInOrder).take
            ((pre.flatMap (·.rounds)).length + σ.roundsTo u.number)).map (·.2.length)).sum) ∧
      (r.called ⟨L.place, u.number⟩ = true → ∃ ca m,
        carriedAt Bk k 0 ⟨L.place, u.number⟩ u.part = .ok ca ∧
        orRefused (midAtW F Bk (G.prover H) w₀ rc x k ρ ⟨L.place, u.number⟩) = .ok m) := by
  obtain ⟨R, a₁, z₁, a₂, z₂, a₃, z₃, hR, -⟩ := runC_parts h
  have P := (F.planOk_ok).1 plan
  have hp := P.places
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  have o₁ := steps_shaped s1 P.blocks₁
  have o₂ := steps_shaped s2 P.blocks₂
  have o₃ := steps_shaped s3 P.blocks₃
  obtain ⟨hnum, hst⟩ := first_stands plan book hR L hL σ hσ
  obtain ⟨⟨pre, t, S⟩, ca, hca⟩ := hst u hu
  have hstr := S.str
  have hown := S.own
  rw [side_place hσ] at hstr
  obtain ⟨ha, htw, hfl, hseg⟩ := stretch_back hstr S.pos S.fits
  have hA := at_first h hR o₁ o₂ o₃ hp ha
  refine ⟨hnum, ⟨pre, t, S.cut, drawnAt_of hA hstr, ?_⟩, fun hc => ?_⟩
  · rw [askedAt_of hA hstr (treeAsks F ρ 0) (runC_asks h hR o₁ o₂ o₃ 0)]
    have e1 : ((R.first.drop ((pre.flatMap (·.rounds)).length + σ.roundsTo u.number)).take
        u.rounds.length).map (·.oracles.length) = u.rounds.map (·.2.length) := by
      have g := congrArg (List.map (·.2.length)) hown
      rw [List.map_map] at g
      exact g
    have e2 : (R.first.take ((pre.flatMap (·.rounds)).length + σ.roundsTo u.number)).map
        (·.oracles.length) = ((rowsOfChain F.first.blocksInOrder).take
          ((pre.flatMap (·.rounds)).length + σ.roundsTo u.number)).map (·.2.length) := by
      rw [← steps_pairs s1, ← List.map_take, List.map_map]
      rfl
    rw [e1, e2]
  · obtain ⟨m, hm, -⟩ := mid_first h hR o₁ o₂ o₃ hp ha hseg hc
    exact ⟨ca, m, hca, orRefused_some hm⟩

/-- **`owedAt` at a list of the first chain whose On holds everywhere comes to its `bud` at the run.**
`st`: the stored tables' columns, which On alone reads. -/
theorem owedAt_first_of (plan : F.planOk = true) (book : Bk.word F = none)
    (h : runC F Bk (G.prover H) w₀ rc x k ρ = .ok r)
    {L : Lettered Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi} (hL : L ∈ G.first)
    (st : List (Nat × Nat × List UInt64)) (hon : ∀ u ca m front, L.On u ca m front)
    (hbud : ∀ σ, L.side F.first.blocksInOrder = some σ → ∀ u ∈ σ.members,
      L.bud u.number (r.run.drawnAt ⟨L.place, u.number⟩) (r.run.askedAt ⟨L.place, u.number⟩)) :
    L.owedAt F.first.blocksInOrder k 0 (fun a => orRefused (midAtW F Bk (G.prover H) w₀ rc x k ρ a)) r.run st
      r.called := by
  intro σ hσ u hu
  refine ⟨hbud σ hσ u hu, fun hc => ?_⟩
  obtain ⟨ca, m, h1, h2⟩ := (first_part_at_run plan book h hL hσ hu).2.2 hc
  exact ⟨ca, m, h1, h2, hon _ _ _ _⟩

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.steps_half_rounds
#print axioms AtPublicFiles.OfflineRows.stands_of_steps
#print axioms AtPublicFiles.OfflineRows.first_stands
#print axioms AtPublicFiles.OfflineRows.first_part_at_run
#print axioms AtPublicFiles.OfflineRows.owedAt_first_of
