-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the simulators' door at the request's own test, on the last chain.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/DoorW.lean: the simulators' state on entry of a proximity test on the last chain (the
frame's chain number 2), as a function of a public description and of a Before alone, and the one equation that ties it to a
run. Twin of DoorTrue.lean, DoorStand.lean and DoorAtL.lean. At this test the fold has to start from the verifier's ends of
the two earlier chains, so the function remakes them from what the Before lists of these chains.

  `roundsOfChain`, `columnsOfChain`   what a Before shows of one chain; the columns that it lists for that chain's reads
  `withSealingRound`         the first chain's rounds as its fold takes them: its last round put back empty
  `firstChainEnd`, `sharedChainEnd`   the description's own folds over the two earlier chains, at what the Before lists
  `doorFromViewOnLastChain`, `stateFromViewOnLastChain`  the last chain's start at these ends, the fold over the blocks in front, the way in; its value or a fall-back
  `stateFromViewOnLastChain_reads`     **ONE FUNCTION OF PUBLIC DATA**: it reads the input through `F.pub` alone, and of the Before the rounds and
      columns named
  `pieces_front`     what a front in closed form shows of each chain
  `views_rounds`     the two earlier views' rounds
  `early_form`, `early_words`   a read of the two earlier chains finds its words in a front CUT AT ANY POINT OF THE LAST CHAIN: these
      chains lay their own trees alone, so what `views_back` (Law/Rule/Reads.lean) says at the whole last chain holds at the cut
  `stateFromViewOnLastChain_at_stand`  **THE EQUATION**: at a called part of the last chain, at the run's front cut back by i, `stateFromViewOnLastChain` is what the way in
      makes of the state that the run's own fold reaches, from the run's own two ends (at the seated description: DoorWAt.lean)

F is a public letter: the description. `stateFromViewOnLastChain` reads it as such, at every Before. WHERE THE FOLD REFUSES OR A COLUMN IS NOT LISTED THE
FALL-BACK IS TAKEN: at such a front the value is no state of the verifier. That the fold returns at a run's front is what
`stateFromViewOnLastChain_at_stand` says, under the premises of `called_at_second`.

Limits. No patch stands here: one function at every Before. No job at this test is typed: this is the door alone, with no law on what
a part shows. Nothing here shows that `ready` or `runC` returns, or that the part is called. Of the walk (runC). No property of the
protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.DoorTrue
import Johnson.Desc.ProofFile.Honest.K12.CalledAtSecond
import Johnson.Desc.ProofFile.Honest.K12.Sim.FrameAtSecond
import Johnson.Desc.ProofFile.Honest.Law.RunC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block OpenedColumn FileDescription foldBlocks Place withEmptySealRound)
open VerifiableInference.Desc.K12 (T12)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light

variable {Xi : Type}

/-! ## 1 The function -/

/-- What f shows of chain number ch, as a view shows rounds. -/
def roundsOfChain (f : Before) (ch : ℕ) : List Fmt.RoundView := roundsOff (f.rounds.filter fun r => r.1 == ch)

/-- The columns that f lists for the reads that the declared rounds of chain number ch make at the
challenges that f shows of that chain. -/
def columnsOfChain (f : Before) (ch ft : ℕ) (decls : List Fmt.DeclaredRound) : Option (List OpenedColumn) :=
  colsOff f (readsOf ch ft (fun _ _ => none) (fun _ => none) decls ((roundsOfChain f ch).map (·.drawn)))

/-- The first chain's rounds as its fold takes them. -/
def withSealingRound (rs : List Fmt.RoundView) : List Fmt.RoundView := rs.dropLast ++ [⟨[], ⟨[], [], [], none⟩⟩]

/-- The verifier's end of the first chain, at what f lists. -/
def firstChainEnd (F : FileDescription Xi) (x : Xi) (f : Before) : Option F.S₁ :=
  (columnsOfChain f 0 0 F.roundsDeclaredByBlocks.1).bind fun cs =>
    (foldBlocks 0 F.first.blocksInOrder (F.start₁ (F.pub x)) (withSealingRound (roundsOfChain f 0)) cs).toOption.map (·.1)

/-- The verifier's end of the shared chain, at what f lists. -/
def sharedChainEnd (F : FileDescription Xi) (x : Xi) (f : Before) : Option F.S₂ :=
  (columnsOfChain f 1 0 F.roundsDeclaredByBlocks.2.1).bind fun cs =>
    (foldBlocks 0 F.shared.blocksInOrder (F.start₂ (F.pub x)) (roundsOfChain f 1) cs).toOption.map (·.1)

/-- The last chain's start at these ends, the fold over the blocks in front, the way in. -/
def doorFromViewOnLastChain (F : FileDescription Xi) (pre : List (Block F.S₃ F.Cl)) (enter : F.S₃ → Except String T12) (x : Xi)
    (f : Before) : Except String T12 :=
  match firstChainEnd F x f, sharedChainEnd F x f, columnsOfChain f 2 F.lastChainFirstTreeNumber (pre.flatMap (·.rounds)) with
  | some e₁, some e₂, some cs =>
    (F.start₃ (F.pub x) e₁ e₂).bind fun v₀ =>
      (foldBlocks F.lastChainFirstTreeNumber pre v₀ (roundsOfChain f 2) cs).bind fun r => enter r.1
  | _, _, _ => .error "what the Before lists does not reach the test"

/-- **The simulators' state on entry.** F: the public description. -/
def stateFromViewOnLastChain (F : FileDescription Xi) (pre : List (Block F.S₃ F.Cl)) (enter : F.S₃ → Except String T12) (fall : T12)
    (x : Xi) (f : Before) : T12 :=
  (doorFromViewOnLastChain F pre enter x f).toOption.getD fall

/-- **It reads nothing else.** -/
theorem stateFromViewOnLastChain_reads (F : FileDescription Xi) (pre : List (Block F.S₃ F.Cl)) (enter : F.S₃ → Except String T12)
    (fall : T12) (x x' : Xi) (f f' : Before) (hx : F.pub x = F.pub x')
    (h0 : roundsOfChain f 0 = roundsOfChain f' 0) (h1 : roundsOfChain f 1 = roundsOfChain f' 1) (h2 : roundsOfChain f 2 = roundsOfChain f' 2)
    (c0 : columnsOfChain f 0 0 F.roundsDeclaredByBlocks.1 = columnsOfChain f' 0 0 F.roundsDeclaredByBlocks.1)
    (c1 : columnsOfChain f 1 0 F.roundsDeclaredByBlocks.2.1 = columnsOfChain f' 1 0 F.roundsDeclaredByBlocks.2.1)
    (c2 : columnsOfChain f 2 F.lastChainFirstTreeNumber (pre.flatMap (·.rounds)) =
      columnsOfChain f' 2 F.lastChainFirstTreeNumber (pre.flatMap (·.rounds))) :
    stateFromViewOnLastChain F pre enter fall x f = stateFromViewOnLastChain F pre enter fall x' f' := by
  unfold stateFromViewOnLastChain doorFromViewOnLastChain firstChainEnd sharedChainEnd
  rw [c0, c1, c2, hx, h0, h1, h2]

/-! ## 2 What a front shows -/

/-- What a front in closed form shows of each chain. -/
theorem pieces_front (F : FileDescription Xi) (ρ : Draws) (l₀ l₁ l₂ : List Played)
    (st : List (ℕ × ℕ × List UInt64)) :
    roundsOfChain ((laidOf F ρ l₀ l₁ l₂).front 2 st) 0 = roundsOf l₀ ∧
      roundsOfChain ((laidOf F ρ l₀ l₁ l₂).front 2 st) 1 = roundsOf l₁ ∧
      roundsOfChain ((laidOf F ρ l₀ l₁ l₂).front 2 st) 2 = roundsOf l₂ := by
  have e : ((laidOf F ρ l₀ l₁ l₂).front 2 st).rounds = shownBy 0 (treeAsks F ρ 0) l₀ 0 ++
      shownBy 1 (treeAsks F ρ 1) l₁ 0 ++ shownBy 2 (treeAsks F ρ 2) l₂ 0 := rfl
  unfold roundsOfChain
  rw [e]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.filter_append, List.filter_append, filter_same, filter_other (by decide),
      filter_other (by decide), List.append_nil, List.append_nil, roundsOff_by]
  · rw [List.filter_append, List.filter_append, filter_same, filter_other (by decide),
      filter_other (by decide), List.nil_append, List.append_nil, roundsOff_by]
  · rw [List.filter_append, List.filter_append, filter_same, filter_other (by decide),
      filter_other (by decide), List.nil_append, List.nil_append, roundsOff_by]

section
variable {W₀ Rc Ky Tr X₀ Y : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts} {P : Prover W₀ Rc Xi Ky Tr X₀ Y}
  {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws} {r : RunC F}

/-- The reads of the two earlier chains, at any third list: they lay their own trees alone. -/
theorem early_form (hrun : runC F Bk P w₀ rc x k ρ = .ok r) (l₂ : List Played) :
    ∀ q ∈ r.run.reads.1 ++ r.run.reads.2.1, q.words.isSome = true ∧
      ((∃ i, q.item = some i ∧ q.src = none ∧ q.words = P.storedWords w₀ rc i q.pos) ∨
        ∃ c j T, q.item = none ∧ q.src = some (c, j) ∧ c ≤ 2 ∧
          ((allTabs (pick3 r.run.played.1 r.run.played.2.1 l₂ c))[j]?).join = some T ∧
          q.words = some (T.col q.pos)) := by
  obtain ⟨R, a₁, z₁, a₂, z₂, a₃, z₃, hR, ha₁, hz₁, -, ha₂, hz₂, ha₃, hz₃, rfl⟩ := runC_parts hrun
  obtain ⟨-, tr, -, -, -, hs₁, hs₂, -⟩ := ready_ok hR
  have l1 := chainSteps_length _ _ hs₁
  have l2 := chainSteps_length _ _ hs₂
  have C1 := chained_of_start ha₁ hz₁ l1
  have C2 := chained_of_start ha₂ hz₂ l2
  obtain ⟨-, w1⟩ := words_of C1 rfl l1 (walk_length _ _ _ _ hz₁) z₁.laid z₂.laid l₂
    fun a b o pT e h => by
      obtain ⟨n, rfl, hn⟩ := own_tab a o pT h
      refine ⟨(show (0 : Nat) ≤ 2 by decide), ?_⟩
      show ((allTabs z₁.laid)[n]?).join = some pT.2
      have e' : z₁.laid = a ++ b := e
      rw [e']
      exact tabs_prefix a b n pT.2 hn
  obtain ⟨-, w2⟩ := words_of C2 rfl l2 (walk_length _ _ _ _ hz₂) z₁.laid z₂.laid l₂
    fun a b o pT e h => by
      obtain ⟨n, rfl, hn⟩ := own_tab a o pT h
      refine ⟨(show (1 : Nat) ≤ 2 by decide), ?_⟩
      show ((allTabs z₂.laid)[n]?).join = some pT.2
      have e' : z₂.laid = a ++ b := e
      rw [e']
      exact tabs_prefix a b n pT.2 hn
  intro q hq
  rcases List.mem_append.1 hq with hq | hq
  · exact w1 q hq
  · exact w2 q hq

/-- **A read of the two earlier chains finds its words in a front cut at any point of the last chain.** -/
theorem early_words (hrun : runC F Bk P w₀ rc x k ρ = .ok r) (l₂ : List Played) (q : Read)
    (hq : q ∈ r.run.reads.1 ++ r.run.reads.2.1) (w : List UInt64) (hqw : q.words = some w) :
    ((laidOf F ρ r.run.played.1 r.run.played.2.1 l₂).front 2
      (storedShown (P.storedWords w₀ rc) (storedAsks F ρ))).wordsAt q.bare = some w := by
  have hok := (runOk_of hrun).1
  have hb : q.bare ∈ allBare F ρ := by
    rw [← hok.bare]
    exact List.mem_map.2 ⟨q, List.mem_append.2 (Or.inl hq), rfl⟩
  obtain ⟨-, hform⟩ := early_form hrun l₂ q hq
  rcases hform with ⟨i, g1, -, g3⟩ | ⟨c, j, T, g1, g2, g3, g4, g5⟩
  · have hi : q.bare.item = some i := g1
    unfold Before.wordsAt
    rw [hi]
    show (((storedShown (P.storedWords w₀ rc) (storedAsks F ρ)).find? fun c =>
      c.1 == i && c.2.1 == q.pos).map (·.2.2)) = some w
    exact find_stored _ i q.pos w (g3.symm.trans hqw) _ (mem_storedAsks F ρ q.bare hb i hi)
  · have hi : q.bare.item = none := g1
    have hs : q.bare.src = some (c, j) := g2
    have hcols := treeCols_at F ρ r.run.played.1 r.run.played.2.1 l₂
      (storedShown (P.storedWords w₀ rc) (storedAsks F ρ)) c j g3
    have hget : (allTabs (pick3 r.run.played.1 r.run.played.2.1 l₂ c))[j]? = some (some T) := by
      cases hg : (allTabs (pick3 r.run.played.1 r.run.played.2.1 l₂ c))[j]? with
      | none =>
        rw [hg] at g4
        cases g4
      | some t =>
        rw [hg] at g4
        exact congrArg some g4
    rw [hget] at hcols
    have hwT : w = T.col q.pos := Option.some.inj (hqw.symm.trans g5)
    unfold Before.wordsAt
    rw [hi, hs]
    show ((((laidOf F ρ r.run.played.1 r.run.played.2.1 l₂).front 2
      (storedShown (P.storedWords w₀ rc) (storedAsks F ρ))).treeCols c j).bind fun cols =>
        (cols.find? fun c => c.1 == q.pos).map (·.2)) = some w
    rw [hcols, hwT]
    exact find_col T q.pos _ (mem_treeAsks F ρ q.bare hb _ _ hs)

/-- The two views' rounds. -/
theorem views_rounds (hrun : runC F Bk P w₀ rc x k ρ = .ok r) :
    r.run.views.1.rounds = (roundsOf r.run.played.1).dropLast ∧
      r.run.views.2.1.rounds = roundsOf r.run.played.2.1 := by
  obtain ⟨R, a₁, z₁, a₂, z₂, a₃, z₃, -, -, -, -, -, -, -, -, rfl⟩ := runC_parts hrun
  exact ⟨rfl, rfl⟩

end

/-! ## 3 The equation -/

/-- **One function on both sides.** -/
theorem stateFromViewOnLastChain_at_stand {W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (σ : Side F.S₃ F.Cl V (Local W₀ Rc Xi Tr) Y Pb) (u : Member V (Local W₀ Rc Xi Tr) Y Pb)
    (pre t : List (Block F.S₃ F.Cl)) (i : ℕ) (S : StandsAt F.second.blocksInOrder R.second σ u pre t i)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) (enter : F.S₃ → Except String T12) (fall : T12) :
    ∃ (e₁ : F.S₁) (e₂ : F.S₂) (v₀ s : F.S₃) (cols : List OpenedColumn),
      r.ends.1 = some e₁ ∧ r.ends.2.1 = some e₂ ∧ F.start₃ (F.pub x) e₁ e₂ = .ok v₀ ∧
      foldBlocks F.lastChainFirstTreeNumber pre v₀
        (roundsOf (r.run.played.2.2.take (pre.flatMap (·.rounds)).length)) cols = .ok (s, [], []) ∧
      stateFromViewOnLastChain F pre enter fall x
        ((r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
          ⟨σ.block.place, u.number⟩).cut i) = (enter s).toOption.getD fall := by
  obtain ⟨m, e₁, e₂, v₀, s, cols, more, rest, tr, -, -, -, -, he₁, he₂, hs₃, -, -, hfold, hfill⟩ :=
    called_at_second hpl hR σ u pre t i S hrun hc
  obtain ⟨m', -, -, -, -, -, hbf, -, -, -, hask⟩ := frame_at_second hpl hR hrun σ u pre t i _ S rfl hc
    (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
  have Q := (F.planOk_ok).1 hpl
  obtain ⟨-, -, -, -, -, s1, s2, s3⟩ := ready_ok hR
  obtain ⟨l1, l2, l3⟩ := runC_laidAs hrun hR (steps_shaped s1 Q.blocks₁) (steps_shaped s2 Q.blocks₂)
    (steps_shaped s3 Q.blocks₃)
  refine ⟨e₁, e₂, v₀, s, cols, he₁, he₂, hs₃, hfold, ?_⟩
  have d₀ : (roundsOf r.run.played.1).map (·.drawn) = ρ.first := by
    rw [← laidAs_drawn l1]
    simp only [roundsOf, List.map_map]
    rfl
  have d₁ : (roundsOf r.run.played.2.1).map (·.drawn) = ρ.shared := by
    rw [← laidAs_drawn l2]
    simp only [roundsOf, List.map_map]
    rfl
  have d₂ := laidAs_drawn l3
  have hall : r.run.played.2.2.length = R.second.length := by
    have h1 := congrArg List.length d₂
    rw [List.length_map] at h1
    exact h1.trans l3.1
  have hfits := S.fits
  have hn : (r.run.played.2.2.take ((pre.flatMap (·.rounds)).length + i)).length =
      (pre.flatMap (·.rounds)).length + i := by
    rw [List.length_take, hall]
    omega
  -- the front, cut back by i
  have hf : (r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
      ⟨σ.block.place, u.number⟩).cut i =
      (laidOf F ρ r.run.played.1 r.run.played.2.1
        (r.run.played.2.2.take (pre.flatMap (·.rounds)).length)).front 2
        (storedShown (P.storedWords w₀ rc) (storedAsks F ρ)) := by
    rw [hbf, hask]
    show (⟨shownBy 0 (treeAsks F ρ 0) r.run.played.1 0 ++ shownBy 1 (treeAsks F ρ 1) r.run.played.2.1 0 ++
      shownBy 2 (treeAsks F ρ 2) (r.run.played.2.2.take ((pre.flatMap (·.rounds)).length + i)) 0,
      storedShown (P.storedWords w₀ rc) (storedAsks F ρ)⟩ : Before).cut i =
      ⟨shownBy 0 (treeAsks F ρ 0) r.run.played.1 0 ++ shownBy 1 (treeAsks F ρ 1) r.run.played.2.1 0 ++
        shownBy 2 (treeAsks F ρ 2) (r.run.played.2.2.take (pre.flatMap (·.rounds)).length) 0,
        storedShown (P.storedWords w₀ rc) (storedAsks F ρ)⟩
    unfold Before.cut
    simp only
    have hC : (shownBy 2 (treeAsks F ρ 2)
        (r.run.played.2.2.take ((pre.flatMap (·.rounds)).length + i)) 0).length =
        (pre.flatMap (·.rounds)).length + i := by
      rw [shownBy_length, hn]
    have hk : (shownBy 0 (treeAsks F ρ 0) r.run.played.1 0 ++
        shownBy 1 (treeAsks F ρ 1) r.run.played.2.1 0 ++
        shownBy 2 (treeAsks F ρ 2) (r.run.played.2.2.take ((pre.flatMap (·.rounds)).length + i)) 0).length - i =
        (shownBy 0 (treeAsks F ρ 0) r.run.played.1 0 ++
          shownBy 1 (treeAsks F ρ 1) r.run.played.2.1 0).length + (pre.flatMap (·.rounds)).length := by
      rw [List.length_append, hC]
      omega
    rw [hk, List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left,
      ← shownBy_take, List.take_take]
    simp
  have Pc := pieces_front F ρ r.run.played.1 r.run.played.2.1
    (r.run.played.2.2.take (pre.flatMap (·.rounds)).length)
    (storedShown (P.storedWords w₀ rc) (storedAsks F ρ))
  obtain ⟨hok, f₀, f₁, -⟩ := runOk_of hrun
  obtain ⟨E₁, E₂, -⟩ := runC_ends hrun
  obtain ⟨v₁, v₂⟩ := views_rounds hrun
  rw [hf]
  -- the two earlier chains
  have hfirst : firstChainEnd F x ((laidOf F ρ r.run.played.1 r.run.played.2.1
      (r.run.played.2.2.take (pre.flatMap (·.rounds)).length)).front 2
      (storedShown (P.storedWords w₀ rc) (storedAsks F ρ))) = some e₁ := by
    have c0 : columnsOfChain ((laidOf F ρ r.run.played.1 r.run.played.2.1
        (r.run.played.2.2.take (pre.flatMap (·.rounds)).length)).front 2
        (storedShown (P.storedWords w₀ rc) (storedAsks F ρ))) 0 0 F.roundsDeclaredByBlocks.1 =
        some r.run.views.1.opened := by
      unfold columnsOfChain
      rw [Pc.1, d₀]
      have kk := colsOff_fill _ r.run.reads.1 _ f₀ fun q hq w hw =>
        early_words hrun (r.run.played.2.2.take (pre.flatMap (·.rounds)).length) q
          (List.mem_append.2 (Or.inl hq)) w hw
      rw [hok.bare₀] at kk
      exact kk
    unfold firstChainEnd
    rw [c0, Pc.1]
    have hv : withSealingRound (roundsOf r.run.played.1) = (withEmptySealRound r.run.views.1).rounds := by
      show _ = r.run.views.1.rounds ++ _
      rw [v₁]
      rfl
    rw [hv]
    show (foldBlocks 0 F.first.blocksInOrder (F.start₁ (F.pub x)) (withEmptySealRound r.run.views.1).rounds
      r.run.views.1.opened).toOption.map (·.1) = _
    rw [← E₁.2.2, he₁]
  have hshared : sharedChainEnd F x ((laidOf F ρ r.run.played.1 r.run.played.2.1
      (r.run.played.2.2.take (pre.flatMap (·.rounds)).length)).front 2
      (storedShown (P.storedWords w₀ rc) (storedAsks F ρ))) = some e₂ := by
    have c1 : columnsOfChain ((laidOf F ρ r.run.played.1 r.run.played.2.1
        (r.run.played.2.2.take (pre.flatMap (·.rounds)).length)).front 2
        (storedShown (P.storedWords w₀ rc) (storedAsks F ρ))) 1 0 F.roundsDeclaredByBlocks.2.1 =
        some r.run.views.2.1.opened := by
      unfold columnsOfChain
      rw [Pc.2.1, d₁]
      have kk := colsOff_fill _ r.run.reads.2.1 _ f₁ fun q hq w hw =>
        early_words hrun (r.run.played.2.2.take (pre.flatMap (·.rounds)).length) q
          (List.mem_append.2 (Or.inr hq)) w hw
      rw [hok.bare₁] at kk
      exact kk
    unfold sharedChainEnd
    rw [c1, Pc.2.1, ← v₂]
    show (foldBlocks 0 F.shared.blocksInOrder (F.start₂ (F.pub x)) r.run.views.2.1.rounds
      r.run.views.2.1.opened).toOption.map (·.1) = _
    rw [← E₂.2.2, he₂]
  -- the last chain's blocks in front
  have hdecl : pre.flatMap (·.rounds) = F.roundsDeclaredByBlocks.2.2.take (pre.flatMap (·.rounds)).length := by
    show _ = (F.second.blocksInOrder.flatMap (·.rounds)).take _
    rw [S.cut, List.flatMap_append]
    simp
  have hdr : (r.run.played.2.2.take (pre.flatMap (·.rounds)).length).map (·.drawn) =
      ρ.second.take (pre.flatMap (·.rounds)).length := by
    rw [List.map_take, d₂]
  have hc2 : columnsOfChain ((laidOf F ρ r.run.played.1 r.run.played.2.1
      (r.run.played.2.2.take (pre.flatMap (·.rounds)).length)).front 2
      (storedShown (P.storedWords w₀ rc) (storedAsks F ρ))) 2 F.lastChainFirstTreeNumber (pre.flatMap (·.rounds)) =
      some cols := by
    unfold columnsOfChain
    rw [Pc.2.2]
    have hd : (roundsOf (r.run.played.2.2.take (pre.flatMap (·.rounds)).length)).map (·.drawn) =
        (r.run.played.2.2.take (pre.flatMap (·.rounds)).length).map (·.drawn) := by
      simp only [roundsOf, List.map_map]
      rfl
    rw [hd, ← readsOf_bare 2 F.lastChainFirstTreeNumber (P.storedWords w₀ rc)
      (treeThird r.run.played.1 r.run.played.2.1
        (r.run.played.2.2.take (pre.flatMap (·.rounds)).length))]
    refine colsOff_fill _ _ cols hfill fun q hq w hw => ?_
    have hb : q.bare ∈ allBare F ρ := by
      have h2 : q.bare ∈ readsOf 2 F.lastChainFirstTreeNumber (fun _ _ => none) (fun _ => none)
          (pre.flatMap (·.rounds)) ((r.run.played.2.2.take (pre.flatMap (·.rounds)).length).map (·.drawn)) := by
        rw [← readsOf_bare 2 F.lastChainFirstTreeNumber (P.storedWords w₀ rc)
          (treeThird r.run.played.1 r.run.played.2.1
            (r.run.played.2.2.take (pre.flatMap (·.rounds)).length))]
        exact List.mem_map.2 ⟨q, hq, rfl⟩
      have h3 : q.bare ∈ readsOf 2 F.lastChainFirstTreeNumber (fun _ _ => none) (fun _ => none) F.roundsDeclaredByBlocks.2.2 ρ.second :=
        reads_of_prefix 2 F.lastChainFirstTreeNumber _ _ (pre.flatMap (·.rounds)).length F.roundsDeclaredByBlocks.2.2 ρ.second q.bare
          (by rw [← hdecl, ← hdr]; exact h2)
      unfold allBare bareReads
      exact List.mem_append.2 (Or.inr h3)
    exact faith_one F ρ _ _ _ (P.storedWords w₀ rc) 2 F.lastChainFirstTreeNumber _ _ _
      (fun o pT h => third_tab _ _ _ o pT h) q hq hb w hw
  unfold stateFromViewOnLastChain doorFromViewOnLastChain
  rw [hfirst, hshared, hc2]
  dsimp only
  rw [hs₃, Pc.2.2]
  show ((foldBlocks F.lastChainFirstTreeNumber pre v₀ _ cols).bind fun r => enter r.1).toOption.getD fall = _
  rw [hfold]
  rfl

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.roundsOfChain
#print axioms ProofFile.Honest.K12.Sim2.columnsOfChain
#print axioms ProofFile.Honest.K12.Sim2.firstChainEnd
#print axioms ProofFile.Honest.K12.Sim2.sharedChainEnd
#print axioms ProofFile.Honest.K12.Sim2.doorFromViewOnLastChain
#print axioms ProofFile.Honest.K12.Sim2.stateFromViewOnLastChain
#print axioms ProofFile.Honest.K12.Sim2.stateFromViewOnLastChain_reads
#print axioms ProofFile.Honest.K12.Sim2.pieces_front
#print axioms ProofFile.Honest.K12.Sim2.early_form
#print axioms ProofFile.Honest.K12.Sim2.early_words
#print axioms ProofFile.Honest.K12.Sim2.views_rounds
#print axioms ProofFile.Honest.K12.Sim2.stateFromViewOnLastChain_at_stand
