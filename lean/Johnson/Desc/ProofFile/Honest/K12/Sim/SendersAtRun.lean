-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/SendersAtRun.lean

A conditional: nothing here shows that ready or runC returns, that a part is called, or that a
filling holds these halves.

What a run of the frame's walking prover (`runC`) has played, in front of a called part of the
shared chain, at a sub-protocol whose half is a sending's part or the part at "SPLIT" of the authors
of the honest side of the linear claim's shared rounds (Honest/K14/): as terms of the coins that the
book lends that part, the input and the challenges heard. Two theorems, with two helpers.

  `at_of_cut`, `view_is_played`: helpers: an entry of a cut of a list; the shared view's rounds are
      the rounds as played.
  `sending_at_run`: a sending's two rounds: the tables (`sendTablesAt`); the items in the clear
      (`sendShownAt`); the shared view's second round.
  `split_at_run`: the one round at "SPLIT": the element `scalarAt`.

What for. Three of the six premises of `onFreeT_head_U_six` (OnFreeTAtHeadUSix.lean) speak of what
three rounds of the shared view hold. These two say what stands there, where the filling's halves
are those authors' own.

By what. `played_at_run` (Sim/PlayedAtRun.lean); `played_stretch` (Sim/PlayedStretch.lean); those
authors' `send_plays` (Honest/K14/SendingsPlay.lean) and `split_plays` (Honest/K14/PartsPlay.lean);
the frame's authors' `runC_parts` (Honest/Law/Rule/WalkLaw.lean); `play_lengths`
(Honest/Small/PlayRow.lean).

Limits.
- The step from these terms to the library's honest values (`answersAt`, `muRun`:
  Johnson/Desc/K14/Honest/) is not here: it asks that the sender's coded tables read as the honest
  rows.
- That the filling holds such a half (hg), and that b declares such rounds (hb, hf₀, hf₁; hd), are
  premises. The called part serves to have the walk in front of it; nothing ties its side to b but
  that b's rounds lie in front (hin).
- The sending's first round in the view is not stated. The shared chain alone. mb is the state that
  the walk named in the statement holds: from the start as `runC` lays it, over the prepared rounds
  in front of b. That `runC`'s own walk goes through that state is not said here; of a `play` from
  the chain's start nothing is said.
- A tie between terms: it names no value and states no law over random values. Nothing on
  completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.PlayedStretch
import Johnson.Desc.ProofFile.Honest.K12.Sim.PlayedAtRun
import Johnson.Desc.ProofFile.Honest.K14.SendingsPlay
import Johnson.Desc.ProofFile.Honest.K14.PartsPlay
import Johnson.Desc.ProofFile.Honest.Law.Rule.WalkLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes.Slice (toE)
open VerifiableInference.Desc (Block FileDescription Oracle)
open ProofFile.Honest
open ProofFile.Honest.Small (play_lengths)
open ProofFile.Honest.K14 (SendJob sendingPart sentTables answersOf Ask liftSend sendTablesAt sendShownAt
  playedBy send_plays Data liftK14 splitPart scalarAt split_plays)

/-- An entry of a cut of a list is the list's own. -/
theorem at_of_cut {α : Type} (l : List α) (N L j : ℕ) (hj : j < L) :
    ((l.drop N).take L)[j]? = l[N + j]? := by
  rw [List.getElem?_take_of_lt hj, List.getElem?_drop]

/-- The shared view's rounds are the rounds as played, each as a view shows it. -/
theorem view_is_played {Xi W₀ Rc Ky Tr X₀ Y : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {r : RunC F} (hrun : runC F Bk P w₀ rc x k ρ = .ok r) :
    r.run.views.2.1.rounds = roundsOf r.run.played.2.1 := by
  obtain ⟨R', a₁, z₁, a₂, z₂, a₃, z₃, -, -, -, -, -, -, -, -, e⟩ := runC_parts hrun
  rw [e]

/-- **A sending's two rounds, as a run has played them, in front of a called part of the shared
chain.** At a run of the walking prover at which a part of a side σ is called: where the shared
chain's flat list is cut as pre ++ b :: t, b declares a sending's two rounds, the prover's half at
b's place is the lifted sending's part of the job J, and both rounds lie in front of the called
part: there are the stand mb in front of b (the state that the shared chain's walk, from runC's own
start, holds in front of b), the values c that the book lends the sender, and the two challenges;
the first round as played holds the sender's tables and no item, the second the items `sendShownAt`
and no table; and the shared view's round there shows just these items. General in the description,
the book, the prover, the called part and the job. -/
theorem sending_at_run {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi}
    {Bk : ProverCoinCounts} {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk}
    {ρ : Draws} {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (σ : Side F.S₂ F.Cl V (Common W₀ Rc Ky) X₀ Pb) (u : Member V (Common W₀ Rc Ky) X₀ Pb)
    (pre' t' : List (Block F.S₂ F.Cl)) (i : ℕ)
    (S : StandsAt F.shared.blocksInOrder R.shared σ u pre' t' i)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true)
    (pre : List (Block F.S₂ F.Cl)) (b : Block F.S₂ F.Cl) (t : List (Block F.S₂ F.Cl))
    (hcut : F.shared.blocksInOrder = pre ++ b :: t) (J : SendJob)
    (wit : Common W₀ Rc Ky → Ask)
    (hg : (P.shared.find? fun g => g.place == b.place) =
      some ⟨b.place, [(liftSend wit (sendingPart J) : Part Empty (Common W₀ Rc Ky) X₀)]⟩)
    (d₀ d₁ : Fmt.DeclaredRound) (os : List Oracle)
    (hb : b.rounds.zip b.oracles = [(d₀, os), (d₁, [])])
    (hf₀ : ∀ L, ({ vals := [], tables := sentTables J.Q.codes J.Q.sent L } : Sending).fits d₀ os =
      true)
    (hf₁ : ∀ L seeds,
      ({ vals := (answersOf J.Q L seeds).map fun y => .answer (toE y.triple), tables := [] } :
        Sending).fits d₁ [] = true)
    (hin : (pre.flatMap (·.rounds)).length + 2 ≤ (pre'.flatMap (·.rounds)).length + i) :
    ∃ (a₂ zb : ChainProgress F.S₂ F.Cl (Common W₀ Rc Ky) X₀) (mb : ProofFile.Honest.Mid (Common W₀ Rc Ky) X₀)
      (c : RowCoins [(liftSend wit (sendingPart J) : Part Empty (Common W₀ Rc Ky) X₀)])
      (x₀ x₁ : Fmt.Drawn),
      ChainProgress.start ⟨1, 0, P.storedWords w₀ rc, treeOwn⟩ F.shared.blocksInOrder (some (R.start₂ P))
        (some (F.start₂ (F.pub x))) [] = .ok a₂ ∧
      walk ⟨1, 0, P.storedWords w₀ rc, treeOwn⟩ (R.shared.take (pre.flatMap (·.rounds)).length)
        (ρ.shared.take (pre.flatMap (·.rounds)).length) a₂ = .ok zb ∧
      zb.laid = r.run.played.2.1.take (pre.flatMap (·.rounds)).length ∧ zb.mid = some mb ∧
      lendRow Bk (Bk.rowsOf 1) (sharedLook Bk k.shared) b.place
        [(liftSend wit (sendingPart J) : Part Empty (Common W₀ Rc Ky) X₀)] 0 = .ok c ∧
      ρ.shared[(pre.flatMap (·.rounds)).length]? = some x₀ ∧
      ρ.shared[(pre.flatMap (·.rounds)).length + 1]? = some x₁ ∧
      r.run.played.2.1[(pre.flatMap (·.rounds)).length]? =
        some (playedBy b [] ((sendTablesAt J c.1.1 (wit mb.st.input) mb.st.heard).map some) x₀) ∧
      r.run.played.2.1[(pre.flatMap (·.rounds)).length + 1]? =
        some (playedBy b (sendShownAt J c.1.1 (wit mb.st.input) (mb.st.heard ++ [x₀])) [] x₁) ∧
      r.run.views.2.1.rounds[(pre.flatMap (·.rounds)).length + 1]? =
        some ⟨sendShownAt J c.1.1 (wit mb.st.input) (mb.st.heard ++ [x₀]), x₁⟩ := by
  obtain ⟨a₂, z, m, ha, hz, hzl, hzm, -⟩ := played_at_run hpl hR hrun σ u pre' t' i _ S rfl hc
  obtain ⟨c, hl, hst⟩ := played_stretch hR pre b t hcut _ hg _ a₂ z m ha hz hzm
  have hL : List.length _ = 2 := (play_lengths _ _ _ _ _ (send_plays J wit b d₀ d₁ os hb hf₀ hf₁
    (Face.shared.sees R.common) c m ⟨[], [], [], none⟩ ⟨[], [], [], none⟩)).symm
  obtain ⟨zb, mb, y, q1, q1l, q1m, q2, q3⟩ := hst (by rw [hL]; exact hin)
  rw [hL] at q2 q3
  rw [hzl] at q1l q3
  obtain ⟨x₀, x₁, ex⟩ := List.length_eq_two.1 ((play_lengths _ _ _ _ _ q2).trans hL)
  rw [ex, send_plays J wit b d₀ d₁ os hb hf₀ hf₁ (Face.shared.sees R.common) c mb x₀ x₁] at q2
  have ey : y.1 = _ := (congrArg Prod.fst (Except.ok.inj q2)).symm
  rw [ey] at q3
  have hN : (pre.flatMap (·.rounds)).length ≤ (pre'.flatMap (·.rounds)).length + i := by omega
  have t0 : ∀ j, j < 2 → r.run.played.2.1[(pre.flatMap (·.rounds)).length + j]? =
      ((((r.run.played.2.1.take ((pre'.flatMap (·.rounds)).length + i)).drop
        (pre.flatMap (·.rounds)).length).take 2))[j]? := by
    intro j hj
    rw [at_of_cut _ _ _ _ hj, List.getElem?_take_of_lt (by omega)]
  have p0 := t0 0 (by omega)
  have p1 := t0 1 (by omega)
  rw [← q3] at p0 p1
  have r0 := at_of_cut ρ.shared (pre.flatMap (·.rounds)).length 2 0 (by omega)
  have r1 := at_of_cut ρ.shared (pre.flatMap (·.rounds)).length 2 1 (by omega)
  rw [ex] at r0 r1
  rw [List.take_take, Nat.min_eq_left hN] at q1l
  refine ⟨a₂, zb, mb, c, x₀, x₁, ha, q1, q1l, q1m, hl, r0.symm, r1.symm, p0, p1, ?_⟩
  rw [view_is_played hrun]
  unfold roundsOf
  rw [List.getElem?_map, p1]
  rfl

/-- **The round at "SPLIT", as a run has played it, in front of a called part.** The like: b
declares one round with one element and no oracle message, and the prover's half at b's place is the
lifted part `splitPart`: the round as played, and the shared view's round there, hold the one
element `scalarAt` at the coin that the book lends that part and at the state mb that the walk over
the rounds in front of b holds. -/
theorem split_at_run {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi}
    {Bk : ProverCoinCounts} {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk}
    {ρ : Draws} {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (σ : Side F.S₂ F.Cl V (Common W₀ Rc Ky) X₀ Pb) (u : Member V (Common W₀ Rc Ky) X₀ Pb)
    (pre' t' : List (Block F.S₂ F.Cl)) (i : ℕ)
    (S : StandsAt F.shared.blocksInOrder R.shared σ u pre' t' i)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true)
    (pre : List (Block F.S₂ F.Cl)) (b : Block F.S₂ F.Cl) (t : List (Block F.S₂ F.Cl))
    (hcut : F.shared.blocksInOrder = pre ++ b :: t) (A : Data)
    (weights : W₀ → Weights)
    (hg : (P.shared.find? fun g => g.place == b.place) =
      some ⟨b.place, [(liftK14 A weights (splitPart A) : Part Empty (Common W₀ Rc Ky) X₀)]⟩)
    (d : Fmt.DeclaredRound) (hb : b.rounds.zip b.oracles = [(d, [])]) (hd : d.items = [.e])
    (hin : (pre.flatMap (·.rounds)).length + 1 ≤ (pre'.flatMap (·.rounds)).length + i) :
    ∃ (a₂ zb : ChainProgress F.S₂ F.Cl (Common W₀ Rc Ky) X₀) (mb : ProofFile.Honest.Mid (Common W₀ Rc Ky) X₀)
      (c : RowCoins [(liftK14 A weights (splitPart A) : Part Empty (Common W₀ Rc Ky) X₀)])
      (x₀ : Fmt.Drawn),
      ChainProgress.start ⟨1, 0, P.storedWords w₀ rc, treeOwn⟩ F.shared.blocksInOrder (some (R.start₂ P))
        (some (F.start₂ (F.pub x))) [] = .ok a₂ ∧
      walk ⟨1, 0, P.storedWords w₀ rc, treeOwn⟩ (R.shared.take (pre.flatMap (·.rounds)).length)
        (ρ.shared.take (pre.flatMap (·.rounds)).length) a₂ = .ok zb ∧
      zb.laid = r.run.played.2.1.take (pre.flatMap (·.rounds)).length ∧ zb.mid = some mb ∧
      lendRow Bk (Bk.rowsOf 1) (sharedLook Bk k.shared) b.place
        [(liftK14 A weights (splitPart A) : Part Empty (Common W₀ Rc Ky) X₀)] 0 = .ok c ∧
      ρ.shared[(pre.flatMap (·.rounds)).length]? = some x₀ ∧
      r.run.played.2.1[(pre.flatMap (·.rounds)).length]? =
        some (playedBy b [.e (OnBytes.Slice.ofE (scalarAt A c.1 (K14.askOf A weights mb.st)))] []
          x₀) ∧
      r.run.views.2.1.rounds[(pre.flatMap (·.rounds)).length]? =
        some ⟨[.e (OnBytes.Slice.ofE (scalarAt A c.1 (K14.askOf A weights mb.st)))], x₀⟩ := by
  obtain ⟨a₂, z, m, ha, hz, hzl, hzm, -⟩ := played_at_run hpl hR hrun σ u pre' t' i _ S rfl hc
  obtain ⟨c, hl, hst⟩ := played_stretch hR pre b t hcut _ hg _ a₂ z m ha hz hzm
  have hL : List.length _ = 1 := (play_lengths _ _ _ _ _ (split_plays A weights b d hb hd
    (Face.shared.sees R.common) c m ⟨[], [], [], none⟩)).symm
  obtain ⟨zb, mb, y, q1, q1l, q1m, q2, q3⟩ := hst (by rw [hL]; exact hin)
  rw [hL] at q2 q3
  rw [hzl] at q1l q3
  obtain ⟨x₀, ex⟩ := List.length_eq_one_iff.1 ((play_lengths _ _ _ _ _ q2).trans hL)
  rw [ex, split_plays A weights b d hb hd (Face.shared.sees R.common) c mb x₀] at q2
  have ey : y.1 = _ := (congrArg Prod.fst (Except.ok.inj q2)).symm
  rw [ey] at q3
  have hN : (pre.flatMap (·.rounds)).length ≤ (pre'.flatMap (·.rounds)).length + i := by omega
  have p0 : r.run.played.2.1[(pre.flatMap (·.rounds)).length + 0]? =
      ((((r.run.played.2.1.take ((pre'.flatMap (·.rounds)).length + i)).drop
        (pre.flatMap (·.rounds)).length).take 1))[0]? := by
    rw [at_of_cut _ _ _ _ (by omega), List.getElem?_take_of_lt (by omega)]
  rw [← q3] at p0
  have r0 := at_of_cut ρ.shared (pre.flatMap (·.rounds)).length 1 0 (by omega)
  rw [ex] at r0
  rw [List.take_take, Nat.min_eq_left hN] at q1l
  refine ⟨a₂, zb, mb, c, x₀, ha, q1, q1l, q1m, hl, r0.symm, p0, ?_⟩
  rw [view_is_played hrun]
  unfold roundsOf
  rw [List.getElem?_map]
  have p0' : r.run.played.2.1[(pre.flatMap (·.rounds)).length]? = _ := p0
  rw [p0']
  rfl

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.at_of_cut
#print axioms ProofFile.Honest.K12.Light.view_is_played
#print axioms ProofFile.Honest.K12.Light.sending_at_run
#print axioms ProofFile.Honest.K12.Light.split_at_run
