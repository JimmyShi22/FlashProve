-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/CalledFold.lean

What it proves. In one chain's walk of the frame's prover that asks the description's own step
(walk, ProofFile/Honest/Walk.lean; runC is three such walks): where the prover's run is still going
on behind the rounds of the blocks pre, the description's own fold over pre has returned, with
nothing left over, at the rounds produced and the columns filled so far (live_fold); so wherever the
walk produces a real round behind these rounds (called_fold). General in the state, the type of
claims and the chain.

Why it is so. After a rejection the walk calls no part: ChainProgress.settle lays mid := none, and every
later round is a fixed substitute, marked as made by no prover's side.

Names.
  cut_one   two cuts of one list of blocks, one of them in front of a block that has a round, are
      one cut where the counts of rounds agree.
  live_fold   at the stand: the walk over just pre's rounds, the prover's run going on.
  called_fold   from a real round behind.

By what, all of the frame's own laws (ProofFile/Honest/Law/): ChainProgress.Tied, ChainProgress.Open, start_tied,
walk_tied, roundsOf_length (WalkFold.lean); start_both, walk_both, fold_some (RunC.lean);
ChainProgress.ColsTied, start_colsT, walk_colsT (WalkCols.lean); told_live, walk_laid' (RunMid.lean);
walk_append_ok (Rule/WalkLaw.lean); walk_len (RunAtFile.lean); walk_grows (AcceptC.lean).

Limits.
- It is of the walk (runC), not of play (run). The frame's run plays with no verifier beside it and
  reaches stands at which the verifier would long have refused; there nothing is said here. What is
  had: at every stand at which a walk calls a part.
- Nothing on whether a walk returns, or calls a part.
- pre, v₀, the Lay and front₀ (the columns that ChainProgress.start is handed) are free: that they are a
  description's own, or a run's, is the caller's. The columns named in the conclusions are the
  walk's own field cols: front₀ is not laid into it.
- Steps of the frame's and of the verifier's: no property of a prover or a protocol. Nothing on
  completeness, on soundness or on what a view shows.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.Law.RunMidFile
import Johnson.Desc.ProofFile.Honest.Law.WalkCols
import Johnson.Desc.ProofFile.Honest.Law.RunC
import Johnson.Desc.ProofFile.Honest.Law.AcceptC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (Block OpenedColumn Place foldBlocks)
open ProofFile.Honest (Lay ChainProgress Mid Step Played Table walk roundsOf readsOf fillCols envOf)

/-- Where a list of blocks is cut in two ways, once in front of a block that has a round, and the
rounds in front of the other cut with k rounds more are as many as those in front of that block,
while k is less than what the block behind the other cut declares: the two cuts are one, and k is
0. -/
theorem cut_one {S Cl : Type} : ∀ (done todo pre : List (Block S Cl)) (b : Block S Cl)
    (t : List (Block S Cl)) (k : ℕ), done ++ todo = pre ++ b :: t → 0 < b.rounds.length →
    (done.flatMap (·.rounds)).length + k = (pre.flatMap (·.rounds)).length →
    (∀ b' t', todo = b' :: t' → k < b'.rounds.length) → done = pre ∧ k = 0
  | [], todo, [], b, t, k, _, _, h3, _ => ⟨rfl, by simpa using h3⟩
  | [], todo, p :: pre, b, t, k, h1, _, h3, h4 => by
    have e : todo = p :: (pre ++ b :: t) := h1
    have := h4 p _ e
    rw [List.flatMap_cons, List.length_append] at h3
    simp only [List.flatMap_nil, List.length_nil] at h3
    omega
  | d :: done, todo, [], b, t, k, h1, h2, h3, _ => by
    have e : d = b := (List.cons.inj h1).1
    rw [List.flatMap_cons, List.length_append, e] at h3
    simp only [List.flatMap_nil, List.length_nil] at h3
    omega
  | d :: done, todo, p :: pre, b, t, k, h1, h2, h3, h4 => by
    obtain ⟨e1, e2⟩ := List.cons.inj h1
    subst e1
    rw [List.flatMap_cons, List.flatMap_cons, List.length_append, List.length_append] at h3
    obtain ⟨rfl, hk⟩ := cut_one done todo pre b t k e2 h2 (by omega) h4
    exact ⟨rfl, hk⟩

/-- **At the stand.** The walk over just the rounds that pre declares has returned z₁, and the
prover's run is going on there. Then no round of the next block has been produced, that block is the
next to be asked, the verifier's state that the walk holds is what the fold over pre returns, with
nothing left over, at all rounds produced and all columns filled; and these columns are what
fillCols returns for pre's reads. -/
theorem live_fold {S Cl W Y : Type} (L : Lay) {taken : ℕ → ℕ → Option (Place × Table)}
    (hL : ∀ ps, L.tree ps = (envOf L.stored taken ps).tree) (pre : List (Block S Cl))
    (b : Block S Cl) (t : List (Block S Cl)) (hb : 0 < b.rounds.length) (m₀ : Mid W Y) (v₀ : S)
    {a z₁ : ChainProgress S Cl W Y} {ss₁ : List (Step W Y)} {ds₁ : List Fmt.Drawn} {front₀ : List OpenedColumn}
    (ha : ChainProgress.start L (pre ++ b :: t) (some m₀) (some v₀) front₀ = .ok a)
    (h1 : walk L ss₁ ds₁ a = .ok z₁) (hlen : ss₁.length = (pre.flatMap (·.rounds)).length)
    (hlive : z₁.mid.isSome = true) :
    ∃ s : S, z₁.ver = some s ∧ z₁.own = [] ∧ z₁.todo = b :: t ∧
      foldBlocks L.firstTree pre v₀ (roundsOf z₁.laid) z₁.cols = .ok (s, [], []) ∧
      fillCols (readsOf L.chain L.firstTree L.stored (L.tree z₁.laid) (pre.flatMap (·.rounds))
        (z₁.laid.map (·.drawn))) [] = .ok z₁.cols := by
  obtain ⟨T0, O0, l0⟩ := ProofFile.Honest.start_tied L _ (some m₀) (some v₀) ha
  obtain ⟨⟨done, front, c1, c2, c3, c4, c5⟩, O1, len1⟩ :=
    ProofFile.Honest.walk_tied L _ _ ss₁ ds₁ a z₁ T0 O0 h1
  have both := ProofFile.Honest.walk_both L ss₁ ds₁ a z₁ (ProofFile.Honest.start_both L _ _ _ ha) h1
  rw [l0, List.length_nil, Nat.zero_add, hlen] at len1
  have hsum : (done.flatMap (·.rounds)).length + z₁.own.length =
      (pre.flatMap (·.rounds)).length := by
    rw [← c3, ← len1, c2, List.length_append]
  obtain ⟨rfl, hk⟩ := cut_one done z₁.todo pre b t z₁.own.length c1.symm hb hsum O1
  have hown : z₁.own = [] := List.eq_nil_of_length_eq_zero hk
  have htodo : z₁.todo = b :: t := (List.append_cancel_left c1).symm
  rw [hown, List.append_nil] at c2
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 (both ▸ hlive)
  have c5' : (foldBlocks L.firstTree done v₀ (roundsOf front) z₁.cols).toOption.map (·.1) =
      some s := by
    rw [← hs, c5]
    rfl
  have hfold := (ProofFile.Honest.fold_some L.firstTree done v₀ s (roundsOf front) z₁.cols
    (by rw [ProofFile.Honest.roundsOf_length, c3]) c4).1 c5'
  obtain ⟨K0, W0⟩ := ProofFile.Honest.start_colsT (L := L) _ (some m₀) (some v₀) ha
  obtain ⟨⟨done', front', g1, g2, g3, g4⟩, W1⟩ :=
    ProofFile.Honest.walk_colsT hL _ ss₁ ds₁ a z₁ K0 W0 h1
  have hsum' : (done'.flatMap (·.rounds)).length + z₁.own.length =
      (done.flatMap (·.rounds)).length := by
    rw [← g3, ← len1, g2, List.length_append]
  obtain ⟨rfl, -⟩ := cut_one done' z₁.todo done b t z₁.own.length g1.symm hb hsum' W1
  rw [hown, List.append_nil] at g2
  rw [← g2] at g4
  rw [← c2] at hfold
  exact ⟨s, hs, hown, htodo, hfold, g4⟩

/-- **What "a real round was produced" gives of the verifier's side, in one chain's walk**
(ProofFile/Honest/Walk.lean). pre: the blocks in front of a block b that has a round. N: how many
rounds pre declares. Where the walk has returned and one of the rounds that it produced behind the
first N was made by a prover's side, the description's own fold over pre has returned, with nothing
left over, from the verifier's state at the chain's start, at the first N rounds produced and at
columns cols, which are what the frame's fillCols returns for pre's reads at the tables produced by
then, and with which the walk's columns begin.
Why: after a rejection the walk calls no part (ChainProgress.settle lays mid := none), so a real round behind
pre says that no block of pre has rejected.
hL: the Lay's look-up of a tree is that of envOf, as in the frame's own laws on a walk's columns.
It is of the walk (runC), not of play (run). -/
theorem called_fold {S Cl W Y : Type} (L : Lay) {taken : ℕ → ℕ → Option (Place × Table)}
    (hL : ∀ ps, L.tree ps = (envOf L.stored taken ps).tree) (pre : List (Block S Cl))
    (b : Block S Cl) (t : List (Block S Cl)) (hb : 0 < b.rounds.length) (m₀ : Mid W Y) (v₀ : S)
    {a z : ChainProgress S Cl W Y} {ss : List (Step W Y)} {ds : List Fmt.Drawn} {front₀ : List OpenedColumn}
    (ha : ChainProgress.start L (pre ++ b :: t) (some m₀) (some v₀) front₀ = .ok a)
    (hz : walk L ss ds a = .ok z)
    (ht : ∃ p ∈ z.laid.drop (pre.flatMap (·.rounds)).length, p.told = true) :
    ∃ (s : S) (cols more : List OpenedColumn),
      foldBlocks L.firstTree pre v₀ (roundsOf (z.laid.take (pre.flatMap (·.rounds)).length)) cols =
        .ok (s, [], []) ∧
      fillCols (readsOf L.chain L.firstTree L.stored
        (L.tree (z.laid.take (pre.flatMap (·.rounds)).length)) (pre.flatMap (·.rounds))
        ((z.laid.take (pre.flatMap (·.rounds)).length).map (·.drawn))) [] = .ok cols ∧
      z.cols = cols ++ more := by
  have hlen := ProofFile.Honest.walk_len L ss ds a z hz
  obtain ⟨-, -, l0⟩ := ProofFile.Honest.start_tied L _ (some m₀) (some v₀) ha
  obtain ⟨psAll, fAll, lAll⟩ := ProofFile.Honest.walk_laid' L ss ds a z hz
  rw [l0, List.nil_append] at fAll
  have hN : (pre.flatMap (·.rounds)).length ≤ ss.length := by
    by_contra hno
    obtain ⟨p, hp, -⟩ := ht
    rw [List.drop_eq_nil_of_le (by rw [fAll, lAll]; omega)] at hp
    cases hp
  have hz' : walk L (ss.take (pre.flatMap (·.rounds)).length ++
      ss.drop (pre.flatMap (·.rounds)).length) (ds.take (pre.flatMap (·.rounds)).length ++
      ds.drop (pre.flatMap (·.rounds)).length) a = .ok z := by
    rw [List.take_append_drop, List.take_append_drop]
    exact hz
  obtain ⟨z₁, h1, h2⟩ := ProofFile.Honest.walk_append_ok _ _ _ _ a z
    (by rw [List.length_take, List.length_take, hlen]) hz'
  obtain ⟨ps₁, f1, f1'⟩ := ProofFile.Honest.walk_laid' L _ _ a z₁ h1
  obtain ⟨ps₂, f2, -⟩ := ProofFile.Honest.walk_laid' L _ _ z₁ z h2
  rw [l0, List.nil_append] at f1
  have e1 : ps₁.length = (pre.flatMap (·.rounds)).length := by
    rw [f1', List.length_take, Nat.min_eq_left hN]
  have htake : z.laid.take (pre.flatMap (·.rounds)).length = z₁.laid := by
    rw [f2, f1, List.take_left' e1]
  have hdrop : z.laid.drop (pre.flatMap (·.rounds)).length = ps₂ := by
    rw [f2, f1, List.drop_left' e1]
  rw [hdrop] at ht
  have live₁ := ProofFile.Honest.told_live L _ _ z₁ z ps₂ h2 f2 ht
  obtain ⟨s, -, -, -, hfold, hfill⟩ := live_fold L hL pre b t hb m₀ v₀ ha h1
    (by rw [List.length_take, Nat.min_eq_left hN]) live₁
  obtain ⟨-, cs, -, hc⟩ := ProofFile.Honest.walk_grows L _ _ z₁ z h2
  rw [htake]
  exact ⟨s, z₁.cols, cs, hfold, hfill, hc⟩

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.cut_one
#print axioms ProofFile.Honest.K12.Light.live_fold
#print axioms ProofFile.Honest.K12.Light.called_fold
