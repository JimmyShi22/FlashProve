-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/LiveField.lean

What it proves. Which columns the field `opened` holds at a round, in one chain's walk
(Honest/Walk.lean). At a round of a block b: where the walk over the rounds that the blocks in
front, pre, declare and i more, i less than b declares, has returned z₁, and the prover's run is
going on there, at the state m: the field of m is `front`, the columns that the chain's start was
handed, and then cols, all the columns that the walk has filled so far; the description's own fold
over pre returns at the rounds produced for pre and at cols, with nothing left over; and cols are
what `fillCols` returns for pre's reads at the tables of the rounds produced for pre. The last two
clauses name no round of b: they are the first two of `called_fold` (CalledFold.lean in this
folder).

Names.
  walk_lengths      a walk that has returned had as many challenges as steps.
  walk_laid_prefix  the rounds produced only grow at their end.
  cut_at            two cuts of one list of blocks are one cut where the counts of rounds agree.
  live_field        the law.

By what. live_field goes as `live_fold` (CalledFold.lean) does, at every round of b and not at its
first alone; the list of the columns filled so far is given a name; and there is one clause more, on
the field: that clause is `walk_inv` at `start_inv` (Honest/WalkOpened.lean). cut_at names nothing
of the frame: it is `cut_one` (CalledFold.lean) with a number i of rounds behind the second cut. Of
the frame's authors, fifteen laws in all: `start_inv`, `walk_inv`, `walk_cols_prefix`
(Honest/WalkOpened.lean), `start_tied`, `walk_tied`, `roundsOf_length` (Honest/Law/WalkFold.lean),
`start_both`, `walk_both`, `fold_some` (Honest/Law/RunC.lean), `start_colsT`, `walk_colsT`
(Honest/Law/WalkCols.lean), `walk_nil_ok`, `walk_cons_ok`, `walk_append_ok`
(Honest/Law/Rule/WalkLaw.lean), `heard_laid` (Honest/Law/WalkOn.lean).

Limits.
- Of the walk (`runC`), not of `play`. m is the walk's state. `midAt`, `midSharedAt` and `run` hand
  a part no columns, and the laws at a run in this folder speak of their states: this file does not
  meet them. That join is not made here: it is the frame's authors'.
- The clause speaks of the field of `Mid`; a part is handed `m.shown`, whose field it is by
  definition.
- Nothing on whether a walk returns, or whether the prover's run is going on at any round.
- pre, v₀ and front are free. The `Lay` is free but for one premise, hL: its look-up of trees is
  `envOf`'s, at its own stored words and at some table `taken` of trees taken over. That these four
  are a description's own is the caller's. In the last chain the start's two states are options;
  here both are given.
- Of the steps ss₁ that the walk has gone over the law asks their number alone (hlen): that they are
  the steps of pre's rounds and of i rounds of b is not asked.
- It does not speak in the terms of `FieldAt` (Honest/Field.lean): that wants a tie between what the
  state has heard and what the rounds produced drew, which is not stated here.
- No test that can fail stands here: the four statements are general.
- It moves no count. No property of a prover or a protocol: nothing on completeness, on soundness or
  on what a view shows.

Terms: Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.WalkOpened
import Johnson.Desc.ProofFile.Honest.Law.WalkCols
import Johnson.Desc.ProofFile.Honest.Law.RunC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open VerifiableInference.Desc (Block OpenedColumn Place foldBlocks)
open ProofFile.Honest (Lay ChainProgress Mid Step Played Table walk roundsOf readsOf fillCols envOf)

/-- A walk that has returned had as many challenges as steps. (The frame's authors have it as
`walk_len`, Honest/Law/RunAtFile.lean; that file is not imported here.) -/
theorem walk_lengths {S Cl W Y : Type} (L : Lay) : ∀ (l : List (Step W Y)) (d : List Fmt.Drawn)
    (u u' : ChainProgress S Cl W Y), walk L l d u = .ok u' → d.length = l.length
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp [walk] at h
  | _ :: _, [], _, _, h => by simp [walk] at h
  | _ :: l, _ :: d, _, u', h => by
    obtain ⟨_, y, -, -, h'⟩ := ProofFile.Honest.walk_cons_ok h
    rw [List.length_cons, List.length_cons, walk_lengths L l d y u' h']

/-- The rounds produced only grow at their end. -/
theorem walk_laid_prefix {S Cl W Y : Type} (L : Lay) : ∀ (l : List (Step W Y))
    (d : List Fmt.Drawn) (u u' : ChainProgress S Cl W Y), walk L l d u = .ok u' → u.laid <+: u'.laid
  | [], [], u, u', h => by
    rw [ProofFile.Honest.walk_nil_ok h]
  | [], _ :: _, _, _, h => by simp [walk] at h
  | _ :: _, [], _, _, h => by simp [walk] at h
  | _ :: l, _ :: d, u, u', h => by
    obtain ⟨_, y, -, hy, h'⟩ := ProofFile.Honest.walk_cons_ok h
    have p := walk_laid_prefix L l d y u' h'
    rw [ProofFile.Honest.heard_laid hy] at p
    exact (List.prefix_append _ _).trans p

/-- Where a list of blocks is cut in two ways, once in front of a block b, and the rounds in front
of the other cut with k rounds more are as many as those in front of b with i more, while i is less
than what b declares and k is less than what the block behind the other cut declares: the two cuts
are one, and k is i. -/
theorem cut_at {S Cl : Type} : ∀ (done todo pre : List (Block S Cl)) (b : Block S Cl)
    (t : List (Block S Cl)) (k i : ℕ), done ++ todo = pre ++ b :: t → i < b.rounds.length →
    (done.flatMap (·.rounds)).length + k = (pre.flatMap (·.rounds)).length + i →
    (∀ b' t', todo = b' :: t' → k < b'.rounds.length) → done = pre ∧ k = i
  | [], todo, [], b, t, k, i, _, _, h3, _ => ⟨rfl, by simpa using h3⟩
  | [], todo, p :: pre, b, t, k, i, h1, _, h3, h4 => by
    have e : todo = p :: (pre ++ b :: t) := h1
    have := h4 p _ e
    rw [List.flatMap_cons, List.length_append] at h3
    simp only [List.flatMap_nil, List.length_nil] at h3
    omega
  | d :: done, todo, [], b, t, k, i, h1, h2, h3, _ => by
    have e : d = b := (List.cons.inj h1).1
    rw [List.flatMap_cons, List.length_append, e] at h3
    simp only [List.flatMap_nil, List.length_nil] at h3
    omega
  | d :: done, todo, p :: pre, b, t, k, i, h1, h2, h3, h4 => by
    obtain ⟨e1, e2⟩ := List.cons.inj h1
    subst e1
    rw [List.flatMap_cons, List.flatMap_cons, List.length_append, List.length_append] at h3
    obtain ⟨rfl, hk⟩ := cut_at done todo pre b t k i e2 h2 (by omega) h4
    exact ⟨rfl, hk⟩

/-- **At a round of a sub-protocol, with the field.** b is a block, pre the blocks in front of it,
and i is less than the number of rounds that b declares. The walk over the rounds that pre declares
and i more has returned z₁, and the prover's run is going on there, at the state m. Then i rounds of
b have been produced, b is the next block to be asked, the field of m is `front` and then all the
columns filled so far, the verifier's state that the walk holds is what the fold over pre returns,
with nothing left over, at the rounds produced for pre and these columns; and these columns are what
`fillCols` returns for pre's reads at the tables of the rounds produced for pre. No term of the last
two clauses names a round of b. hL: the `Lay`'s look-up of trees is `envOf`'s at some table `taken`.
hlen: the walk has gone over as many steps as pre declares rounds, and i more. -/
theorem live_field {S Cl W Y : Type} (L : Lay) {taken : ℕ → ℕ → Option (Place × Table)}
    (hL : ∀ ps, L.tree ps = (envOf L.stored taken ps).tree) (pre : List (Block S Cl))
    (b : Block S Cl) (t : List (Block S Cl)) (i : ℕ) (hi : i < b.rounds.length) (m₀ : Mid W Y)
    (v₀ : S) (front : List OpenedColumn) {a z₁ : ChainProgress S Cl W Y} {ss₁ : List (Step W Y)}
    {ds₁ : List Fmt.Drawn} (ha : ChainProgress.start L (pre ++ b :: t) (some m₀) (some v₀) front = .ok a)
    (h1 : walk L ss₁ ds₁ a = .ok z₁) (hlen : ss₁.length = (pre.flatMap (·.rounds)).length + i)
    {m : Mid W Y} (hm : z₁.mid = some m) :
    ∃ (s : S) (cols : List OpenedColumn), z₁.ver = some s ∧ z₁.own.length = i ∧ z₁.todo = b :: t ∧
      z₁.cols = cols ∧ m.opened = some (front ++ cols) ∧
      foldBlocks L.firstTree pre v₀ (roundsOf (z₁.laid.take (pre.flatMap (·.rounds)).length))
        cols = .ok (s, [], []) ∧
      fillCols (readsOf L.chain L.firstTree L.stored
        (L.tree (z₁.laid.take (pre.flatMap (·.rounds)).length)) (pre.flatMap (·.rounds))
        ((z₁.laid.take (pre.flatMap (·.rounds)).length).map (·.drawn))) [] = .ok cols := by
  have hb : 0 < b.rounds.length := Nat.lt_of_le_of_lt (Nat.zero_le i) hi
  have hdl := walk_lengths L ss₁ ds₁ a z₁ h1
  have hN : (pre.flatMap (·.rounds)).length ≤ ss₁.length := by omega
  have h1' : walk L (ss₁.take (pre.flatMap (·.rounds)).length ++ ss₁.drop (pre.flatMap
      (·.rounds)).length) (ds₁.take (pre.flatMap (·.rounds)).length ++ ds₁.drop (pre.flatMap
      (·.rounds)).length) a = .ok z₁ := by
    rw [List.take_append_drop, List.take_append_drop]
    exact h1
  obtain ⟨z₀, h0, h2⟩ := ProofFile.Honest.walk_append_ok _ _ _ _ a z₁
    (by rw [List.length_take, List.length_take, hdl]) h1'
  obtain ⟨T0, O0, l0⟩ := ProofFile.Honest.start_tied L _ (some m₀) (some v₀) ha
  obtain ⟨K0, W0⟩ := ProofFile.Honest.start_colsT (L := L) _ (some m₀) (some v₀) ha
  obtain ⟨⟨done, fr, c1, c2, c3, c4, c5⟩, O1, len1⟩ :=
    ProofFile.Honest.walk_tied L _ _ ss₁ ds₁ a z₁ T0 O0 h1
  obtain ⟨⟨dn, fr0, d1, d2, d3, d4, -⟩, P1, len0⟩ :=
    ProofFile.Honest.walk_tied L _ _ _ _ a z₀ T0 O0 h0
  obtain ⟨⟨dn', fr0', e1, e2, e3, e4⟩, Q1⟩ := ProofFile.Honest.walk_colsT hL _ _ _ a z₀ K0 W0 h0
  have both := ProofFile.Honest.walk_both L ss₁ ds₁ a z₁ (ProofFile.Honest.start_both L _ _ _ ha) h1
  rw [l0, List.length_nil, Nat.zero_add, hlen] at len1
  rw [l0, List.length_nil, Nat.zero_add, List.length_take, Nat.min_eq_left hN] at len0
  have s1 : (done.flatMap (·.rounds)).length + z₁.own.length = (pre.flatMap (·.rounds)).length + i
    := by rw [← c3, ← len1, c2, List.length_append]
  have s2 : (dn.flatMap (·.rounds)).length + z₀.own.length = (pre.flatMap (·.rounds)).length + 0 :=
    by rw [← d3, Nat.add_zero, ← len0, d2, List.length_append]
  have s3 : (dn'.flatMap (·.rounds)).length + z₀.own.length = (pre.flatMap (·.rounds)).length + 0 :=
    by rw [← e3, Nat.add_zero, ← len0, e2, List.length_append]
  obtain ⟨q1, hk⟩ := cut_at done z₁.todo pre b t z₁.own.length i c1.symm hi s1 O1
  obtain ⟨q2, hk0⟩ := cut_at dn z₀.todo pre b t z₀.own.length 0 d1.symm hb s2 P1
  obtain ⟨q3, -⟩ := cut_at dn' z₀.todo pre b t z₀.own.length 0 e1.symm hb s3 Q1
  have r1 := q1.symm
  have r2 := q2.symm
  have r3 := q3.symm
  subst r1 r2 r3
  have htodo : z₁.todo = b :: t := (List.append_cancel_left c1).symm
  have own0 : z₀.own = [] := List.eq_nil_of_length_eq_zero hk0
  rw [own0, List.append_nil] at d2 e2
  have tk : z₁.laid.take (pre.flatMap (·.rounds)).length = z₀.laid := by
    have p := List.prefix_iff_eq_take.1 (walk_laid_prefix L _ _ z₀ z₁ h2)
    rw [len0] at p
    exact p.symm
  have tk1 : z₁.laid.take (pre.flatMap (·.rounds)).length = fr := by
    rw [c2, List.take_left' c3]
  have efr : fr = z₀.laid := tk1.symm.trans tk
  have ec : z₀.cols = z₁.cols :=
    (ProofFile.Honest.walk_cols_prefix L _ _ z₀ z₁ h2).eq_of_length (by rw [d4, c4, efr, d2])
  have hlive : z₁.mid.isSome = true := by rw [hm]; rfl
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 (both ▸ hlive)
  have c5' : (foldBlocks L.firstTree pre v₀ (roundsOf fr) z₁.cols).toOption.map (·.1) =
      some s := by
    rw [← hs, c5]
    rfl
  have hfold := (ProofFile.Honest.fold_some L.firstTree pre v₀ s (roundsOf fr) z₁.cols
    (by rw [ProofFile.Honest.roundsOf_length, c3]) c4).1 c5'
  refine ⟨s, z₁.cols, hs, hk, htodo, rfl,
    ProofFile.Honest.walk_inv L front ss₁ ds₁ a z₁ (ProofFile.Honest.start_inv ha) h1 m hm, ?_, ?_⟩
  · rw [tk1]
    exact hfold
  · rw [tk, ← ec]
    rw [← e2] at e4
    exact e4

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.walk_lengths
#print axioms ProofFile.Honest.K12.walk_laid_prefix
#print axioms ProofFile.Honest.K12.cut_at
#print axioms ProofFile.Honest.K12.live_field
