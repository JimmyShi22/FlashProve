-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Small/DepthByPlay.lean: the table that a `Thread`
(Honest/Thread/Thr.lean) names for one of its chain's own trees has the depth that the sub-protocol
states for that tree. Shown for a `Thread` whose field `table` is `tableBy` (PlayedTo.lean: the
table that the frame's own `play` sends), at a state m of the prover's run that `play` returns over
the first n sub-protocols (`PlayedTo T start n k m`), for every tree that these n sub-protocols
state. General in the `Thread` and in the prover: no kind of sub-protocol and no description is
named.

  `statedTo bs n`: a definition: the oracle messages that the first n sub-protocols of bs state, in
    order. It is the library's `oraclesOf (bs.take n)` (Johnson/Desc/Block.lean), by unfolding; its
    length is `treesTo bs n`, by definition
  `depth_by_play`: the statement: where `(statedTo T.bs n)[j]? = some o`, the depth
    `(T.tableAt (.own j) k m).2.logLength` is `o.logLength`
  `table_by_play`: `T.tableAt (.own j) k m` is the table number j of the rounds that `play`
    returned, or the default `dflt` where no part of the prover's sent it
  `depth_by_play_below`: `depth_by_play` with less asked of the fields `table` and `fixed`: htab and
    hfix as `trees_by_play_below` (PlayedTo.lean, "What the statements `…_below` ask") has them;
    `depth_by_play` is a call of it
  `table_by_play_below`: under these, where a part of the prover's has sent the table number j, that
    table has the place of `T.tableAt (.own j) k m` and shows the same (`Table.same`). Another
    conclusion than that of `table_by_play`, which is no call of it
  `tables_depths`: where every step states as many oracle messages as its entry has roots (`Rooted`,
    PlayedTo.lean) and has a move or its entry's `roots` is 0, the tables of the rounds that `play`
    returns have, one by one, the depths that the steps state; none is missing
  `told_depths`: the same for one round
  `steps_oracles_all`: the steps that `chainSteps` returns state, in order, the oracle messages of
    the sub-protocols
  `steps_moved_or`: where every sub-protocol has a part of the prover's or none of its rounds has a
    root, every step has a move or its entry's `roots` is 0
  `zip_fst_mem`, `zip_snd_map`, `flatMap_map_id`, `flatMap_flat`, `rows_oracles`: small facts on
    lists

By what. `Step.tell` (Honest/Frame.lean) returns an error unless the message of a prover's part
passes `Sending.fits`, which compares the pairs (logLength, words) of its tables with the stated
ones (`tell_yields`, Honest/Law/Play.lean). So a table that was sent has the stated depth, and no
hypothesis on the parts' tables is needed. What a `Thread` calls a tree's table (`Thread.tableAt`)
is read off its field `table`; at `tableBy` it is that sent table.

Hypotheses of `depth_by_play`. htab: the field `table` at every own tree is `tableBy`. hfix: the
field `fixed` at an own tree counts the challenges before the chain and those before the round that
sends the tree. hsh: each sub-protocol has one list of oracle messages for each round, with one
message for each root (`Listed`, FixedSent.lean). hP: `PlayedTo`; of `ThrS`
(Honest/Thread/Said.lean: the invariant `Thr` and a second proposition, here `PlayedTo`), only
`PlayedTo` is a hypothesis. `start` is a parameter of `PlayedTo` and `tableBy`: the state at which
the chain's run begins, made of a run's coins, the input and the challenges before the chain. hAll:
`chainSteps` returns for the whole chain, at this run's coins and input (`tableBy` reads the whole
chain's steps). hhalf: each of the first n sub-protocols has a part of the prover's (`Placed`), or
none of its rounds has a root.

Limits. hhalf is needed: where a sub-protocol that sends a tree has no part of the prover's, no
table is sent, `tableBy` is its default, and the conclusion is false unless the default has the
stated depth. A `Thread` in which a tree-sending sub-protocol before n has no part of the prover's
does not meet it. It asks more than tree j needs: the sender of tree j alone would do. Own trees
only: `tableBy` says nothing of a tree that is taken over from another chain. That the depth at
which a round opens a tree is the depth that is stated for it is not said here: it is a test on the
description (DepthsAtByPlay.lean). No law here ties `(statedTo bs n)[j]?` to `(oraclesOf bs)[j]?`.
No `Thread` is shown to meet the hypotheses together. All limits of PlayedTo.lean hold, above all:
at arguments that `start` does not keep (its state's input, or the challenges that it has heard, are
not those that it was given) `PlayedTo` is false, and the statements here hold vacuously there. The
proofs of `table_by_play` and `table_by_play_below` rest on `sentAt_by_play` (PlayedTo.lean).
`tables_sent` (Honest/Law/StratPlay.lean, not imported here) says the like of `tables_depths` for
each table that was sent. `ProofFile.Honest.steps_oracles` (Honest/Thread/MadeLaw.lean) is
`steps_oracles_all` at one sub-protocol, and `flatMap_map_id` is `ProofFile.Honest.flatMap_id_map` (also
MadeLaw.lean) with its two sides exchanged. Conditional lemmas on the frame's own definitions. No
property of a protocol is stated: nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Small.PlayedTo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Small
open VerifiableInference.Desc (Block Place Oracle sendRound)

/-! ## 1 On lists -/

theorem zip_fst_mem {α β : Type} : ∀ (a : List α) (b : List β) (z : α × β), z ∈ a.zip b → z.1 ∈ a
  | [], _, _, hz => by simp at hz
  | _ :: _, [], _, hz => by simp at hz
  | x :: a, y :: b, z, hz => by
    rw [List.zip_cons_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (zip_fst_mem a b z hz)

theorem zip_snd_map {α β : Type} : ∀ (a : List α) (b : List β), b.length = a.length →
    (a.zip b).map (·.2) = b
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | x :: a, y :: b, h => by
    rw [List.zip_cons_cons, List.map_cons, zip_snd_map a b (Nat.succ.inj h)]

theorem flatMap_map_id {α β : Type} (f : α → List β) : ∀ l : List α,
    l.flatMap f = (l.map f).flatMap id
  | [] => rfl
  | x :: l => by
    rw [List.flatMap_cons, List.map_cons, List.flatMap_cons, flatMap_map_id f l]
    rfl

theorem flatMap_flat {α β : Type} (f : α → List (List β)) : ∀ l : List α,
    (l.flatMap f).flatMap id = l.flatMap fun x => (f x).flatMap id
  | [] => rfl
  | x :: l => by
    rw [List.flatMap_cons, List.flatMap_append, List.flatMap_cons, flatMap_flat f l]

section Lists
variable {S Cl : Type}

/-- The oracle messages that the first n sub-protocols state, in order. -/
def statedTo (bs : List (Block S Cl)) (n : Nat) : List Oracle :=
  (bs.take n).flatMap fun x => x.oracles.flatMap id

/-- Of the list of tuples in which `chainSteps_rows` (Honest/Law/Steps.lean) describes a chain's
steps, the second components are the sub-protocols' lists of oracle messages, in order. -/
theorem rows_oracles (f : Block S Cl → Bool) : ∀ bs : List (Block S Cl),
    (∀ b ∈ bs, b.oracles.length = b.rounds.length) →
    (bs.flatMap fun b => (b.rounds.zip b.oracles).map fun z => (z.1, z.2, b.place, f b)).map
      (·.2.1) = bs.flatMap (·.oracles)
  | [], _ => rfl
  | b :: bs, h => by
    rw [List.flatMap_cons, List.flatMap_cons, List.map_append,
      rows_oracles f bs fun x hx => h x (List.mem_cons_of_mem _ hx), List.map_map]
    congr 1
    exact zip_snd_map b.rounds b.oracles (h b List.mem_cons_self)

end Lists

/-! ## 2 On steps -/

section Chain
variable {S Cl V W X : Type} {B : ProverCoinCounts} {rows : List (Addr × Due)}
  {look : Addr → (d : Due) × Cs d} {v : Option V} {bs : List (Block S Cl)}
  {hs : List (Placed V W X)} {ss : List (Step W X)}

/-- The steps that `chainSteps` returns state, in order, the oracle messages of the sub-protocols.
-/
theorem steps_oracles_all (h : chainSteps B rows look v bs hs = .ok ss) :
    ss.flatMap (·.oracles) = bs.flatMap fun x => x.oracles.flatMap id := by
  obtain ⟨h1, h2⟩ := chainSteps_rows bs hs ss h
  have h3 := congrArg (List.map (·.2.1)) h2
  rw [List.map_map, rows_oracles _ bs h1] at h3
  rw [flatMap_map_id, ← flatMap_flat]
  exact congrArg (fun l => l.flatMap id) h3

/-- Where every sub-protocol has a part of the prover's or none of its rounds has a root, every step
has a move or its entry's `roots` is 0. -/
theorem steps_moved_or (h : chainSteps B rows look v bs hs = .ok ss)
    (hh : ∀ x ∈ bs, (hs.any fun g => g.place == x.place) = true ∨
      ∀ d ∈ x.rounds, d.entry.roots = 0) :
    ∀ s ∈ ss, s.move.isSome = true ∨ s.decl.entry.roots = 0 := by
  intro s hs'
  have e := (chainSteps_rows bs hs ss h).2
  have hm : (s.decl, s.oracles, s.addr.place, s.move.isSome) ∈
      ss.map (fun s => (s.decl, s.oracles, s.addr.place, s.move.isSome)) :=
    List.mem_map.2 ⟨s, hs', rfl⟩
  rw [e] at hm
  obtain ⟨b, hb, hz⟩ := List.mem_flatMap.1 hm
  obtain ⟨z, hz1, hz2⟩ := List.mem_map.1 hz
  have h1 : z.1 = s.decl := congrArg (·.1) hz2
  have h3 : (hs.any fun g => g.place == b.place) = s.move.isSome := congrArg (·.2.2.2) hz2
  rcases hh b hb with a | a
  · exact Or.inl (h3 ▸ a)
  · exact Or.inr (h1 ▸ a z.1 (zip_fst_mem _ _ z hz1))

end Chain

section Steps
variable {W X : Type}

/-- The tables that one round tells have the depths that its step states. hr: the step states as
many oracle messages as its entry has roots. hm: it has a move, or its entry's `roots` is 0. -/
theorem told_depths {s : Step W X} {b : Option Fmt.RoundView} {m : Mid W X} {x : Told}
    (h : s.tell b m = .ok x) (hr : s.oracles.length = s.decl.entry.roots)
    (hm : s.move.isSome = true ∨ s.decl.entry.roots = 0) :
    x.tables.map (fun t => t.map fun u => u.logLength) =
      s.oracles.map fun o => some o.logLength := by
  obtain ⟨-, a, c⟩ := tell_yields h
  cases hmv : s.move.isSome with
  | true =>
    obtain ⟨w, hw, -, e⟩ := a hmv
    unfold Sending.fits at hw
    have hw3 : w.tables.map (fun t => (t.logLength, t.words)) =
        s.oracles.map fun o => (o.logLength, o.words) := eq_of_beq (Bool.and_eq_true_iff.1 hw).2
    have hw4 := congrArg (List.map fun p : Nat × Nat => some p.1) hw3
    rw [List.map_map, List.map_map] at hw4
    rw [e, List.map_map]
    exact hw4
  | false =>
    have h0 : s.decl.entry.roots = 0 := by
      rcases hm with q | q
      · rw [hmv] at q
        cases q
      · exact q
    have ho : s.oracles = [] := List.eq_nil_of_length_eq_zero (hr.trans h0)
    rw [(c hmv).2, h0, ho]
    rfl

/-- The tables of the rounds that `play` returns have, one by one, the depths that the steps state,
where every step states as many oracle messages as its entry has roots (`Rooted`) and has a move or
its entry's `roots` is 0. -/
theorem tables_depths : ∀ (L : List (Step W X)) (ds : List Fmt.Drawn) (back : List Fmt.RoundView)
    (m : Mid W X) (y : List Played × Mid W X), play L ds back m = .ok y → Rooted L →
    (∀ s ∈ L, s.move.isSome = true ∨ s.decl.entry.roots = 0) →
    (tablesOf y.1).map (fun t => t.map fun u => u.2.logLength) =
      (L.flatMap (·.oracles)).map fun o => some o.logLength
  | [], [], _, m, y, h, _, _ => by
    simp only [play] at h
    cases h
    rfl
  | [], _ :: _, _, _, _, h, _, _ => by simp [play] at h
  | _ :: _, [], _, _, _, h, _, _ => by simp [play] at h
  | s :: L, d :: ds, back, m, y, h, hr, hm => by
    obtain ⟨x, m', z, h1, -, h3, rfl⟩ := play_cons_ok h
    have ih := tables_depths L ds back.tail m' z h3
      (fun t ht => hr t (List.mem_cons_of_mem _ ht)) fun t ht => hm t (List.mem_cons_of_mem _ ht)
    have hx := told_depths h1 (hr s List.mem_cons_self) (hm s List.mem_cons_self)
    have ht : ∀ p : Played, p.tables = x.tables → p.place = s.addr.place →
        tablesOf (p :: z.1) =
          (x.tables.map fun t => t.map fun u => (s.addr.place, u)) ++ tablesOf z.1 := by
      intro p e1 e2
      unfold tablesOf
      rw [List.flatMap_cons, e1, e2]
    show (tablesOf (_ :: z.1)).map _ = _
    rw [ht _ rfl rfl, List.map_append, ih, List.flatMap_cons, List.map_append, List.map_map, ← hx]
    congr 1
    refine List.map_congr_left fun t _ => ?_
    cases t <;> rfl

end Steps

/-! ## 3 The table, and its depth -/

section Law
variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)
  (start : Coins Bk → W → List Fmt.Drawn → Mid W X)

/-- **What the `Thread` names for an own tree that the first n sub-protocols state shows the same as
the table of that number of the rounds that `play` returned**, where a part of the prover's has sent
one. htab and hfix as `trees_by_play_below` (PlayedTo.lean) asks them. It has another conclusion
than `table_by_play`, which is an equation and speaks where nothing was sent too, there of the
default: so that one is no call of this one. -/
theorem table_by_play_below
    (htab : ∀ j, j < treesTo T.bs T.bs.length → ∀ k w h u, h.length = T.fixed (.own j) →
      sentAt T start j k w h = some u →
      u.1 = (T.table (.own j) k w h).1 ∧ u.2.same (T.table (.own j) k w h).2 = true)
    (hfix : ∀ j, j < treesTo T.bs T.bs.length →
      T.fixed (.own j) = T.front + sentIn (T.bs.flatMap (·.rounds)) j)
    (hsh : ∀ x ∈ T.bs, Listed x) {n : Nat} {k : Coins Bk} {m : Mid W X} {L : List (Step W X)}
    {ps : List Played}
    (hL : chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees m.st.input) (T.bs.take n)
      T.hs = .ok L)
    (hp : play L (m.st.heard.drop T.front) [] (start k m.st.input (m.st.heard.take T.front)) =
      .ok (ps, m))
    {Lall : List (Step W X)}
    (hAll : chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees m.st.input) T.bs T.hs =
      .ok Lall)
    {j : Nat} (hj1 : j < treesTo T.bs n) {u : Place × Table}
    (hu : ((tablesOf ps)[j]?).bind id = some u) :
    u.1 = (T.tableAt (.own j) k m).1 ∧ u.2.same (T.tableAt (.own j) k m).2 = true := by
  obtain ⟨hs, hlt⟩ := sentAt_by_play T start hfix hsh hL hp hAll hj1
  exact htab j (Nat.lt_of_lt_of_le hj1 (treesTo_le_all T.bs n)) k _ _ u hlt (hs.trans hu)

/-- The table that the `Thread` names for an own tree that the first n sub-protocols state, at a
state that `play` returns over them, is the table of that number of the rounds that `play` returned,
or the default where no part of the prover's sent it. -/
theorem table_by_play (dflt : Place × Table)
    (htab : ∀ j k w h, T.table (.own j) k w h = tableBy T start dflt j k w h)
    (hfix : ∀ j, T.fixed (.own j) = T.front + sentIn (T.bs.flatMap (·.rounds)) j)
    (hsh : ∀ x ∈ T.bs, Listed x) {n : Nat} {k : Coins Bk} {m : Mid W X} {L : List (Step W X)}
    {ps : List Played}
    (hL : chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees m.st.input) (T.bs.take n)
      T.hs = .ok L)
    (hp : play L (m.st.heard.drop T.front) [] (start k m.st.input (m.st.heard.take T.front)) =
      .ok (ps, m))
    {Lall : List (Step W X)}
    (hAll : chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees m.st.input) T.bs T.hs =
      .ok Lall)
    {j : Nat} (hj1 : j < treesTo T.bs n) :
    T.tableAt (.own j) k m = (((tablesOf ps)[j]?).bind id).getD dflt := by
  unfold Thread.tableAt
  rw [htab, tableBy_eq, (sentAt_by_play T start (fun j _ => hfix j) hsh hL hp hAll hj1).1]

/-- **`depth_by_play`, with less asked of the fields `table` and `fixed`**: htab and hfix as
`trees_by_play_below` (PlayedTo.lean) asks them. -/
theorem depth_by_play_below
    (htab : ∀ j, j < treesTo T.bs T.bs.length → ∀ k w h u, h.length = T.fixed (.own j) →
      sentAt T start j k w h = some u →
      u.1 = (T.table (.own j) k w h).1 ∧ u.2.same (T.table (.own j) k w h).2 = true)
    (hfix : ∀ j, j < treesTo T.bs T.bs.length →
      T.fixed (.own j) = T.front + sentIn (T.bs.flatMap (·.rounds)) j)
    (hsh : ∀ x ∈ T.bs, Listed x) {n : Nat} {k : Coins Bk} {m : Mid W X}
    (hP : PlayedTo T start n k m) {Lall : List (Step W X)}
    (hAll : chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees m.st.input) T.bs T.hs =
      .ok Lall)
    (hhalf : ∀ x ∈ T.bs.take n, (T.hs.any fun g => g.place == x.place) = true ∨
      ∀ d ∈ x.rounds, d.entry.roots = 0)
    {j : Nat} {o : Oracle} (hj : (statedTo T.bs n)[j]? = some o) :
    (T.tableAt (.own j) k m).2.logLength = o.logLength := by
  obtain ⟨L, ps, hL, hp⟩ := hP
  have hj1 : j < (statedTo T.bs n).length := by
    by_contra hc
    rw [List.getElem?_eq_none (Nat.le_of_not_lt hc)] at hj
    cases hj
  have hd := tables_depths L _ _ _ _ hp
    (steps_rooted hL fun x hx => hsh x (List.mem_of_mem_take hx)) (steps_moved_or hL hhalf)
  rw [steps_oracles_all hL] at hd
  have hq : ((tablesOf ps)[j]?).map (fun t => t.map fun u => u.2.logLength) =
      some (some o.logLength) := by
    have q := congrArg (fun l => l[j]?) hd
    simp only [List.getElem?_map] at q
    rw [q]
    show ((statedTo T.bs n)[j]?).map _ = _
    rw [hj]
    rfl
  cases ht : (tablesOf ps)[j]? with
  | none =>
    rw [ht] at hq
    cases hq
  | some t =>
    rw [ht] at hq
    cases t with
    | none => cases hq
    | some u =>
      have hs := (table_by_play_below T start htab hfix hsh hL hp hAll hj1 (u := u)
        (by rw [ht]; rfl)).2
      unfold Table.same at hs
      rw [Bool.and_eq_true, Bool.and_eq_true] at hs
      rw [← eq_of_beq hs.1.1]
      exact Option.some.inj (Option.some.inj hq)

/-- **The table of an own tree that the first n sub-protocols state has the stated depth**, at a
state of the prover's run that the frame's own `play` returns over them. -/
theorem depth_by_play (dflt : Place × Table)
    (htab : ∀ j k w h, T.table (.own j) k w h = tableBy T start dflt j k w h)
    (hfix : ∀ j, T.fixed (.own j) = T.front + sentIn (T.bs.flatMap (·.rounds)) j)
    (hsh : ∀ x ∈ T.bs, Listed x) {n : Nat} {k : Coins Bk} {m : Mid W X}
    (hP : PlayedTo T start n k m) {Lall : List (Step W X)}
    (hAll : chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees m.st.input) T.bs T.hs =
      .ok Lall)
    (hhalf : ∀ x ∈ T.bs.take n, (T.hs.any fun g => g.place == x.place) = true ∨
      ∀ d ∈ x.rounds, d.entry.roots = 0)
    {j : Nat} {o : Oracle} (hj : (statedTo T.bs n)[j]? = some o) :
    (T.tableAt (.own j) k m).2.logLength = o.logLength :=
  depth_by_play_below T start (sent_of_tableBy T start dflt fun j _ => htab j) (fun j _ => hfix j)
    hsh hP hAll hhalf hj

end Law

end ProofFile.Honest.Small

#print axioms ProofFile.Honest.Small.statedTo
#print axioms ProofFile.Honest.Small.zip_fst_mem
#print axioms ProofFile.Honest.Small.zip_snd_map
#print axioms ProofFile.Honest.Small.flatMap_map_id
#print axioms ProofFile.Honest.Small.flatMap_flat
#print axioms ProofFile.Honest.Small.rows_oracles
#print axioms ProofFile.Honest.Small.steps_oracles_all
#print axioms ProofFile.Honest.Small.steps_moved_or
#print axioms ProofFile.Honest.Small.told_depths
#print axioms ProofFile.Honest.Small.tables_depths
#print axioms ProofFile.Honest.Small.table_by_play
#print axioms ProofFile.Honest.Small.depth_by_play
#print axioms ProofFile.Honest.Small.table_by_play_below
#print axioms ProofFile.Honest.Small.depth_by_play_below
