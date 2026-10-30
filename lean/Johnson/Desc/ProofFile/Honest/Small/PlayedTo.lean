-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Small/PlayedTo.lean: `PlayedTo` says that a state m of the prover's
run (`Mid`) is what the frame's own `play` (Honest/Frame.lean) returns over the first b
sub-protocols of the chain of a `Thread` (the structure, Honest/Thread/Thr.lean). It has the type of
the parameter `Said` of Honest/Thread/Said.lean, and the hypothesis `SaidNext` that comes with that
parameter is proved for it at every sub-protocol, where `start` hands no columns. `tableBy` is the
table of one of the chain's own
trees as that `play` sends it. For a `Thread` whose field `table` is `tableBy`, a sub-protocol's new
trees are the tables that the `Thread` names: the last clause of `PlaysS`
(Honest/Thread/PaysS.lean). General in the `Thread` and in the prover: no kind of sub-protocol is
named.

For what. The invariant `Thr` does not say that m comes from the prover's parts: its clause
`Thread.Made` speaks of the verifier's steps over the rounds seen, and no clause reads `m.st.own`. A
sub-protocol's new tree is sent by `play` from m, while the field `table` is a function of a run's
coins, the input and the challenges heard. `PlayedTo` ties m to these three (`playedTo_unique`), so
that the two can be compared.

  `PlayedTo T start b k m`: a definition: `chainSteps` returns steps L for the first b
    sub-protocols, and `play` over L, from the state `start k m.st.input (m.st.heard.take T.front)`,
    at the chain's own challenges `m.st.heard.drop T.front`, returns m. `start` is a parameter: the
    state in which the chain's run begins, as a function of a run's coins, the input and the
    challenges before the chain
  `saidNext_played`: `SaidNext T (PlayedTo T start) b`, at every b, under one hypothesis: the field
    `opened` of every value of `start` is `none`: from `Thr` and `PlayedTo` at b, and the rounds of
    the sub-protocol number b (from 0) as played (`Thread.Moved`), `PlayedTo` holds at b + 1, at the
    state after these rounds, which `Mid.took` leaves as it is (`play_opened`, Honest/Gap.lean)
  `trees_by_play`: `T.Trees (T.fresh b) k y.2 (E.add y.1)`: each tree that is at hand after the
    sub-protocol number b and not before it comes from the place, and shows the table, that the
    `Thread` names for it
  `playsS_by_play`: `PlaysS T (PlayedTo T start) b`, at a sub-protocol that has a part of the
    prover's (`Placed`). What is left to show at the sub-protocol is that its `play` and the filling
    of its columns (`fillCols`) return
  `trees_by_play_below`, `playsS_by_play_below`: the same two conclusions with less asked of the
    fields `table` and `fixed` (see "Hypotheses"); the two statements above are calls of these
  `playedTo_unique`: at one b and one run's coins, two states that meet `PlayedTo` and have the same
    input and the same challenges heard are equal
  `sentBy L ds m`: a definition: the tables that the steps L send from the state m along the
    challenges ds, each with its sender's place, `none` where no part of the prover's sent the
    table. The tables of the round after the last challenge are included: a round's message is sent
    before its challenge. The list ends at the first error of `Step.tell` or `Step.hear`
  `tableBy T start dflt j k w h`: a definition: the entry number j of `sentBy` over the whole
    chain's steps, from `start k w (h.take T.front)`, along `h.drop T.front`; the default `dflt`
    where `chainSteps` returns an error for the whole chain, where the list has no entry j (the
    chain sends no such tree, h has too few challenges, or `sentBy` ended at an error), and where
    that entry is `none`
  `sentAt T start j k w h`: a definition: `tableBy` without its default: `none` in the cases in
    which `tableBy` is `dflt`. `tableBy_eq`: `tableBy` is `sentAt` with the default
  `sentAt_congr`, `tableBy_congr`: two `Thread`s that agree in `chain`, `φ`, `bs`, `hs` and `front`
    give the same `sentAt` and the same `tableBy`
  `sent_of_tableBy`: a `Thread` whose field `table` is `tableBy` at the own trees below N meets htab
    as the statements `…_below` ask it
  `sentAt_by_play`: at a state that `play` returns over the first n sub-protocols, and at the
    challenges that `fixed` counts for an own tree that these n state, `sentAt` is the table of that
    number of the rounds that `play` returned; no hypothesis on the field `table`
  `played_next`: the step of `saidNext_played`, with the lists of steps and of rounds named
  `play_split`: a `play` over two lists of steps that has returned, split in two
  `sent_of_play`: where `play` has returned over some steps and one more, `sentBy` along all the
    challenges but the last gives the tables of the rounds as played, whatever steps follow
  `Rooted L`: a definition: each step of L states as many oracle messages as its entry's `roots`.
    `steps_rooted`: so do the steps that `chainSteps` returns, where every sub-protocol is `Listed`
  `oracles_roots`, `tables_roots`: for such steps, the oracle messages stated, and the tables of the
    rounds that `play` returns, are as many as the entries' `roots` together (`rootsSum`)
  `tables_some`: where every step has a move or its entry's `roots` is 0, a part of the prover's has
    sent every table. `steps_moved`: at a sub-protocol that has such a part, every step has a move
  `sender_bounds`: where the round number r sends the tree number j (`sendRound`,
    Johnson/Desc/Block.lean), the rounds before it have at most j roots, and with it more than j
  `zip_of_map`: a small fact on lists

By what. At the challenges that `fixed` counts, `sentAt` (and so `tableBy`) plays the whole chain's
steps anew, up to and with the message of the round r that sends the tree number j, and takes the
entry j of the tables sent. By `sent_of_play` these are the tables of the rounds that `play` returns
over the first r + 1 steps; by `play_split` these rounds are the first r + 1 of the rounds that
`PlayedTo` gives: this is `sentAt_by_play`. `trees_by_play_below` calls it at b + 1, at the rounds
`ps ++ y.1` that `PlayedTo` and `Thread.Moved` give (`played_next`); `Env.add` (Honest/Side.lean)
has the same entry for that tree. Called: `play_append`, `play_cons_ok`, `tell_yields`,
`play_yields`, `exBind_ok`, `exMap_ok` (Honest/Law/Play.lean), `tables_count`
(Honest/Law/Causal.lean), `chainSteps_append`, `tablesOf_append` (Honest/Law/Cut.lean),
`chainSteps_rows` (Honest/Law/Steps.lean), `steps_decl` (Honest/Law/Run.lean), `play_mid`
(Honest/Law/Along.lean), `play_heard`, `Thread.heard_length` (Honest/Thread/PaysLaw.lean),
`take_succ_some` (Honest/Thread/MadeLaw.lean), `play_lengths` (PlayRow.lean), and `rootsSum_cons`,
`treesTo_roots`, `decls_split`, `sender_found`, `sender_front`, `sender_below`, `treesTo_le_all`
(FixedSent.lean).

Hypotheses of `trees_by_play`. htab: the field `table` at every own tree is `tableBy`. hfix: the
field `fixed` at an own tree counts the challenges before the chain and those before the round that
sends the tree. hsh: each sub-protocol has one list of oracle messages for each round, with one
message for each root (`Listed`, FixedSent.lean). hblk: blk is the sub-protocol number b. hT: the
pair of the invariant `Thr` and `PlayedTo` at b (`ThrS`, Honest/Thread/Said.lean). hM: the rounds of
blk as played from m, and its columns (`Thread.Moved`, Honest/Thread/Pays.lean). hAll: `chainSteps`
returns for the whole chain, at this run's coins and input (`tableBy` reads the whole chain's
steps). hsome: a part of the prover's has sent each table of these rounds. `playsS_by_play` keeps
htab, hfix, hsh and hblk. Its others: hf: `T.hs` has a part of the prover's at the place of blk (so
hsome holds, by `steps_moved` and `tables_some`). hall: hAll at all coins and inputs. hmv: under the
hypotheses of `PlaysS`, `Thread.Moved` holds of some y and cols.

What the statements `…_below` ask instead of htab and hfix. Both are asked only at j below
`treesTo T.bs T.bs.length`, the number of the oracle messages that the chain's sub-protocols state.
Beyond it `sentIn` is 0 (`sentIn_beyond`, FixedSent.lean), so hfix at every j says there that
`T.fixed (.own j)` is `T.front`; a `Thread` whose field `fixed` counts all the chain's rounds there
(`Script.ofLots`, Honest/Thread/ScriptLots.lean) does not meet that unless the chain has no round,
and the two plain statements say nothing of it. htab is asked only at lists of challenges as long as
`fixed` counts, and only where `sentAt` is some u: nothing at a list that is too short, nothing
where `chainSteps` or a step returns an error, and no default. It asks that u has the place of the
`Thread`'s table and that `u.2.same` of that table is true, as `Thread.handAt` reads them: no
equation of tables, whose symbols are functions on all numbers.

Limits. With `table` set to `tableBy`, the conclusion of `trees_by_play` holds of every prover by
construction: the `Thread`'s table is defined as what `play` sends. That such a table encodes a
message of the `Thread`'s witness (the field `wit`) is not shown: whoever proves an item on that
message has to show it. `saidNext_played` carries `PlayedTo` from b to b + 1; at b = 0 it has to be
shown, and there it says that m is the value of `start`. It stands where no column is handed: of
the states of a walk (`runC`, Honest/Walk.lean), whose field `opened` is `some …`, it says nothing.
`play` keeps the input and only appends to
`heard`, `loc` and `seen` (`play_mid`, `play_heard`). So where the value of `start` does not keep
its arguments (its `st.input` is not the input that it is given, or its `st.heard` is not the list
that it is given), or its `loc` or `seen` is not as `Thread.Made` asks, `PlayedTo` and `Thr` do not
hold together. At a `start` that is so at all arguments, `PlayedTo` is false at every state at which
`Thr` holds, and every statement that has the pair as a hypothesis holds vacuously. This is argued,
not stated as a theorem, and no predicate that says that `start` is fit is defined. hAll and hall
ask that `chainSteps` returns for the whole chain: Honest/Thread/Laid.lean has the like for one
sub-protocol's steps, from one return of `ready`, and no lemma for the whole chain is called here.
hsome asks that a part of the prover's has sent each new tree's table. Own trees only: no tree that
is taken over from another chain is in `T.fresh b`, and `tableBy` says nothing of such a tree. In
this folder no `Thread` is shown to meet the hypotheses together. Conditional lemmas on the frame's
own definitions. No property of a protocol is stated: nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Small.PlayRow
import Johnson.Desc.ProofFile.Honest.Small.FixedSent
import Johnson.Desc.ProofFile.Honest.Thread.PaysS
import Johnson.Desc.ProofFile.Honest.Gap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Small
open VerifiableInference.Desc (Block Place OpenedColumn sendRound)

/-! ## 1 On lists of steps and of rounds -/

section Steps
variable {W X : Type}

/-- A `play` over two lists of steps that has returned, split in two. -/
theorem play_split {A B : List (Step W X)} {dA dB : List Fmt.Drawn} {m : Mid W X}
    {y : List Played × Mid W X} (hl : dA.length = A.length)
    (h : play (A ++ B) (dA ++ dB) [] m = .ok y) :
    ∃ y₁ z, play A dA [] m = .ok y₁ ∧ play B dB [] y₁.2 = .ok z ∧ y = (y₁.1 ++ z.1, z.2) := by
  rw [play_append _ _ _ _ _ _ hl] at h
  obtain ⟨y₁, e1, h⟩ := exBind_ok h
  rw [List.drop_nil] at h
  obtain ⟨z, e2, rfl⟩ := exMap_ok h
  exact ⟨y₁, z, e1, e2, rfl⟩

/-- The tables that steps send along challenges, each with its sender's place, `none` where no part
of the prover's sent the table. The tables of the round after the last challenge are included. The
list ends at the first error of `Step.tell` or `Step.hear`. -/
def sentBy : List (Step W X) → List Fmt.Drawn → Mid W X → List (Option (Place × Table))
  | [], _, _ => []
  | s :: ss, ds, m =>
    match s.tell none m with
    | .error _ => []
    | .ok x =>
      (x.tables.map fun t => t.map fun u => (s.addr.place, u)) ++
        match ds with
        | [] => []
        | d :: ds' =>
          match s.hear x d m with
          | .error _ => []
          | .ok m' => sentBy ss ds' m'

/-- Where `play` has returned over the steps L₁ and one more, s, `sentBy` along all the challenges
but the last gives the tables of the rounds as played, whatever steps L₂ follow s. -/
theorem sent_of_play (s : Step W X) (L₂ : List (Step W X)) (d : Fmt.Drawn) :
    ∀ (L₁ : List (Step W X)) (ds : List Fmt.Drawn) (m : Mid W X) (y : List Played × Mid W X),
      play (L₁ ++ [s]) (ds ++ [d]) [] m = .ok y → ds.length = L₁.length →
      sentBy (L₁ ++ s :: L₂) ds m = tablesOf y.1
  | [], [], m, y, h, _ => by
    obtain ⟨x, m', z, h1, -, h3, rfl⟩ :=
      play_cons_ok (show play (s :: []) (d :: []) [] m = .ok y from h)
    have hz : z = ([], m') := by
      simp only [play] at h3
      exact (Except.ok.inj h3).symm
    subst hz
    have h1' : s.tell none m = .ok x := h1
    simp only [List.nil_append, sentBy, h1', tablesOf, List.flatMap_cons, List.flatMap_nil]
  | [], _ :: _, _, _, _, hl => by cases hl
  | _ :: _, [], _, _, _, hl => by cases hl
  | t :: L₁, e :: ds, m, y, h, hl => by
    obtain ⟨x, m', z, h1, h2, h3, rfl⟩ :=
      play_cons_ok (show play (t :: (L₁ ++ [s])) (e :: (ds ++ [d])) [] m = .ok y from h)
    have h1' : t.tell none m = .ok x := h1
    have ih := sent_of_play s L₂ d L₁ ds m' z h3 (Nat.succ.inj hl)
    simp only [List.cons_append, sentBy, h1', h2, ih, tablesOf, List.flatMap_cons]

/-- Each step states as many oracle messages as its entry's `roots`. -/
def Rooted (L : List (Step W X)) : Prop := ∀ s ∈ L, s.oracles.length = s.decl.entry.roots

theorem oracles_roots : ∀ L : List (Step W X), Rooted L →
    (L.flatMap (·.oracles)).length = rootsSum (L.map (·.decl))
  | [], _ => rfl
  | s :: L, h => by
    rw [List.flatMap_cons, List.length_append, List.map_cons, rootsSum_cons,
      oracles_roots L fun t ht => h t (List.mem_cons_of_mem _ ht), h s List.mem_cons_self]

/-- Where the steps are `Rooted`, the rounds that `play` returns have as many tables as the steps'
entries have `roots` together: `tables_count` (Honest/Law/Causal.lean), in roots. -/
theorem tables_roots (L : List (Step W X)) (ds : List Fmt.Drawn) (back : List Fmt.RoundView)
    (m : Mid W X) (y : List Played × Mid W X) (h : play L ds back m = .ok y) (hr : Rooted L) :
    (tablesOf y.1).length = rootsSum (L.map (·.decl)) := by
  rw [tables_count L ds back y.1 (play_yields L ds back m y h) hr, oracles_roots L hr]

/-- Where every step has a move or its entry's `roots` is 0, a part of the prover's has sent every
table. -/
theorem tables_some : ∀ (L : List (Step W X)) (ds : List Fmt.Drawn) (back : List Fmt.RoundView)
    (m : Mid W X) (y : List Played × Mid W X), play L ds back m = .ok y →
    (∀ s ∈ L, s.move.isSome = true ∨ s.decl.entry.roots = 0) → ∀ t ∈ tablesOf y.1, t.isSome = true
  | [], [], _, m, y, h, _ => by
    simp only [play] at h
    cases h
    intro t ht
    cases ht
  | [], _ :: _, _, _, _, h, _ => by simp [play] at h
  | _ :: _, [], _, _, _, h, _ => by simp [play] at h
  | s :: L, d :: ds, back, m, y, h, hr => by
    obtain ⟨x, m', z, h1, -, h3, rfl⟩ := play_cons_ok h
    have ih := tables_some L ds back.tail m' z h3 fun t ht => hr t (List.mem_cons_of_mem _ ht)
    intro t ht
    have ht' : t ∈ (x.tables.map fun t => t.map fun u => (s.addr.place, u)) ++ tablesOf z.1 := by
      unfold tablesOf at ht ⊢
      rwa [List.flatMap_cons] at ht
    rcases List.mem_append.1 ht' with hx | hz
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
      obtain ⟨-, a, b⟩ := tell_yields h1
      rcases hr s List.mem_cons_self with hm | h0
      · obtain ⟨w, -, -, e⟩ := a hm
        rw [e] at hq
        obtain ⟨v, -, rfl⟩ := List.mem_map.1 hq
        rfl
      · cases hm : s.move.isSome with
        | true =>
          obtain ⟨w, -, -, e⟩ := a hm
          rw [e] at hq
          obtain ⟨v, -, rfl⟩ := List.mem_map.1 hq
          rfl
        | false =>
          rw [(b hm).2, h0] at hq
          cases hq
    · exact ih t hz

end Steps

/-- Where the round number r sends the tree number j, the rounds before it have at most j roots, and
with it more than j. -/
theorem sender_bounds : ∀ (l : List Fmt.DeclaredRound) (j r : Nat), sendRound l j = some r →
    rootsSum (l.take r) ≤ j ∧ j < rootsSum (l.take (r + 1))
  | [], _, _, h => by cases h
  | x :: l, j, r, h => by
    unfold sendRound at h
    by_cases hj : j < x.entry.roots
    · rw [if_pos hj] at h
      cases h
      refine ⟨Nat.zero_le _, ?_⟩
      rw [List.take_succ_cons, rootsSum_cons]
      omega
    · rw [if_neg hj] at h
      obtain ⟨r', h', rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨a, b⟩ := sender_bounds l _ _ h'
      rw [List.take_succ_cons, List.take_succ_cons, rootsSum_cons, rootsSum_cons]
      omega

theorem zip_of_map {α β : Type} (f : α → Nat) (g : β → Nat) : ∀ (a : List α) (b : List β),
    a.map f = b.map g → ∀ z ∈ a.zip b, f z.1 = g z.2
  | [], _, _, _, hz => by simp at hz
  | _ :: _, [], _, _, hz => by simp at hz
  | x :: a, y :: b, h, z, hz => by
    rw [List.map_cons, List.map_cons, List.cons.injEq] at h
    rw [List.zip_cons_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact h.1
    · exact zip_of_map f g a b h.2 z hz

/-! ## 2 `PlayedTo`, and `SaidNext` for it -/

section Thread
variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)
  (start : Coins Bk → W → List Fmt.Drawn → Mid W X)

/-- The state m is what the frame's own `play` returns over the first b sub-protocols. A definition,
of the type of the parameter `Said` of Honest/Thread/Said.lean. -/
def PlayedTo (b : Nat) (k : Coins Bk) (m : Mid W X) : Prop :=
  ∃ L ps, chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees m.st.input) (T.bs.take b)
      T.hs = .ok L ∧
    play L (m.st.heard.drop T.front) [] (start k m.st.input (m.st.heard.take T.front)) =
      .ok (ps, m)

variable {T start}

/-- One sub-protocol more, with the lists of steps and of rounds named. -/
theorem played_next {b : Nat} {blk : Block S Cl} {k : Coins Bk} {m : Mid W X}
    {ds : List Fmt.Drawn} {l L : List (Step W X)} {ps : List Played} {y : List Played × Mid W X}
    (hblk : T.bs[b]? = some blk) (hlen : T.front ≤ m.st.heard.length)
    (hL : chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees m.st.input) (T.bs.take b)
      T.hs = .ok L)
    (hp : play L (m.st.heard.drop T.front) [] (start k m.st.input (m.st.heard.take T.front)) =
      .ok (ps, m))
    (hl : chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees m.st.input) [blk] T.hs =
      .ok l)
    (hy : play l ds [] m = .ok y) :
    chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees y.2.st.input)
        (T.bs.take (b + 1)) T.hs = .ok (L ++ l) ∧
      play (L ++ l) (y.2.st.heard.drop T.front) []
        (start k y.2.st.input (y.2.st.heard.take T.front)) = .ok (ps ++ y.1, y.2) := by
  have hi := (play_mid _ _ _ _ _ hy).1
  have hh := play_heard _ _ _ _ _ hy
  constructor
  · rw [hi, take_succ_some hblk, chainSteps_append, hL, hl]
    rfl
  · rw [hi, hh, List.drop_append_of_le_length hlen, List.take_append_of_le_length hlen,
      play_append _ _ _ _ _ _ (play_lengths _ _ _ _ _ hp), hp]
    show ((play l ds (List.drop L.length []) m).map fun z => _) = _
    rw [List.drop_nil, hy]
    rfl

variable (T start)

/-- **`SaidNext` holds for `PlayedTo` at every sub-protocol**, where the chain's run begins with no
columns handed. h₀: the field `opened` of every value of `start` is `none`. `play` carries that
field on (`play_opened`, Honest/Gap.lean), so `Mid.took` leaves the state after the rounds as it
is. It stands where no column is handed: at a state whose field is `some …`, as a walk's own states
are, `PlayedTo` does not hold under h₀, and nothing is said. -/
theorem saidNext_played (h₀ : ∀ k w h, (start k w h).opened = none) (b : Nat) :
    SaidNext T (PlayedTo T start) b := by
  intro blk hblk k s m E ds y cols hT hS _ hM
  obtain ⟨L, ps, hL, hp⟩ := hS
  unfold Thread.Moved at hM
  obtain ⟨⟨l, hl, hy⟩, -⟩ := hM
  have hlen : T.front ≤ m.st.heard.length := by
    rw [Thread.heard_length T hT.2.1]
    exact Nat.le_add_right _ _
  obtain ⟨a1, a2⟩ := played_next hblk hlen hL hp hl hy
  have e : y.2.took cols = y.2 := by
    have e1 : y.2.opened = none :=
      (play_opened _ _ _ _ _ hy).trans ((play_opened _ _ _ _ _ hp).trans (h₀ _ _ _))
    obtain ⟨ps', st, loc, seen, opened⟩ := y
    have e2 : opened = none := e1
    subst e2
    rfl
  rw [e]
  exact ⟨L ++ l, ps ++ y.1, a1, a2⟩

/-- At one b and one run's coins, two states that meet `PlayedTo` and have the same input and the
same challenges heard are equal. -/
theorem playedTo_unique {b : Nat} {k : Coins Bk} {m m' : Mid W X} (h : PlayedTo T start b k m)
    (h' : PlayedTo T start b k m') (hi : m.st.input = m'.st.input)
    (hh : m.st.heard = m'.st.heard) : m = m' := by
  obtain ⟨L, ps, hL, hp⟩ := h
  obtain ⟨L', ps', hL', hp'⟩ := h'
  rw [← hi] at hL' hp'
  rw [← hh] at hp'
  have e : L = L' := Except.ok.inj (hL.symm.trans hL')
  subst e
  exact congrArg Prod.snd (Except.ok.inj (hp.symm.trans hp'))

/-! ## 3 The trees' tables, as `play` sends them -/

/-- The chain's tree number j, as the frame's own `play` sends it; `dflt` where `chainSteps` returns
an error for the whole chain, or `sentBy` has no table at the number j. -/
def tableBy (dflt : Place × Table) (j : Nat) (k : Coins Bk) (w : W) (h : List Fmt.Drawn) :
    Place × Table :=
  match chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees w) T.bs T.hs with
  | .ok L => (((sentBy L (h.drop T.front) (start k w (h.take T.front)))[j]?).bind id).getD dflt
  | .error _ => dflt

/-- The chain's tree number j, as the frame's own `play` sends it; `none` where `chainSteps` returns
an error for the whole chain, or `sentBy` has no table at the number j. `tableBy` is this with a
default (`tableBy_eq`). -/
def sentAt (j : Nat) (k : Coins Bk) (w : W) (h : List Fmt.Drawn) : Option (Place × Table) :=
  match chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees w) T.bs T.hs with
  | .ok L => ((sentBy L (h.drop T.front) (start k w (h.take T.front)))[j]?).bind id
  | .error _ => none

theorem tableBy_eq (dflt : Place × Table) (j : Nat) (k : Coins Bk) (w : W) (h : List Fmt.Drawn) :
    tableBy T start dflt j k w h = (sentAt T start j k w h).getD dflt := by
  unfold tableBy sentAt
  cases chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees w) T.bs T.hs <;> rfl

/-- `sentAt` reads five things of a `Thread`: `chain`, `φ`, `bs`, `hs` and `front`. Two that agree
in these give the same, whatever their other fields are, `table` and `fixed` among them. So a
`Thread`'s field `table` can be laid as `tableBy` at another `Thread` that is there before it. -/
theorem sentAt_congr {T T' : Thread Bk S Cl V W X Pb} (hc : T.chain = T'.chain) (hφ : T.φ = T'.φ)
    (hb : T.bs = T'.bs) (hh : T.hs = T'.hs) (hf : T.front = T'.front)
    (start : Coins Bk → W → List Fmt.Drawn → Mid W X) (j : Nat) (k : Coins Bk) (w : W)
    (h : List Fmt.Drawn) : sentAt T start j k w h = sentAt T' start j k w h := by
  unfold sentAt
  rw [hc, hφ, hb, hh, hf]

/-- The same for `tableBy`. -/
theorem tableBy_congr {T T' : Thread Bk S Cl V W X Pb} (hc : T.chain = T'.chain) (hφ : T.φ = T'.φ)
    (hb : T.bs = T'.bs) (hh : T.hs = T'.hs) (hf : T.front = T'.front)
    (start : Coins Bk → W → List Fmt.Drawn → Mid W X) (dflt : Place × Table) (j : Nat)
    (k : Coins Bk) (w : W) (h : List Fmt.Drawn) :
    tableBy T start dflt j k w h = tableBy T' start dflt j k w h := by
  rw [tableBy_eq, tableBy_eq, sentAt_congr hc hφ hb hh hf]

/-- A `Thread` whose field `table` is `tableBy` at the own trees below N meets the hypothesis htab
of the statements `…_below` there. -/
theorem sent_of_tableBy (dflt : Place × Table) {N : Nat}
    (htab : ∀ j, j < N → ∀ k w h, T.table (.own j) k w h = tableBy T start dflt j k w h) :
    ∀ j, j < N → ∀ k w h u, h.length = T.fixed (.own j) → sentAt T start j k w h = some u →
      u.1 = (T.table (.own j) k w h).1 ∧ u.2.same (T.table (.own j) k w h).2 = true := by
  intro j hj k w h u _ e
  have q : T.table (.own j) k w h = u := by
    rw [htab j hj, tableBy_eq, e]
    rfl
  rw [q]
  exact ⟨rfl, by simp [Table.same]⟩

end Thread

/-- The steps that `chainSteps` returns each state as many oracle messages as their entry's `roots`,
where every sub-protocol is `Listed`. -/
theorem steps_rooted {S Cl V W X : Type} {B : ProverCoinCounts} {rows : List (Addr × Due)}
    {look : Addr → (d : Due) × Cs d} {v : Option V} {bs : List (Block S Cl)}
    {hs : List (Placed V W X)} {ss : List (Step W X)}
    (h : chainSteps B rows look v bs hs = .ok ss) (hl : ∀ x ∈ bs, Listed x) : Rooted ss := by
  intro s hs'
  have e := (chainSteps_rows bs hs ss h).2
  have hm : (s.decl, s.oracles, s.addr.place, s.move.isSome) ∈
      ss.map (fun s => (s.decl, s.oracles, s.addr.place, s.move.isSome)) :=
    List.mem_map.2 ⟨s, hs', rfl⟩
  rw [e] at hm
  obtain ⟨b, hb, hz⟩ := List.mem_flatMap.1 hm
  obtain ⟨z, hz1, hz2⟩ := List.mem_map.1 hz
  have hq := zip_of_map (·.entry.roots) (·.length) b.rounds b.oracles (hl b hb).2 z hz1
  have h1 : z.1 = s.decl := congrArg (·.1) hz2
  have h2 : z.2 = s.oracles := congrArg (·.2.1) hz2
  rw [← h1, ← h2]
  exact hq.symm

/-- At a sub-protocol that has a part of the prover's, every step has a move. -/
theorem steps_moved {S Cl V W X : Type} {B : ProverCoinCounts} {rows : List (Addr × Due)}
    {look : Addr → (d : Due) × Cs d} {v : Option V} {blk : Block S Cl}
    {hs : List (Placed V W X)} {l : List (Step W X)} {g : Placed V W X}
    (h : chainSteps B rows look v [blk] hs = .ok l)
    (hf : (hs.find? fun g => g.place == blk.place) = some g) : ∀ s ∈ l, s.move.isSome = true := by
  intro s hs'
  have e := (chainSteps_rows [blk] hs l h).2
  have hm : (s.decl, s.oracles, s.addr.place, s.move.isSome) ∈
      l.map (fun s => (s.decl, s.oracles, s.addr.place, s.move.isSome)) :=
    List.mem_map.2 ⟨s, hs', rfl⟩
  rw [e, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hm
  obtain ⟨z, -, hz2⟩ := List.mem_map.1 hm
  have h3 : (hs.any fun h => h.place == blk.place) = s.move.isSome := congrArg (·.2.2.2) hz2
  rw [← h3, List.any_eq_true]
  have hp : (g.place == blk.place) = true :=
    List.find?_some (p := fun g : Placed V W X => g.place == blk.place) hf
  exact ⟨g, List.mem_of_find?_eq_some hf, hp⟩

/-! ## 4 The two main theorems -/

section Law
variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)
  (start : Coins Bk → W → List Fmt.Drawn → Mid W X)

/-- At a state that `play` returns over the first n sub-protocols, and at the challenges that
`fixed` counts for an own tree that these n state: what `sentAt` gives is the table of that number
of the rounds that `play` returned; and as many challenges were heard. No hypothesis on the field
`table`. -/
theorem sentAt_by_play
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
    {j : Nat} (hj1 : j < treesTo T.bs n) :
    sentAt T start j k m.st.input (m.st.heard.take (T.fixed (.own j))) =
        ((tablesOf ps)[j]?).bind id ∧
      (m.st.heard.take (T.fixed (.own j))).length = T.fixed (.own j) := by
  -- the rest of the chain's steps
  obtain ⟨rest, rfl⟩ : ∃ rest, Lall = L ++ rest := by
    have e := chainSteps_append (B := Bk) (rows := Bk.rowsOf T.chain) (look := k.look T.chain)
      (v := T.φ.sees m.st.input) T.hs (T.bs.take n) (T.bs.drop n)
    rw [List.take_append_drop, hAll, hL] at e
    obtain ⟨rest, -, hr⟩ := exMap_ok e.symm
    exact ⟨rest, hr.symm⟩
  -- counts
  have dL : L.map (·.decl) = declsTo T.bs n := steps_decl hL
  have rL : Rooted L := steps_rooted hL fun x hx => hsh x (List.mem_of_mem_take hx)
  -- the round that sends the tree
  have hjr : j < rootsSum (declsTo T.bs n) := by
    rw [← treesTo_roots T.bs hsh]
    exact hj1
  obtain ⟨r, hr⟩ := sender_found _ _ hjr
  have hsent : sentIn (T.bs.flatMap (·.rounds)) j = r := by
    unfold sentIn
    rw [decls_split T.bs n, sender_front _ _ _ hjr, hr]
    rfl
  have hrl : r < L.length := by
    have := sender_below _ _ _ hr
    rwa [← dL, List.length_map] at this
  obtain ⟨-, hb2⟩ := sender_bounds _ _ _ hr
  -- the steps and the challenges, split after that round
  have hown := play_lengths _ _ _ _ _ hp
  have hro : r < (m.st.heard.drop T.front).length := by rw [hown]; exact hrl
  obtain ⟨y', z, e1, -, e3⟩ := play_split (A := L.take (r + 1)) (B := L.drop (r + 1))
    (dA := (m.st.heard.drop T.front).take (r + 1))
    (dB := (m.st.heard.drop T.front).drop (r + 1))
    (by rw [List.length_take, List.length_take, hown])
    (by rw [List.take_append_drop, List.take_append_drop]; exact hp)
  have e3' : ps = y'.1 ++ z.1 := congrArg Prod.fst e3
  have cy' : j < (tablesOf y'.1).length := by
    rw [tables_roots _ _ _ _ _ e1 fun t ht => rL t (List.mem_of_mem_take ht), List.map_take, dL]
    exact hb2
  have hs' : sentBy (L ++ rest) ((m.st.heard.drop T.front).take r)
      (start k m.st.input (m.st.heard.take T.front)) = tablesOf y'.1 := by
    have q := sent_of_play (L[r]) (L.drop (r + 1) ++ rest)
      ((m.st.heard.drop T.front)[r]) (L.take r) ((m.st.heard.drop T.front).take r) _ y'
      (by rw [List.take_append_getElem, List.take_append_getElem]; exact e1)
      (by rw [List.length_take, List.length_take, hown])
    rw [← q]
    congr 1
    rw [← List.cons_append, ← List.append_assoc, ← List.singleton_append, ← List.append_assoc,
      List.take_append_getElem, List.take_append_drop]
  -- at the challenges that `fixed` counts
  rw [hfix j (Nat.lt_of_lt_of_le hj1 (treesTo_le_all T.bs n)), hsent]
  constructor
  · unfold sentAt
    rw [hAll]
    show ((sentBy _ ((m.st.heard.take (T.front + r)).drop T.front)
      (start k m.st.input ((m.st.heard.take (T.front + r)).take T.front)))[j]?).bind id = _
    rw [List.drop_take, Nat.add_sub_cancel_left, List.take_take,
      Nat.min_eq_left (Nat.le_add_right _ _), hs', e3', tablesOf_append,
      List.getElem?_append_left cy']
  · rw [List.length_take]
    rw [List.length_drop] at hro
    omega

/-- **`trees_by_play`, with less asked of the fields `table` and `fixed`.** Both are asked below the
chain's last tree alone: at the numbers j of the oracle messages that the chain's sub-protocols
state (why: `sentIn_beyond`, FixedSent.lean). htab is asked only at lists of challenges as long as
`fixed` counts, and only where the frame's `play` has sent a table number j; it asks the same place
and `Table.same`, no equation of tables. No default is named. -/
theorem trees_by_play_below
    (htab : ∀ j, j < treesTo T.bs T.bs.length → ∀ k w h u, h.length = T.fixed (.own j) →
      sentAt T start j k w h = some u →
      u.1 = (T.table (.own j) k w h).1 ∧ u.2.same (T.table (.own j) k w h).2 = true)
    (hfix : ∀ j, j < treesTo T.bs T.bs.length →
      T.fixed (.own j) = T.front + sentIn (T.bs.flatMap (·.rounds)) j)
    (hsh : ∀ x ∈ T.bs, Listed x) {b : Nat} {blk : Block S Cl} (hblk : T.bs[b]? = some blk)
    {k : Coins Bk} {s : S} {m : Mid W X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid W X} {cols : List OpenedColumn}
    (hT : ThrS T (PlayedTo T start) b k s m E) (hM : T.Moved blk k m E ds y cols)
    {Lall : List (Step W X)}
    (hAll : chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees m.st.input) T.bs T.hs =
      .ok Lall)
    (hsome : ∀ t ∈ tablesOf y.1, t.isSome = true) :
    T.Trees (T.fresh b) k y.2 (E.add y.1) := by
  obtain ⟨hThr, L, ps, hL, hp⟩ := hT
  unfold Thread.Moved at hM
  obtain ⟨⟨l, hl, hy⟩, -⟩ := hM
  have hlen : T.front ≤ m.st.heard.length := by
    rw [Thread.heard_length T hThr.2.1]
    exact Nat.le_add_right _ _
  obtain ⟨hL', hp'⟩ := played_next hblk hlen hL hp hl hy
  have hi := (play_mid _ _ _ _ _ hy).1
  intro σ hσ
  obtain ⟨h1, h2⟩ := List.mem_filter.1 hσ
  unfold Thread.hand at h1 h2
  rcases List.mem_append.1 h1 with ht | ho
  · simp [ht] at h2
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 ho
  have hj1 : j < treesTo T.bs (b + 1) := List.mem_range.1 hj
  have hj0 : treesTo T.bs b ≤ j := by
    by_contra hc
    have : Fmt.TreeSource.own j ∈ T.taken ++ (List.range (treesTo T.bs b)).map Fmt.TreeSource.own :=
      List.mem_append_right _ (List.mem_map.2 ⟨j, List.mem_range.2 (Nat.lt_of_not_le hc), rfl⟩)
    simp [this] at h2
  -- counts
  have dL : L.map (·.decl) = declsTo T.bs b := steps_decl hL
  have dL' : (L ++ l).map (·.decl) = declsTo T.bs (b + 1) := steps_decl hL'
  have rL : Rooted L := steps_rooted hL fun x hx => hsh x (List.mem_of_mem_take hx)
  have rL' : Rooted (L ++ l) := steps_rooted hL' fun x hx => hsh x (List.mem_of_mem_take hx)
  have cps : (tablesOf ps).length = treesTo T.bs b := by
    rw [tables_roots _ _ _ _ _ hp rL, dL, treesTo_roots T.bs hsh b]
  have call : (tablesOf (ps ++ y.1)).length = treesTo T.bs (b + 1) := by
    rw [tables_roots _ _ _ _ _ hp' rL', dL', treesTo_roots T.bs hsh (b + 1)]
  have q : (tablesOf (ps ++ y.1))[j]? = (tablesOf y.1)[j - treesTo T.bs b]? := by
    rw [tablesOf_append, List.getElem?_append_right (by omega), cps]
  -- what the play has sent, at the challenges that `fixed` counts
  obtain ⟨hs, hlt⟩ := sentAt_by_play T start hfix hsh hL' hp' (by rw [hi]; exact hAll) hj1
  -- the tree at hand
  have htree : (E.add y.1).tree (.own j) = ((tablesOf (ps ++ y.1))[j]?).bind id := by
    have hsnt : E.sent = treesTo T.bs b := hThr.2.2.2.2.1.2.2.1
    show (if j < E.sent then E.tree (.own j) else ((tablesOf y.1)[j - E.sent]?).bind id) = _
    rw [if_neg (by omega), hsnt, q]
  obtain ⟨u, hu⟩ : ∃ u, ((tablesOf (ps ++ y.1))[j]?).bind id = some u := by
    have hin' : j < (tablesOf (ps ++ y.1)).length := by
      rw [call]
      exact hj1
    have q' := q
    rw [List.getElem?_eq_getElem hin'] at q' ⊢
    have hin := hsome _ (List.mem_of_getElem? q'.symm)
    cases hv : (tablesOf (ps ++ y.1))[j] with
    | none =>
      rw [hv] at hin
      cases hin
    | some u => exact ⟨u, rfl⟩
  obtain ⟨a1, a2⟩ := htab j (Nat.lt_of_lt_of_le hj1 (treesTo_le_all T.bs (b + 1))) k _ _ u hlt
    (hs.trans hu)
  unfold Thread.handAt
  rw [htree, hu]
  show (u.1 == (T.tableAt (.own j) k y.2).1 && u.2.same (T.tableAt (.own j) k y.2).2) = true
  rw [Bool.and_eq_true, beq_iff_eq]
  exact ⟨a1, a2⟩

/-- **A sub-protocol's new trees are the tables that the `Thread` names** (the same place, and
`Table.same`), for a `Thread` whose field `table` at its own trees is `tableBy`. The other
hypotheses: see the head. -/
theorem trees_by_play (dflt : Place × Table)
    (htab : ∀ j k w h, T.table (.own j) k w h = tableBy T start dflt j k w h)
    (hfix : ∀ j, T.fixed (.own j) = T.front + sentIn (T.bs.flatMap (·.rounds)) j)
    (hsh : ∀ x ∈ T.bs, Listed x) {b : Nat} {blk : Block S Cl} (hblk : T.bs[b]? = some blk)
    {k : Coins Bk} {s : S} {m : Mid W X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid W X} {cols : List OpenedColumn}
    (hT : ThrS T (PlayedTo T start) b k s m E) (hM : T.Moved blk k m E ds y cols)
    {Lall : List (Step W X)}
    (hAll : chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees m.st.input) T.bs T.hs =
      .ok Lall)
    (hsome : ∀ t ∈ tablesOf y.1, t.isSome = true) :
    T.Trees (T.fresh b) k y.2 (E.add y.1) :=
  trees_by_play_below T start (sent_of_tableBy T start dflt fun j _ => htab j) (fun j _ => hfix j)
    hsh hblk hT hM hAll hsome

/-- **`playsS_by_play`, with less asked of the fields `table` and `fixed`**: htab and hfix as
`trees_by_play_below` asks them. -/
theorem playsS_by_play_below
    (htab : ∀ j, j < treesTo T.bs T.bs.length → ∀ k w h u, h.length = T.fixed (.own j) →
      sentAt T start j k w h = some u →
      u.1 = (T.table (.own j) k w h).1 ∧ u.2.same (T.table (.own j) k w h).2 = true)
    (hfix : ∀ j, j < treesTo T.bs T.bs.length →
      T.fixed (.own j) = T.front + sentIn (T.bs.flatMap (·.rounds)) j)
    (hsh : ∀ x ∈ T.bs, Listed x) {b : Nat} {blk : Block S Cl} (hblk : T.bs[b]? = some blk)
    {g : Placed V W X} (hf : (T.hs.find? fun g => g.place == blk.place) = some g)
    (hall : ∀ (k : Coins Bk) (w : W), ∃ Lall,
      chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees w) T.bs T.hs = .ok Lall)
    (hmv : ∀ k s m E ds l, ThrS T (PlayedTo T start) b k s m E → drawsFit blk.rounds ds = true →
      chainStopAt (T.φ.sees m.st.input) [blk] T.hs m.loc ds = none →
      chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees m.st.input) [blk] T.hs =
        .ok l → ∃ y cols, T.Moved blk k m E ds y cols) :
    PlaysS T (PlayedTo T start) b := by
  intro blk' hblk' k s m E ds l hT hd hst hl
  rw [hblk] at hblk'
  cases hblk'
  obtain ⟨y, cols, hM⟩ := hmv k s m E ds l hT hd hst hl
  obtain ⟨Lall, hAll⟩ := hall k m.st.input
  refine ⟨y, cols, hM, trees_by_play_below T start htab hfix hsh hblk hT hM hAll ?_⟩
  have hM' := hM
  unfold Thread.Moved at hM'
  obtain ⟨⟨l', hl', hy⟩, -⟩ := hM'
  exact tables_some _ _ _ _ _ hy fun s hs' => Or.inl (steps_moved hl' hf s hs')

/-- **`PlaysS` at `PlayedTo`**, at a sub-protocol that has a part of the prover's. Beside the
hypotheses on the `Thread`'s fields (htab, hfix, hsh) and on the whole chain's steps (hall), what is
left to show at the sub-protocol is hmv: its `play` and the filling of its columns return. -/
theorem playsS_by_play (dflt : Place × Table)
    (htab : ∀ j k w h, T.table (.own j) k w h = tableBy T start dflt j k w h)
    (hfix : ∀ j, T.fixed (.own j) = T.front + sentIn (T.bs.flatMap (·.rounds)) j)
    (hsh : ∀ x ∈ T.bs, Listed x) {b : Nat} {blk : Block S Cl} (hblk : T.bs[b]? = some blk)
    {g : Placed V W X} (hf : (T.hs.find? fun g => g.place == blk.place) = some g)
    (hall : ∀ (k : Coins Bk) (w : W), ∃ Lall,
      chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees w) T.bs T.hs = .ok Lall)
    (hmv : ∀ k s m E ds l, ThrS T (PlayedTo T start) b k s m E → drawsFit blk.rounds ds = true →
      chainStopAt (T.φ.sees m.st.input) [blk] T.hs m.loc ds = none →
      chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees m.st.input) [blk] T.hs =
        .ok l → ∃ y cols, T.Moved blk k m E ds y cols) :
    PlaysS T (PlayedTo T start) b :=
  playsS_by_play_below T start (sent_of_tableBy T start dflt fun j _ => htab j)
    (fun j _ => hfix j) hsh hblk hf hall hmv

end Law

end ProofFile.Honest.Small

#print axioms ProofFile.Honest.Small.play_split
#print axioms ProofFile.Honest.Small.sent_of_play
#print axioms ProofFile.Honest.Small.oracles_roots
#print axioms ProofFile.Honest.Small.tables_roots
#print axioms ProofFile.Honest.Small.sender_bounds
#print axioms ProofFile.Honest.Small.zip_of_map
#print axioms ProofFile.Honest.Small.played_next
#print axioms ProofFile.Honest.Small.saidNext_played
#print axioms ProofFile.Honest.Small.playedTo_unique
#print axioms ProofFile.Honest.Small.steps_rooted
#print axioms ProofFile.Honest.Small.tables_some
#print axioms ProofFile.Honest.Small.steps_moved
#print axioms ProofFile.Honest.Small.trees_by_play
#print axioms ProofFile.Honest.Small.playsS_by_play
#print axioms ProofFile.Honest.Small.sentAt
#print axioms ProofFile.Honest.Small.tableBy_eq
#print axioms ProofFile.Honest.Small.sentAt_congr
#print axioms ProofFile.Honest.Small.tableBy_congr
#print axioms ProofFile.Honest.Small.sent_of_tableBy
#print axioms ProofFile.Honest.Small.sentAt_by_play
#print axioms ProofFile.Honest.Small.trees_by_play_below
#print axioms ProofFile.Honest.Small.playsS_by_play_below
#print axioms ProofFile.Honest.Small.sentBy
#print axioms ProofFile.Honest.Small.Rooted
#print axioms ProofFile.Honest.Small.PlayedTo
#print axioms ProofFile.Honest.Small.tableBy
