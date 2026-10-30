-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Small/SaysYesOf.lean: `SaysYes` and `PlaysOn`, the two propositions
that Honest/Law/ThreadC.lean defines for one sub-protocol b of a chain, each follow from a
hypothesis in terms of the prover's part g for b (a `Placed`, Honest/Frame.lean). For `SaysYes` the
hypothesis is that b's own field `decide` returns, with no error, on the rounds that `play` returns
over g's steps and on the columns that are read after them. It is for whoever has to show the two
propositions for one kind of sub-protocol. General in b and g: no kind of sub-protocol is named. One
definition, statements and proofs; the main proofs join lemmas of other files.

  `saysYes_of_play`: `SaysYes` holds if, wherever `YesGiven` holds, `b.decide` returns at the
    verifier's state s, on the rounds of y.1 without the sealed digest, and on `colGroups`
    (ColGroups.lean): the columns that b's rounds read at the challenges ds from the tables
    `E.add y.1`, in groups
  `saysYes_of`: the same with a list l of rounds in place of y: where `YesGiven` has the return of
    `play`, the hypothesis has `playedRow` = some l (each move of `g.parts` returns a message; l:
    the rounds as played) and `fitsRow` = true (each message has the shape that its round states;
    both PlayRow.lean); the other fields of `YesGiven` are written out
  `playsOn_of`: `PlaysOn` holds if, under the fields `stand`, `draws`, `silent`, `laid`, `lent`,
    `oracles` and `rounds` of `YesGiven`, written out, there are l and cols such that `playedRow` =
    some l, `fitsRow` = true, `fillCols` returns cols at the tables `E.add l`, and, wherever
    `b.step` returns on l's rounds and cols, B holds at the state after l, which has taken cols
    (`Mid.took`), and at `E.add l`
  `YesGiven`: a definition: the hypotheses of `SaysYes`, stated for g, with what follows from them
    on g's coins and on the lengths. Its fields: see Hypotheses
  `member_played`: where `chainSteps` returns l for b and `play` over l returns y: `lendRow` returns
    coins c, l is `g.steps b v c`, `playedRow` is some y.1, `fitsRow` is true, and the state y.2 is
    written out
  `row_silent`, `member_silent`: at challenges that pass `drawsFit`, `rowStopAt` at `g.parts` is
    `none` where `chainStopAt` at the list [b] is, and the converse
  `member_lengths`: where `chainSteps` returns for b, b has as many lists of oracle messages as
    rounds, and `g.rounds` is the number of b's rounds
  `placed_rounds`, `zip_length`: `g.rounds` is the sum of the numbers of moves of the `Part`s in
    `g.parts`; under the two equations of `member_lengths` so is the length of
    `b.rounds.zip b.oracles`

By what. `SaysYes` speaks of the steps that `chainSteps` returns for b, of the columns in the one
list that `fillCols` returns, and of `Block.step` (Johnson/Desc/Block.lean). A lemma on one kind of
sub-protocol speaks of the `Part`s in `g.parts`, of the tables' columns in groups, and of the field
`decide`. Between the two: `steps_one_half` (Honest/Law/Thread.lean): the steps that `chainSteps`
returns for b are `g.steps b v c`, at coins c that `lendRow` returns. `step_iff_decide`
(Honest/Law/Cut.lean): on rounds that `play` returned and columns that `fillCols` returned, `b.step`
returns s' and the number of the columns just where `b.decide` returns s' on the columns cut into
groups. `regroup_cols` (ColGroups.lean): these groups are `colGroups`. `played_of_play`
(PlayRow.lean): from a return of `play` to `playedRow` and `fitsRow`; `play_row_whole` (same file):
back, where `rowStopAt` is `none`. Small facts: `exIte_ok` (Honest/Law/Play.lean), `or_none`
(Honest/Law/Thread.lean), `drawsFit_length` (Honest/Law/Along.lean).

Hypotheses. hf, in every theorem but `placed_rounds` and `zip_length`: `hs.find?` at b's place
returns g. H, in the three main theorems: as listed above. The fields of `YesGiven`, at a run's
coins k, the verifier's state s before b, a state m of the prover's run (`Mid`), tables E (`Env`,
Honest/Side.lean) and challenges ds; v stands for `φ.sees m.st.input`. `stand`: the parameter A
holds at k, s, m and E. `draws`: ds passes `drawsFit b.rounds`. `silent`: `rowStopAt` at v,
`g.parts`, m.loc and ds is `none`: no `Part` of g stops at these challenges. `noFall`: the parameter
`fall` at s and ds is `none`. `laid`: `chainSteps`, at the chain's rows of the `ProverCoinCounts` and at k's
coins for the chain, returns `g.steps b v c` for [b]. `lent`: `lendRow` returns c for `g.parts`.
`oracles`, `rounds`: the two equations of `member_lengths`. `played`: `play` over these steps, at ds
and from m, with no stored run to fall back on, returns y. `filled`: `fillCols`, on what b's rounds
read at ds from the tables `E.add y.1`, with no stored column to fall back on, returns cols.

Limits. Conditional lemmas on the frame's own definitions. The hypothesis H of the three main
theorems is shown here for no kind of sub-protocol: whoever uses one of them for a kind has to show
it. `SaysYes` and `PlaysOn` hold vacuously where `chainSteps … [b] hs` returns an error, and
`SaysYes` also where `play` or `fillCols` does. So whoever shows one of the two for a sub-protocol
has to show beside it that `chainSteps` returns. This is a limit of Honest/Law/ThreadC.lean itself;
Honest/Thread/Laid.lean has that return of `chainSteps`, at all coins, for each sub-protocol of a
description's three chains, from one return of `ready` (Honest/Frame.lean). No statement here is for
a sub-protocol that has no part of the prover's: hf fails there. Nothing on how likely it is that a
`Part` stops or that `fall` is not `none`. No property of a protocol is stated: nothing on
completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Small.PlayRow
import Johnson.Desc.ProofFile.Honest.Small.ColGroups
import Johnson.Desc.ProofFile.Honest.Law.ThreadC
import Johnson.Desc.ProofFile.Honest.Law.Cut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Small
open VerifiableInference.Desc (Block Place OpenedColumn noDigest)

variable {S Cl V W Y Pb : Type}

/-- `g.rounds` is the sum of the numbers of moves of the `Part`s in `g.parts`. -/
theorem placed_rounds (g : Placed V W Y) : g.rounds = (g.parts.map (·.moves.length)).sum := by
  unfold Placed.rounds
  have : ∀ (l : List (Part V W Y)) (n : Nat),
      l.foldl (fun n p => n + p.moves.length) n = n + (l.map (·.moves.length)).sum := by
    intro l
    induction l with
    | nil => intro n; rfl
    | cons p l ih =>
      intro n
      rw [List.foldl_cons, ih, List.map_cons, List.sum_cons, Nat.add_assoc]
  rw [this, Nat.zero_add]

/-- Where b has one list of oracle messages for each round and g has as many rounds as b, the list
`b.rounds.zip b.oracles` is as long as the `Part`s in `g.parts` have moves together. -/
theorem zip_length {b : Block S Cl} {g : Placed V W Y} (ho : b.oracles.length = b.rounds.length)
    (hr : g.rounds = b.rounds.length) :
    (b.rounds.zip b.oracles).length = (g.parts.map (·.moves.length)).sum := by
  rw [List.length_zip, ho, Nat.min_self, ← hr, placed_rounds]

section
variable {Bk : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d} {v : Option V}
  {b : Block S Cl} {hs : List (Placed V W Y)} {l : List (Step W Y)} {g : Placed V W Y}

/-- Where `chainSteps` returns for b and g is the prover's part for b: b has as many lists of oracle
messages as rounds, and g has as many rounds as b. Both are tests that `chainSteps` itself makes. -/
theorem member_lengths (hf : (hs.find? fun g => g.place == b.place) = some g)
    (h : chainSteps Bk rows look v [b] hs = .ok l) :
    b.oracles.length = b.rounds.length ∧ g.rounds = b.rounds.length := by
  simp only [chainSteps, hf] at h
  obtain ⟨h1, h⟩ := exIte_ok h
  obtain ⟨h2, -⟩ := exIte_ok h
  exact ⟨by simpa using h1, by simpa using h2⟩

/-- **What `chainSteps` and `play` have returned for b, written out in terms of g.** Where
`chainSteps` returns l and `play` over l returns y: `lendRow` returns coins c, l is `g.steps b v c`,
the rounds y.1 are those of `playedRow`, `fitsRow` is true, and the state y.2 is that of `stateRow`,
with ds appended to `m.loc`, the rounds of y.1 to `m.seen`, and m's own field `opened`. -/
theorem member_played (hf : (hs.find? fun g => g.place == b.place) = some g)
    (h : chainSteps Bk rows look v [b] hs = .ok l) {ds : List Fmt.Drawn} {m : Mid W Y}
    {y : List Played × Mid W Y} (hy : play l ds [] m = .ok y) :
    ∃ c, lendRow Bk rows look b.place g.parts 0 = .ok c ∧ l = g.steps b v c ∧
      playedRow b.name b.place g.parts 0 c m.st m.shown ds = some y.1 ∧
      fitsRow g.parts (b.rounds.zip b.oracles) c m.st m.shown ds = true ∧
      y.2 = ⟨stateRow g.parts m.st ds, m.loc ++ ds, m.seen ++ roundsOf y.1, m.opened⟩ := by
  obtain ⟨ho, hr⟩ := member_lengths hf h
  obtain ⟨c, hc, rfl⟩ := steps_one_half hf h
  obtain ⟨a1, a2, a3⟩ :=
    played_of_play b.name b.place v g.parts 0 _ c ds [] m y (zip_length ho hr) hy
  exact ⟨c, hc, rfl, a1, a2, a3⟩

end

section
variable (φ : Face V W Pb) (Bk : ProverCoinCounts) (chain ft : Nat) (hs : List (Placed V W Y))
  (b : Block S Cl) (fall : S → List Fmt.Drawn → Option String)
  (A : Coins Bk → S → Mid W Y → Env → Prop) (g : Placed V W Y)

/-- **The hypotheses of `SaysYes`, stated for the prover's part g**, with what follows from them:
the coins c that `lendRow` returns, and the two equations on lengths. It is a definition: the form
of a hypothesis. -/
structure YesGiven (k : Coins Bk) (s : S) (m : Mid W Y) (E : Env) (ds : List Fmt.Drawn)
    (c : RowCoins g.parts) (y : List Played × Mid W Y) (cols : List OpenedColumn) : Prop where
  stand : A k s m E
  draws : drawsFit b.rounds ds = true
  silent : rowStopAt (φ.sees m.st.input) g.parts m.loc ds = none
  noFall : fall s ds = none
  laid : chainSteps Bk (Bk.rowsOf chain) (k.look chain) (φ.sees m.st.input) [b] hs =
    .ok (g.steps b (φ.sees m.st.input) c)
  lent : lendRow Bk (Bk.rowsOf chain) (k.look chain) b.place g.parts 0 = .ok c
  oracles : b.oracles.length = b.rounds.length
  rounds : g.rounds = b.rounds.length
  played : play (g.steps b (φ.sees m.st.input) c) ds [] m = .ok y
  filled : fillCols (readsOf chain ft (E.add y.1).stored (E.add y.1).tree b.rounds ds) [] =
    .ok cols

end

section
variable {φ : Face V W Pb} {Bk : ProverCoinCounts} {chain ft : Nat} {hs : List (Placed V W Y)}
  {b : Block S Cl} {fall : S → List Fmt.Drawn → Option String}
  {A B : Coins Bk → S → Mid W Y → Env → Prop} {g : Placed V W Y}

/-- At challenges that pass `drawsFit`: where `chainStopAt` at the list [b] is `none`, so is
`rowStopAt` at `g.parts`. The proof is that of `stop_one` (Honest/Law/ThreadC.lean), word for word,
with b and g in place of a `Side`'s `block` and `half`. -/
theorem row_silent (hf : (hs.find? fun g => g.place == b.place) = some g) {m : Mid W Y}
    {ds : List Fmt.Drawn} (hd : drawsFit b.rounds ds = true)
    (hst : chainStopAt (φ.sees m.st.input) [b] hs m.loc ds = none) :
    rowStopAt (φ.sees m.st.input) g.parts m.loc ds = none := by
  have hlen := drawsFit_length _ _ hd
  have hst' : ((hs.find? fun g => g.place == b.place).bind fun g =>
      rowStopAt (φ.sees m.st.input) g.parts m.loc (ds.take b.rounds.length)).or
        (none : Option Why) = none := hst
  rw [hf, ← hlen, List.take_length] at hst'
  exact (or_none hst').1

/-- The converse: where `rowStopAt` at `g.parts` is `none`, so is `chainStopAt` at the list [b]. -/
theorem member_silent (hf : (hs.find? fun g => g.place == b.place) = some g) {m : Mid W Y}
    {ds : List Fmt.Drawn} (hd : drawsFit b.rounds ds = true)
    (hst : rowStopAt (φ.sees m.st.input) g.parts m.loc ds = none) :
    chainStopAt (φ.sees m.st.input) [b] hs m.loc ds = none := by
  have hlen := drawsFit_length _ _ hd
  show ((hs.find? fun g => g.place == b.place).bind fun g =>
      rowStopAt (φ.sees m.st.input) g.parts m.loc (ds.take b.rounds.length)).or
        (none : Option Why) = none
  rw [hf, ← hlen, List.take_length]
  show (rowStopAt (φ.sees m.st.input) g.parts m.loc ds).or none = none
  rw [hst]
  rfl

/-- **`SaysYes` holds if `b.decide` returns wherever `YesGiven` holds**: on the rounds of y.1
without the sealed digest, and on `colGroups` at the tables `E.add y.1`. -/
theorem saysYes_of_play (hf : (hs.find? fun g => g.place == b.place) = some g)
    (H : ∀ k s m E ds c y cols, YesGiven φ Bk chain ft hs b fall A g k s m E ds c y cols →
      ∃ s', b.decide s ((roundsOf y.1).map noDigest)
        (colGroups (E.add y.1).stored (E.add y.1).tree b.rounds ds) = .ok s') :
    SaysYes φ Bk chain ft hs b fall A := by
  intro k s m E ds l y cols hA hd hst hfall hl hy hc
  obtain ⟨ho, hr⟩ := member_lengths hf hl
  obtain ⟨c, hc', rfl⟩ := steps_one_half hf hl
  obtain ⟨s', hs'⟩ := H k s m E ds c y cols
    ⟨hA, hd, row_silent hf hd hst, hfall, hl, hc', ho, hr, hy, hc⟩
  refine ⟨s', cols.length, (step_iff_decide s s' hr ho hy hd hc).2 ?_⟩
  rw [regroup_cols _ _ _ _ hc]
  exact hs'

/-- **The same with `playedRow` and `fitsRow` in place of `play`.** The hypothesis H speaks of a
list l of rounds with `playedRow` = some l and `fitsRow` = true, and not of y. Under H's hypotheses
`play` does return l (`play_row_whole`, PlayRow.lean; the proof here does not call it). -/
theorem saysYes_of (hf : (hs.find? fun g => g.place == b.place) = some g)
    (H : ∀ k s m E ds c l cols, A k s m E → drawsFit b.rounds ds = true →
      rowStopAt (φ.sees m.st.input) g.parts m.loc ds = none → fall s ds = none →
      chainSteps Bk (Bk.rowsOf chain) (k.look chain) (φ.sees m.st.input) [b] hs =
        .ok (g.steps b (φ.sees m.st.input) c) →
      lendRow Bk (Bk.rowsOf chain) (k.look chain) b.place g.parts 0 = .ok c →
      b.oracles.length = b.rounds.length → g.rounds = b.rounds.length →
      playedRow b.name b.place g.parts 0 c m.st m.shown ds = some l →
      fitsRow g.parts (b.rounds.zip b.oracles) c m.st m.shown ds = true →
      fillCols (readsOf chain ft (E.add l).stored (E.add l).tree b.rounds ds) [] = .ok cols →
      ∃ s', b.decide s ((roundsOf l).map noDigest)
        (colGroups (E.add l).stored (E.add l).tree b.rounds ds) = .ok s') :
    SaysYes φ Bk chain ft hs b fall A :=
  saysYes_of_play hf fun k s m E ds c y cols h => by
    obtain ⟨a1, a2, -⟩ := played_of_play b.name b.place _ g.parts 0 _ c ds [] m y
      (zip_length h.oracles h.rounds) h.played
    exact H k s m E ds c y.1 cols h.stand h.draws h.silent h.noFall h.laid h.lent h.oracles h.rounds
      a1 a2 h.filled

/-- **`PlaysOn` from `playedRow`, `fitsRow`, `fillCols`, and B after `b.step`.** The hypothesis H,
in terms of g: where A holds, no `Part` of g stops and `lendRow` returns c, there are l and cols
such that `playedRow` = some l, `fitsRow` = true, `fillCols` returns cols at the tables `E.add l`,
and B holds, at the state after l that has taken cols (`Mid.took`), wherever `b.step` returns on l's
rounds and cols. -/
theorem playsOn_of (hf : (hs.find? fun g => g.place == b.place) = some g)
    (H : ∀ k s m E ds c, A k s m E → drawsFit b.rounds ds = true →
      rowStopAt (φ.sees m.st.input) g.parts m.loc ds = none →
      chainSteps Bk (Bk.rowsOf chain) (k.look chain) (φ.sees m.st.input) [b] hs =
        .ok (g.steps b (φ.sees m.st.input) c) →
      lendRow Bk (Bk.rowsOf chain) (k.look chain) b.place g.parts 0 = .ok c →
      b.oracles.length = b.rounds.length → g.rounds = b.rounds.length →
      ∃ l cols, playedRow b.name b.place g.parts 0 c m.st m.shown ds = some l ∧
        fitsRow g.parts (b.rounds.zip b.oracles) c m.st m.shown ds = true ∧
        fillCols (readsOf chain ft (E.add l).stored (E.add l).tree b.rounds ds) [] = .ok cols ∧
        ∀ s' n, b.step ft s (roundsOf l) cols = .ok (s', n) →
          B k s' (Mid.took ⟨stateRow g.parts m.st ds, m.loc ++ ds, m.seen ++ roundsOf l, m.opened⟩
            cols) (E.add l)) :
    PlaysOn φ Bk chain ft hs b A B := by
  intro k s m E ds l hA hd hst hl
  obtain ⟨ho, hr⟩ := member_lengths hf hl
  obtain ⟨c, hc, rfl⟩ := steps_one_half hf hl
  have hs' := row_silent hf hd hst
  obtain ⟨p, cols, h1, h2, h3, h4⟩ := H k s m E ds c hA hd hs' hl hc ho hr
  exact ⟨(p, ⟨stateRow g.parts m.st ds, m.loc ++ ds, m.seen ++ roundsOf p, m.opened⟩), cols,
    play_row_whole b.name b.place _ g.parts 0 _ c ds [] m p hs' h2 h1, h3, h4⟩

end

end ProofFile.Honest.Small

#print axioms ProofFile.Honest.Small.member_lengths
#print axioms ProofFile.Honest.Small.member_played
#print axioms ProofFile.Honest.Small.row_silent
#print axioms ProofFile.Honest.Small.member_silent
#print axioms ProofFile.Honest.Small.saysYes_of_play
#print axioms ProofFile.Honest.Small.saysYes_of
#print axioms ProofFile.Honest.Small.playsOn_of
#print axioms ProofFile.Honest.Small.placed_rounds
#print axioms ProofFile.Honest.Small.zip_length
#print axioms ProofFile.Honest.Small.YesGiven
