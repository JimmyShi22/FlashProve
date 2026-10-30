-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/FitsAll.lean: every message of a proximity test's term has the
shape that its declared round states (`Sending.fits`, Johnson/Desc/ProofFile/Honest/Frame.lean),
under two clauses on the plan: the declared rounds ask just the sorts of items that the term shows;
each declared oracle message has the depth and the width of the tree that the term sends in that
round. Whatever the input, the front, the coins and the challenges. Definitions, none marked
`noncomputable`, and theorems with their proofs.

In the list: the term is `testAll J w fr C D` (Test.lean in this folder). It defines a test's rounds
(`rs`), for each round the written column of the tree that it sends (`tr`; the empty column where it
sends none) and the opened columns, as a function of a job J (`TestJob`: what a caller supplies for
its test), the prover's input w, the front fr (`Front`, Johnson/Desc/ProofFile/Honest/Sum.lean: what
precedes the test), the coins C (`TestCoins`) and the challenges D by the round's number. Round 0 is
the batching's round "BAT"; the other rounds are those of `stagesAll`
(Johnson/Desc/K12/Honest/Stages.lean). The plan, also called the place, is `J.p` (`P12`,
Johnson/Desc/K12/Frame.lean: the test's parameters), with its list of stages `J.p.nums.stages`
(`Fmt.M1.Stage`). h and g are those of `sgOf` of a stage (Johnson/Desc/K12/Law/ChainOf.lean), where
g is k - h. A stage that is not the last has the rounds of a fold and the two rounds of a switch,
which leads to the next stage. `J.fresh` names who sent the first fold's fresh table; where it is
`none`, the fold sends the table itself. `laidOf p` (Johnson/Desc/K12/Law/ReadsK.lean) pairs each
declared round (`Fmt.DeclaredRound`) with its declared oracle messages (`Oracle`,
Johnson/Desc/Oracle.lean). `msgAt J w fr C D i` (Parts.lean in this folder) is the message
(`Sending`, Frame.lean) of round number i: the items of the term's round, without roots, and one
table where `depthAt J i` (Test.lean) gives a depth. `treeAt J w fr C D i` (SentTables.lean in this
folder) is the column that the term lists at round i. The width of a tree is here the length of its
column at position 0: that is what `msgAt` sets as the table's `words`. `sortsOf`
(Johnson/Prover/Link/LinkItems.lean) lists the sorts of a round's items; `asked`
(Johnson/Prover/Link/BodySorts.lean) lists a declared round's items without the roots.
`Sending.fits` compares the sorts of the message's items with the declared round's items without the
roots, and the log-length and the words of each table with those of the declared oracle messages.

  `fits_all`: under the four hypotheses below, `(msgAt J w fr C D i).fits d.1 d.2` is true: the
    message of every round that the place declares fits what the round states
  `tablesFitB J`: a definition: the second clause as a test that returns a Bool. At every number i
    of a declared round: where `depthAt J i` gives a depth a, the round declares just one oracle
    message, of log-length a and of the words that `widthsOf J.fresh.isNone J.p.nums.stages` has at
    i; where it gives none, the round declares no oracle message. Of the job it reads only the place
    and whether `J.fresh` is `none`
  `stages_sorts`, `test_sorts`: the sorts of the items that the term's rounds show: a list of the
    stages' numbers alone (`bodyItems`, Johnson/Prover/Link/LinkItems.lean). As Lean has it:
    `sortsOf` of the rounds of `stagesAll`, at all its arguments, is `bodyItems cur rest`; where the
    place's stages are s :: rest, `sortsOf` of the rounds of `testAll` is `[] :: bodyItems s rest`,
    so "BAT" has no item
  `colW last next`: a definition: the width of the tree that a switch sends: 12 where the next stage
    is the last (`last`), else 3 * 2 ^ (h + g) + 3 * (2 * 2 ^ h) at the next stage's h and g
  `length_aCol'`: the column of a switch's tree (`aCol`, Stages.lean) has `colW last next` words, at
    every state of the prover and every position
  `widthsFrom cur rest`: a definition: a width for each round of the stages from cur on. At a stage
    that is not the last: 0 for each of the fold's 1 + (h + g) rounds, `colW` for the switch's first
    round, 0 for its second. At the last stage: 0 for each of its two rounds
  `widthsOf own stages`: a definition: the same for the test's rounds: 0 for "BAT", then
    `widthsFrom`. Where own is true (the first fold sends its own table), round 1 has 3 * 2 ^ h at
    the first stage's h instead of 0. At no stage: the empty list
  `stages_widths`, `test_widths`, `width_treeAt`: the term's trees have these widths. The columns at
    position 0 that `stagesAll` lists have the lengths `widthsFrom cur rest`; those that `testAll`
    lists have the lengths `widthsOf J.fresh.isNone J.p.nums.stages`; and `treeAt J w fr C D i 0`
    has the length that this list has at i, or 0 beyond its end. No hypothesis

By what. `stages_sorts` goes by recursion on the list of stages, with `aFold_sorts` (FormDraws.lean
in this folder) at a fold and `items_e` and `length_shownAll` (LinkItems.lean) at the last stage.
`length_aCol'` calls `length_stageColW` (Johnson/Prover/Link/HyStage.lean) and `length_words12`
(TableCol.lean in this folder). `stages_widths` goes by the same recursion, with `length_aCol'` and
`length_aFold` (Johnson/Desc/K12/Honest/Causal.lean); `test_widths` adds `length_freshCol`
(FreshCols.lean in this folder). `fits_all` unfolds `Sending.fits`. For the items: by `msgAt_vals`
(Canon.lean in this folder), `Said.got` of the message's items gives the items of the term's round;
their sorts are the declared ones by `test_sorts` and the first clause. For the tables:
`msgAt_tables` (SentTables.lean), `width_treeAt` and the second clause.

Hypotheses of `fits_all`. hst: the place's list of stages is s :: rest: one stage or more. hS: the
first clause: `asked` of the rounds of `laidOf J.p` is `[] :: bodyItems s rest`. hT: the second
clause: `tablesFitB J` is true. hd: d is element number i of `laidOf J.p`: a declared round with its
oracle messages.

Limits. The two clauses are hypotheses: they are shown of no place here. At a list of one stage
`fits_all` is vacuous: `roundsOfNums` (Johnson/Desc/K12/TestEntries.lean) returns rounds from two
stages on only, so `laidOf J.p` is empty and hS and hd are false. The widths are those of the
columns at position 0: that a tree's columns have one width at all positions is stated in
SentTables.lean (`good_test`), not here. `depthAt` counts a fold's rounds as 1 + k, `widthsFrom` as
1 + (h + g): one number where h is at most k, which is no hypothesis here. Nothing on a decision, on
completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.FormDraws
import Johnson.Desc.ProofFile.Honest.K12.SentTables
import Johnson.Desc.ProofFile.Honest.K12.Canon

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)

variable {W X : Type}

/-! ## 1 The sorts -/

theorem stages_sorts (p : P12) (K : BCoins) (D : ℕ → Fmt.Drawn) : ∀ (rest : List Fmt.M1.Stage)
    (j : ℕ) (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS) (trees : List Tree),
    (stagesAll p K rest j cur l o t P trees D).rs.map sortsOf = bodyItems cur rest
  | [], j, cur, l, o, t, P, trees => by
    show [[Fmt.Item.e], ((shownAll _ _ _ _ _ _ _ _ _ _ _).map Fmt.ItemValue.e).map itemOf] = _
    rw [items_e, length_shownAll]
    rfl
  | next :: rest, j, cur, l, o, t, P, trees => by
    simp only [stagesAll, List.map_append, aFold_sorts, stages_sorts p K D rest]
    rfl

theorem test_sorts (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn)
    (s : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: rest) :
    (testAll J w fr C D).rs.map sortsOf = [] :: bodyItems s rest := by
  unfold testAll
  split
  · rename_i h0
    rw [hst] at h0
    cases h0
  · rename_i s' rest' h0
    rw [hst] at h0
    obtain ⟨rfl, rfl⟩ := List.cons.inj h0
    show [] :: (stagesAll _ _ _ _ _ _ _ _ _ _ _).rs.map sortsOf = _
    rw [stages_sorts]

/-! ## 2 The widths -/

/-- The width of the tree that a switch sends. `last`: the next stage is the last. -/
def colW (last : Bool) (next : Fmt.M1.Stage) : ℕ :=
  if last then 12 else 3 * 2 ^ ((sgOf next).h + (sgOf next).g) + 3 * (2 * 2 ^ (sgOf next).h)

theorem length_aCol' (last : Bool) (next : Fmt.M1.Stage) (Q : PS) (x : ℕ) :
    (aCol last next Q x).length = colW last next := by
  unfold aCol colW
  cases last
  · simp only [Bool.false_eq_true, if_false, length_stageColW]
  · simp only [if_true, lastCol, length_words12]

/-- For each round of the stages from a stage on: the width of what the term lists as its tree; 0
where it lists the empty column. -/
def widthsFrom : Fmt.M1.Stage → List Fmt.M1.Stage → List ℕ
  | _, [] => [0, 0]
  | cur, next :: rest =>
    List.replicate (1 + ((sgOf cur).h + (sgOf cur).g)) 0 ++ [colW rest.isEmpty next, 0] ++
      widthsFrom next rest

theorem stages_widths (p : P12) (K : BCoins) (D : ℕ → Fmt.Drawn) : ∀ (rest : List Fmt.M1.Stage)
    (j : ℕ) (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS) (trees : List Tree),
    (stagesAll p K rest j cur l o t P trees D).tr.map (fun c => (c 0).length) =
      widthsFrom cur rest
  | [], _, _, _, _, _, _, _ => rfl
  | next :: rest, j, cur, l, o, t, P, trees => by
    simp only [stagesAll, List.map_append, List.map_map, List.map_cons, List.map_nil,
      stages_widths p K D rest, length_aCol', widthsFrom]
    congr 2
    show List.map (fun _ => 0) (aFold K j cur o P (rowOf t) D) = _
    rw [List.map_const', length_aFold]

/-- The same for the test's rounds, "BAT" being round 0. `own`: the first fold sends its own
table. -/
def widthsOf (own : Bool) : List Fmt.M1.Stage → List ℕ
  | [] => []
  | s :: rest =>
    0 :: (if own then (widthsFrom s rest).set 0 (3 * 2 ^ (sgOf s).h) else widthsFrom s rest)

theorem test_widths (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn) :
    (testAll J w fr C D).tr.map (fun c => (c 0).length) =
      widthsOf J.fresh.isNone J.p.nums.stages := by
  unfold testAll
  split
  · rename_i h0
    rw [h0]
    rfl
  · rename_i s rest h0
    rw [h0]
    show 0 :: List.map _ (if J.fresh.isNone = true then _ else _) = _
    unfold widthsOf
    cases J.fresh.isNone
    · simp only [Bool.false_eq_true, if_false, stages_widths]
    · simp only [if_true, List.map_set, stages_widths, length_freshCol]

theorem width_treeAt (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn)
    (i : ℕ) :
    (treeAt J w fr C D i 0).length = (widthsOf J.fresh.isNone J.p.nums.stages).getD i 0 := by
  rw [← test_widths J w fr C D]
  unfold treeAt
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases (testAll J w fr C D).tr[i]? <;> rfl

/-! ## 3 Every message fits -/

/-- Each declared oracle message has the depth and the width of the tree that the term sends. As a
test: at every declared round, the list of the log-length and the words of its oracle messages is
the one pair of `depthAt` and `widthsOf` at the round's number, or empty where `depthAt` gives no
depth. -/
def tablesFitB (J : TestJob W X) : Bool :=
  (List.range (laidOf J.p).length).all fun i =>
    (depthAt J i).toList.map (fun a => (a, (widthsOf J.fresh.isNone J.p.nums.stages).getD i 0)) ==
      ((((laidOf J.p)[i]?).map fun d => d.2).getD []).map fun o => (o.logLength, o.words)

/-- **Every message of the term fits what its round states.** Under the two clauses hS and hT, at a
round that the place declares (hd). At a list of one stage hS and hd are false, so the theorem is
vacuous there: see the head's limits. -/
theorem fits_all (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn)
    (s : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: rest)
    (hS : (laidOf J.p).map asked = [] :: bodyItems s rest) (hT : tablesFitB J = true) (i : ℕ)
    (d : Fmt.DeclaredRound × List VerifiableInference.Desc.Oracle) (hd : (laidOf J.p)[i]? = some d) :
    (msgAt J w fr C D i).fits d.1 d.2 = true := by
  have hi : i < (laidOf J.p).length := (List.getElem?_eq_some_iff.1 hd).1
  have e := (test_sorts J w fr C D s rest hst).trans hS.symm
  obtain ⟨r, hr⟩ : ∃ r, (testAll J w fr C D).rs[i]? = some r := by
    have hl := congrArg List.length e
    rw [List.length_map, List.length_map] at hl
    exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have e1 := congrArg (·[i]?) e
  simp only [List.getElem?_map, hr, hd, Option.map_some] at e1
  have e2 : sortsOf r = asked d := Option.some.inj e1
  unfold Sending.fits
  rw [Bool.and_eq_true]
  constructor
  · rw [beq_iff_eq]
    have k := msgAt_vals J w fr C D i r hr
    have : (msgAt J w fr C D i).vals.map (fun v => itemOf v.got) =
        ((msgAt J w fr C D i).vals.map Said.got).map itemOf := by rw [List.map_map]; rfl
    rw [this, k]
    exact e2
  · unfold tablesFitB at hT
    have k := List.all_eq_true.1 hT i (List.mem_range.2 hi)
    rw [hd] at k
    rw [msgAt_tables, List.map_map]
    rw [beq_iff_eq] at k ⊢
    refine Eq.trans ?_ k
    refine List.map_congr_left fun a _ => ?_
    show (a, (treeAt J w fr C D i 0).length) = _
    rw [width_treeAt]

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.stages_sorts
#print axioms ProofFile.Honest.K12.test_sorts
#print axioms ProofFile.Honest.K12.length_aCol'
#print axioms ProofFile.Honest.K12.stages_widths
#print axioms ProofFile.Honest.K12.test_widths
#print axioms ProofFile.Honest.K12.width_treeAt
#print axioms ProofFile.Honest.K12.fits_all
#print axioms ProofFile.Honest.K12.colW
#print axioms ProofFile.Honest.K12.widthsFrom
#print axioms ProofFile.Honest.K12.widthsOf
#print axioms ProofFile.Honest.K12.tablesFitB
