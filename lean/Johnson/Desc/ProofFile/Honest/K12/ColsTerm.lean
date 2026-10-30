-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/ColsTerm.lean: the groups of columns that a proximity test's
declared rounds read, taken at the tables that are available after the test's rounds were played,
are the term's groups. This is `cols_term`: `colGroups` at these tables is the field `gs` of
`testAll`. It is stated at every job J (`TestJob`, Test.lean in this folder: what a caller supplies
for its test), under the hypotheses below. SaysYesK12.lean and SaysYesSeat.lean in this folder call
it. Definitions and theorems.

In the list: the frame is Johnson/Desc/ProofFile/Honest/Frame.lean. The term is `testAll J w fr C D`
(Test.lean), computed from the job, the prover's input w, a front fr (`Front`,
Johnson/Desc/ProofFile/Honest/Sum.lean: what the job's functions are given of the run before the
test), a family of coins C (`TestCoins`) and the challenges D by the round's number. Its field `gs`
is its list of groups; its field `tr` has a family of columns for each round. The stages are the
list `J.p.nums.stages`. A tree (`Tree`, Johnson/Desc/K12/Honest/Stages.lean) is a depth a and a
column for every position; its length is 2 ^ a. The job's trees, T₀ below, are
`J.trees₀ w fr C.mem (J.first w fr C)`. A group is `groupAt a poss col`
(Johnson/Prover/Link/BodyAll.lean): the pairs of a position and its column, over the set of the
sampled positions poss modulo 2 ^ a, in increasing order. An opening is a round's number, a tree's
depth, and the tree's origin or source. An origin (`From`, TermOpens.lean in this folder) is
`old k`, the job's tree number k, or `sent r`, the tree that the test's round number r sends;
`colBy` (same file) gives an origin's column. A source (`Fmt.TreeSource`, Decl/Declared.lean) is the
name by which a declared round (`Fmt.DeclaredRound`, same file) opens a tree: `own n`, tree number n of
those that this chain sends, or `taken c q`, a tree taken over from another chain. The declared
openings are `planOpens decls 0` (PlanOpens.lean in this folder). The available tables are a
structure E (`Env`, Johnson/Desc/ProofFile/Honest/Side.lean): the stored tables' columns (`stored`),
the table for a source (`tree`), and how many trees the chain has sent so far (`sent`). `E.add l` is
the same after the played rounds l (`Played`, the frame). `colAt tree σ x` (PlanOpens.lean) is the
column at position x of the table for the source σ, and the empty list where there is no table.
`colGroups` (Johnson/Desc/ProofFile/Honest/Small/ColGroups.lean) lists, round by round, for each
stored part and then for each opening that the round declares, the pairs of a position and its
column at the available tables. `treeAt J w fr C D r` (SentTables.lean in this folder) is element
number r of the term's `tr`. `depthAt J r` (Test.lean) is the depth of the tree that round number r
sends, if any, computed from the stages and from whether `J.fresh` is `none`. `sentBefore J r`
(SentTables.lean) counts the rounds below r at which `depthAt` is `some`. `msgAt` (Parts.lean in
this folder) is a round's message, taken from the term. `byNo ds` (PlayedTerm.lean in this folder)
is the list ds as a function of the round's number.

  `cols_term`: under the hypotheses below, `colGroups (E.add l).stored (E.add l).tree decls ds` is
    the field `gs` of the term at w, fr, C and the challenges `byNo ds`
  `OpensFit J decls depths src₀ sent`: a structure of four propositions. `opens`: the declared
    openings are the term's (`opensTest` at the stages and depths), one by one: the round's number,
    the depth, and the origin's source by `srcBy J src₀ sent`. `stored`: no declared round has a
    stored part. `olds`: every opening of the term with the origin `old k` has k below the length of
    depths, and its depth is element number k of depths. `senders`: every opening of the term with
    the origin `sent r` has r below the number of declared rounds, and `depthAt J r` is `some`
  `OldAt E T₀ src₀`: a structure of two propositions on the tables available before the test, each
    for every k below the length of T₀. `inFront`: if `src₀ k` is `own n`, then n is below `E.sent`.
    `cols`: at every position x below the length of tree number k, `colAt E.tree (src₀ k) x` is that
    tree's column at x
  `srcBy J src₀ sent`: a definition: an origin's source. src₀: the stated sources of the job's
    trees, by number. sent: how many trees the chain has sent before the test. `old k` has the
    source `src₀ k`; `sent r` has `own (sent + sentBefore J r)`
  `opensTest stages depths`: a definition: the term's openings over the whole test. Without a stage
    there is none; else they are `opensFrom` (TermOpens.lean) from the first stage on, whose first
    round has the number 1, at the trees `frontTrees depths`
  `frontTrees depths`: a definition: each depth of the list, paired with the origin `old k`, where k
    is its index in the list
  `gs_test`: where there is a stage, the term's `gs` is the list of `groupAt` over `opensTest` at
    the stages and the depths of T₀: at each opening's depth, at the positions in the challenge of
    its round, at its origin's column by `colBy T₀` and `treeAt`
  `test_parts`: where there is a stage, the term's `gs` is that of `stagesAll`
    (Johnson/Desc/K12/Honest/Stages.lean) at the arguments that `testAll` passes to it; the term's
    `tr` is the family of empty columns followed by the `tr` of `stagesAll`, with `freshCol`
    (Test.lean) set as its element number 0 where `J.fresh` is `none`
  `trees_front`: a list of trees T₀ is `frontTrees` of its depths, with each origin replaced by its
    column by `colBy T₀`, whatever the second argument of `colBy`
  `groupAt_congr`: two columns that agree at every position below 2 ^ a have the same
    `groupAt a poss`

By what. `cols_term` rewrites its left side by `colGroups_opens` (PlanOpens.lean: where no declared
round has a stored part, `colGroups` is the list of `groupAt` over the declared openings, at the
columns of `colAt`) and by the field `opens`, and its right side by `gs_test`. The two lists are
then compared opening by opening, and by `groupAt_congr` only at the positions below the tree's
length. At an origin `old k` the columns agree by the field `cols` of `OldAt`, since `E.add l`
leaves the chain's earlier trees and the trees taken over as they were (`add_old`, `add_taken`,
Johnson/Desc/ProofFile/Honest/Small/ColGroups.lean). At an origin `sent r`: the tables of the
chain's next trees are the played rounds' tables in the order of sending (`add_new`, same file); in
the list of all tables of the messages, the table of a round r that sends a tree has the index
`sentBefore J r` (`sent_table`, SentTables.lean); and that table's column is `treeAt` (`col_treeAt`,
SentTables.lean). `gs_test` calls `gs_stages` (TermOpens.lean: the groups of `stagesAll` are the
groups of `opensFrom`), `test_parts` and `trees_front`. `groupAt_congr` calls `listOf_lt`
(Johnson/Desc/K12/Law/ViewWide.lean).

Hypotheses of `cols_term`. hst: the stages are s :: rest: one stage or more. hdep: the depths of T₀
are the list depths. hO: `OpensFit J decls depths src₀ E.sent`. hE: `OldAt E T₀ src₀`. hT: the
tables of the rounds in l are, round by round, those of `msgAt J w fr C (byNo ds) i` for i below the
number of declared rounds, each under `some`. hl: ds has as many challenges as decls has rounds. The
lists decls, depths, ds and l, the function src₀ and E are free parameters.

Limits.
- `OpensFit` (hO), `OldAt` (hE) and the depths (hdep) are hypotheses: none of them is proved here.
  No theorem of the library concludes `OpensFit` or `OldAt`: neither condition has a value that
  meets it in the library yet.
- The field `cols` of `OldAt` does not say that a table is there. It compares through `colAt`, which
  is the empty list where there is no table: so a tree of the job whose columns are empty meets
  `cols` with no table for its source. That a table is available for each old source that is opened
  is the hypothesis hold of `cols_return` (ColsReturn.lean in this folder), not a part of `OldAt`.
- `OpensFit` reads no state, no coin and no input.
- The depths of the job's trees are, by type, a function of the input, the front and the coins: that
  they are the listed ones is a premise.
- The case in which the first fold sends its own table (`J.fresh` is `none`) is not covered: there
  the last of the job's trees is sent in the test, and `OldAt` asks that every tree of the job is
  among those sent before the test.
- Between `OldAt` and what a thread of the frame gives ("the table at hand shows what the thread's
  table shows, below its length") two things are not stated in this file: the depth is at most that
  table's length's logarithm; that table's columns are the job's tree's. The thread is `Thread`, and
  "shows what" is `Table.same` (both Johnson/Desc/ProofFile/Honest/Thread/Thr.lean). `oldAt_of_same`
  in TreesSentBeforeTestFromSameColumns.lean in this folder (not in the library yet) proves `OldAt` from that form only at a
  job made of one sending: `jobOne` in JobOne.lean in this folder (not in the library yet), with the
  table that the sending's part makes in the place of the thread's, under hypotheses of its own. So
  no file of the library derives `OldAt` from what a thread gives.
- The field `olds` of `OpensFit` could be derived from the definition of `opensTest`; that is not
  done here.
- No play is called here: l is a free parameter. hT has the form of the second conclusion of
  `played_term` (PlayedTerm.lean), which has hypotheses of its own.
- `colGroups` is not the frame's own text. That the frame's list of columns (`fillCols` at
  `readsOf`), cut into groups, is `colGroups` is `regroup_cols` (Small/ColGroups.lean), under a
  hypothesis of its own; it is not called here.
- Nothing on a decision, on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.PlayedTerm
import Johnson.Desc.ProofFile.Honest.K12.SentTables
import Johnson.Desc.ProofFile.Honest.K12.TermOpens
import Johnson.Desc.ProofFile.Honest.K12.PlanOpens
import Johnson.Desc.K12.Law.ViewWide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open ProofFile.Honest.Small (colGroups add_new add_old add_taken)

variable {W X : Type}

/-- Each depth of the list, paired with the origin `old k`, where k is its index in the list. -/
def frontTrees (depths : List ℕ) : List (ℕ × From) := depths.zipIdx.map fun x => (x.1, .old x.2)

/-- The term's openings over the whole test, from the stages and the depths of the job's trees. -/
def opensTest (stages : List Fmt.M1.Stage) (depths : List ℕ) : List (ℕ × ℕ × From) :=
  match stages with
  | [] => []
  | s :: rest => opensFrom rest s 1 (frontTrees depths)

theorem trees_front (T₀ : List Tree) (TR : ℕ → ℕ → List UInt64) :
    T₀ = (frontTrees (T₀.map (·.1))).map fun x => (x.1, colBy T₀ TR x.2) := by
  refine List.ext_getElem (by simp [frontTrees]) fun i h1 h2 => ?_
  simp only [frontTrees, List.getElem_map, List.getElem_zipIdx, colBy, Nat.zero_add]
  rw [List.getD_eq_getElem _ _ h1]

/-- Where there is a stage: the term's fields `gs` and `tr`, written out by `stagesAll`. -/
theorem test_parts (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn)
    (s : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: rest) :
    (testAll J w fr C D).gs = (stagesAll J.p (coinsOf J.p.nums.stages C.hide C.rest) rest 0 s
      (J.laid.drop 1) 1 (J.recB w fr (D 0)) (J.first w fr C)
      (J.trees₀ w fr C.mem (J.first w fr C)) D).gs ∧
    (testAll J w fr C D).tr = (fun _ => []) :: (if J.fresh.isNone then
      (stagesAll J.p (coinsOf J.p.nums.stages C.hide C.rest) rest 0 s (J.laid.drop 1) 1
        (J.recB w fr (D 0)) (J.first w fr C) (J.trees₀ w fr C.mem (J.first w fr C)) D).tr.set 0
        (freshCol (sgOf s) (J.first w fr C))
      else (stagesAll J.p (coinsOf J.p.nums.stages C.hide C.rest) rest 0 s (J.laid.drop 1) 1
        (J.recB w fr (D 0)) (J.first w fr C) (J.trees₀ w fr C.mem (J.first w fr C)) D).tr) := by
  unfold testAll
  split
  · rename_i h0
    rw [hst] at h0
    cases h0
  · rename_i s' rest' h0
    rw [hst] at h0
    obtain ⟨rfl, rfl⟩ := List.cons.inj h0
    exact ⟨rfl, rfl⟩

/-- The term's groups are the groups (`groupAt`) of its openings (`opensTest`), at the depths of the
job's trees. -/
theorem gs_test (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn)
    (s : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: rest) :
    (testAll J w fr C D).gs =
      (opensTest J.p.nums.stages ((J.trees₀ w fr C.mem (J.first w fr C)).map (·.1))).map fun x =>
        groupAt x.2.1 (D x.1).poss
          (colBy (J.trees₀ w fr C.mem (J.first w fr C)) (treeAt J w fr C D) x.2.2) := by
  obtain ⟨e1, e2⟩ := test_parts J w fr C D s rest hst
  have eo : opensTest J.p.nums.stages ((J.trees₀ w fr C.mem (J.first w fr C)).map (·.1)) =
      opensFrom rest s 1 (frontTrees ((J.trees₀ w fr C.mem (J.first w fr C)).map (·.1))) := by
    rw [hst]
    rfl
  rw [e1, eo]
  refine gs_stages J.p _ _ _ D rest 0 s _ 1 _ _ _ _ (trees_front _ _) fun i h0 _ => ?_
  unfold treeAt
  rw [e2, Nat.add_comm 1 i, List.getD_cons_succ]
  split
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega)]
  · rfl

/-- An origin's source. src₀: the stated sources of the job's trees, by number. sent: how many trees
the chain has sent before the test. -/
def srcBy (J : TestJob W X) (src₀ : ℕ → Fmt.TreeSource) (sent : ℕ) : From → Fmt.TreeSource
  | .old k => src₀ k
  | .sent r => .own (sent + sentBefore J r)

/-- Public: the declared openings are the term's. -/
structure OpensFit (J : TestJob W X) (decls : List Fmt.DeclaredRound) (depths : List ℕ)
    (src₀ : ℕ → Fmt.TreeSource) (sent : ℕ) : Prop where
  opens : planOpens decls 0 =
    (opensTest J.p.nums.stages depths).map fun x => (x.1, x.2.1, srcBy J src₀ sent x.2.2)
  stored : ∀ d ∈ decls, d.stored = []
  olds : ∀ x ∈ opensTest J.p.nums.stages depths, ∀ k, x.2.2 = .old k →
    k < depths.length ∧ x.2.1 = depths.getD k 0
  senders : ∀ x ∈ opensTest J.p.nums.stages depths, ∀ r, x.2.2 = .sent r →
    r < decls.length ∧ (depthAt J r).isSome = true

/-- On the tables available before the test: at the positions below a tree's length, the column of
the table for the stated source is the tree's; an `own` source is below `E.sent`. The column is read
by `colAt`, which is the empty list where there is no table: `cols` does not say that one is
there. -/
structure OldAt (E : Env) (T₀ : List Tree) (src₀ : ℕ → Fmt.TreeSource) : Prop where
  inFront : ∀ k, k < T₀.length → ∀ n, src₀ k = .own n → n < E.sent
  cols : ∀ k, k < T₀.length → ∀ x, x < 2 ^ (T₀.getD k (0, fun _ => [])).1 →
    colAt E.tree (src₀ k) x = (T₀.getD k (0, fun _ => [])).2 x

/-- A group reads its column only at positions below 2 ^ a, the tree's length. -/
theorem groupAt_congr (a : ℕ) (poss : List ℕ) (col col' : ℕ → List UInt64)
    (h : ∀ x, x < 2 ^ a → col x = col' x) : groupAt a poss col = groupAt a poss col' := by
  unfold groupAt
  exact List.map_congr_left fun x hx => by
    rw [h x (H2K.First.listOf_lt _ _ _ (Nat.two_pow_pos a) hx)]

/-- **`colGroups` at the tables available after the played rounds is the term's list of groups.** -/
theorem cols_term (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (ds : List Fmt.Drawn)
    (s : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: rest)
    (decls : List Fmt.DeclaredRound) (depths : List ℕ) (src₀ : ℕ → Fmt.TreeSource) (E : Env)
    (l : List Played) (hdep : (J.trees₀ w fr C.mem (J.first w fr C)).map (·.1) = depths)
    (hO : OpensFit J decls depths src₀ E.sent)
    (hE : OldAt E (J.trees₀ w fr C.mem (J.first w fr C)) src₀)
    (hT : l.map (·.tables) = (List.range decls.length).map fun i =>
      (msgAt J w fr C (byNo ds) i).tables.map some)
    (hl : ds.length = decls.length) :
    colGroups (E.add l).stored (E.add l).tree decls ds = (testAll J w fr C (byNo ds)).gs := by
  subst hdep
  rw [colGroups_opens _ _ (byNo ds) decls ds 0 hO.stored hl (fun n h => by
      rw [Nat.zero_add]
      unfold byNo
      rw [List.getD_eq_getElem _ _ h]), hO.opens, gs_test J w fr C (byNo ds) s rest hst,
    List.map_map]
  refine List.map_congr_left fun x hx => ?_
  show groupAt x.2.1 (byNo ds x.1).poss (colAt (E.add l).tree (srcBy J src₀ E.sent x.2.2)) = _
  refine groupAt_congr _ _ _ _ fun pos hpos => ?_
  cases hs : x.2.2 with
  | old k =>
    obtain ⟨hk', hdk⟩ := hO.olds x hx k hs
    have hk : k < (J.trees₀ w fr C.mem (J.first w fr C)).length := by
      rwa [List.length_map] at hk'
    have hdep' : x.2.1 = ((J.trees₀ w fr C.mem (J.first w fr C)).getD k (0, fun _ => [])).1 := by
      rw [hdk, List.getD_eq_getElem _ _ hk', List.getD_eq_getElem _ _ hk, List.getElem_map]
    rw [hdep'] at hpos
    show colAt (E.add l).tree (src₀ k) pos =
      ((J.trees₀ w fr C.mem (J.first w fr C)).getD k (0, fun _ => [])).2 pos
    rw [← hE.cols k hk pos hpos]
    unfold colAt
    cases hσ : src₀ k with
    | own n => rw [add_old E l (hE.inFront k hk n hσ)]
    | taken c q => rw [add_taken]
  | sent r =>
    obtain ⟨hr, hd⟩ := hO.senders x hx r hs
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 hd
    show colAt (E.add l).tree (.own (E.sent + sentBefore J r)) pos = treeAt J w fr C (byNo ds) r pos
    have e1 : l.flatMap (·.tables) = (List.range decls.length).flatMap fun i =>
        (msgAt J w fr C (byNo ds) i).tables.map some := by
      rw [List.flatMap_def, hT, ← List.flatMap_def]
    have e2 := add_new E l (sentBefore J r)
    rw [e1, sent_table J w fr C (byNo ds) decls.length r a hr ha] at e2
    unfold colAt
    cases ht : (E.add l).tree (.own (E.sent + sentBefore J r)) with
    | none =>
      rw [ht] at e2
      cases e2
    | some u =>
      rw [ht] at e2
      have e3 : u.2 = tableOf a (treeAt J w fr C (byNo ds) r) := Option.some.inj e2
      show u.2.col pos = _
      rw [e3, col_treeAt]

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.trees_front
#print axioms ProofFile.Honest.K12.test_parts
#print axioms ProofFile.Honest.K12.gs_test
#print axioms ProofFile.Honest.K12.groupAt_congr
#print axioms ProofFile.Honest.K12.cols_term
#print axioms ProofFile.Honest.K12.frontTrees
#print axioms ProofFile.Honest.K12.opensTest
#print axioms ProofFile.Honest.K12.srcBy
#print axioms ProofFile.Honest.K12.OpensFit
#print axioms ProofFile.Honest.K12.OldAt
