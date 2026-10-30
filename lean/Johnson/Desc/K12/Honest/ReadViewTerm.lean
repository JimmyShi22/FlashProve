-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/ReadViewTerm.lean: the view's half of what the reading of the old rows asks
(`ReadView`, Johnson/Desc/K12/Honest/ReadPub.lean) holds at the columns that the stages' term itself
deals (`groupsAt`, Johnson/Desc/K12/Honest/Stages.lean, at `groupTrees`,
Johnson/Desc/K12/Honest/GroupState.lean), with the keys of the place's declared openings (`keyed`,
Johnson/Desc/K12/Join.lean). It holds under the three hypotheses that are listed below. The reading
of the old rows is `Tw.L9.readOld` (Johnson/Top/H0/Tw/L9/Switch.lean): a code switch of a proximity
test reads the symbols of its old rows out of dealt columns. That reading accepts under `ReadAsks`
(`read_yes_trees`, Johnson/Desc/K12/Honest/ReadWhole.lean), and `ReadAsks` follows from two halves,
`ReadPub` and `ReadView` (`readAsks_of_halves`, ReadPub.lean). `ReadView` is the half on the sampled
positions and on the form of the dealt columns. The stages' term is `stagesAll` (Stages.lean): it
makes its groups of columns by `groupsAt`, at the first of its stages from the list of trees that it
is given. `read_first_any` (Johnson/Desc/K12/Honest/Shape/ReadFirst.lean) calls `readView_term`. One
definition and four theorems, general in every parameter. The file does not depend on the frame for
an honest side (Johnson/Desc/ProofFile/Honest/Frame.lean).

In the list: t is a natural number: in `ReadAsks`, the place of a tree in the book (`TreeBook`,
OnBytes/Iop/Ground.lean). ts is a list of such numbers. `key t`, `log t` and `c t` are used as the
key, the depth and the column function (for each position a list of words) of the tree at t.
`groupTrees ts log c` lists the pair (`log t`, `c t`) for each t in ts: a tree in the sense of
Stages.lean (`Tree`). T and `TT t` are trees in the sense of a book (`OnBytes.Tree`, Ground.lean),
with a shape and a number. poss is the list of the sampled positions. `Positions.ofDraws a poss`
(Ground.lean) is the structure `Positions` with the range a (`logN`), the sampled positions poss
(`draws`) and the listed positions `listOfT poss` (`all`; OnBytes/Chain/Draws.lean): each position
of poss once, increasing. Below, the list of t is `Fmt.listOf (poss.map (· % 2 ^ log t))`
(Fmt/Rules6.lean): the sampled positions modulo 2 ^ `log t`, each once, increasing. `groupsAt` makes
one group for each tree: the pairs (x, `c t x`) for x in the list of t (`groupAt`,
Johnson/Prover/Link/BodyAll.lean). A dealt column (`Tw.L9.Col`, Switch.lean) is a key, a position
and a list of words. p (`P12`, Johnson/Desc/K12/Frame.lean) holds the numbers of a place at which a
proximity test is; this file reads only `p.nums.firstTree`, the number that is subtracted from a
tree's number to give its key (F in `dealt_term`; subtraction of natural numbers, cut off at 0). cut
is a list of declared rounds (`Fmt.DeclaredRound`, Decl/Declared.lean). The declared openings' keys are
`o.1.tree - p.nums.firstTree` for each o in the field `opens` of each round of cut, in order.
`keyed p cut gs` zips these keys with the groups gs and puts each group's key before each of its
columns. places is an array of pairs; `treesAt places` (ReadWhole.lean) lists their first
components, each once, increasing.

  `readView_term`: under the three hypotheses below, `ReadView` holds at `p.nums.firstTree`,
    `Positions.ofDraws a poss`, places, TT, the columns `dealtOf key log c poss` and, as the list of
    all dealt columns, `keyed p cut (groupsAt (groupTrees (treesAt places) log c) poss)`. `ReadView`
    has three fields: every listed position is among the sampled ones (`listed`); `Dealt` at `TT t`
    and the columns of t, for each t in `treesAt places` (`dealt`); the list of all dealt columns is
    the columns of each t in `treesAt places`, tree after tree, and no more (`opened`)
  `dealt_term`: `Dealt F (Positions.ofDraws a poss) T (dealtOf key log c poss t)` (`Dealt`,
    Johnson/Desc/K12/Honest/ReadTrees.lean), where every sampled position is below 2 ^ a, T has the
    depth `log t` (`T.shape.logN`) and the key `key t` (`T.number - F`), and `c t x` has the width
    of T (`T.shape.mainWidth + T.shape.maskWidth` words) at every x below 2 ^ `log t`
  `keyed_groups`: where the declared openings' keys are `ts.map key`, that is the trees' keys in the
    order of ts: `keyed p cut (groupsAt (groupTrees ts log c) poss)` is
    `ts.flatMap (dealtOf key log c poss)`: the keyed columns are the trees' `dealtOf`, tree after
    tree. It is not `H2K.Sw.keyed_groups` (Johnson/Desc/K12/Law/FirstRead.lean), another theorem in
    a namespace that this file opens
  `zip_flat`: the same with `keyed` unfolded and `ts.map key` in the place of the declared openings'
    keys. No hypothesis
  `dealtOf key log c poss t`: a definition: one tree's dealt columns as the term deals them, with
    the tree's key: the column (`key t`, x, `c t x`) for each x in the list of t

By what. `zip_flat` goes by recursion on ts. `keyed_groups` unfolds `keyed`, rewrites by its
hypothesis and calls `zip_flat`. `dealt_term` first shows that the list at which T is opened under
the positions (`Blk.ownList`, Ground.lean) is the list of t: by `ownList_eq`
(OnBytes/Slice/BlkProxMany.lean) and `ownAt_ofDraws` (FirstRead.lean), which takes the bound on the
sampled positions. It then unfolds `Own.colsStand` (Johnson/Desc/Own/Shapes.lean), the test on key,
position and width in `Dealt`; that every x in the list of t is below 2 ^ `log t` follows from
`Fmt.listOf_mem` (Fmt/Rules6Laws.lean). `readView_term` has `listed` from `listOfT_eq` (Draws.lean)
and `Fmt.listOf_mem`, `dealt` from `dealt_term` and `opened` from `keyed_groups`.

Hypotheses of `readView_term`. hkeys: the declared openings' keys of cut are
`(treesAt places).map key`: as many as the trees, and in the order of `treesAt places`. hr: every
sampled position is below 2 ^ a. hT: for each t in `treesAt places`: `(TT t).shape.logN` is `log t`;
`(TT t).number - p.nums.firstTree` is `key t`; and `c t x` has
`(TT t).shape.mainWidth + (TT t).shape.maskWidth` words at every x below 2 ^ `log t`.

Limits. The clauses on keys, depths and widths are hypotheses, and so is the bound on the sampled
positions: this file proves them at no values. Only this half is treated: nothing on `ReadPub`. p,
cut, places, TT, key, log and c are free parameters. That cut is a list of rounds that the place of
p declares is stated nowhere in this file. That `TT t` is the tree at place t of a book is no
hypothesis here: it is the field `there` of `TreePub` (ReadPub.lean). Of a column `c t x` the
hypotheses fix only the number of its words. No statement of this file names `stagesAll` or
`readOld`: the theorems are on `groupsAt` at `groupTrees`. Nothing on completeness, on soundness or
on what is hidden.
-/
import Johnson.Desc.K12.Honest.ReadPub
import Johnson.Desc.K12.Honest.GroupState

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw
open Johnson.Prover.Link (groupAt)

/-- One tree's dealt columns, with the tree's key: the column (`key t`, x, `c t x`) for each x in
`Fmt.listOf (poss.map (· % 2 ^ log t))`, the sampled positions modulo 2 ^ `log t`, each once,
increasing. -/
def dealtOf (key log : ℕ → ℕ) (c : ℕ → ℕ → List UInt64) (poss : List ℕ) (t : ℕ) :
    List Tw.L9.Col :=
  (groupAt (log t) poss (c t)).map fun y => (key t, y.1, y.2)

theorem zip_flat (key log : ℕ → ℕ) (c : ℕ → ℕ → List UInt64) (poss : List ℕ) : ∀ ts : List ℕ,
    ((ts.map key).zip (groupsAt (groupTrees ts log c) poss)).flatMap
      (fun x => x.2.map fun y => (x.1, y.1, y.2)) = ts.flatMap (dealtOf key log c poss)
  | [] => rfl
  | t :: ts => by
    show (groupAt (log t) poss (c t)).map (fun y => (key t, y.1, y.2)) ++ _ = _
    rw [List.flatMap_cons]
    exact congrArg _ (zip_flat key log c poss ts)

/-- The keyed columns are the trees', tree after tree. hkeys: the declared openings' keys of cut are
the trees' keys, in the order of ts. -/
theorem keyed_groups (p : P12) (cut : List Fmt.DeclaredRound) (ts : List ℕ) (key log : ℕ → ℕ)
    (c : ℕ → ℕ → List UInt64) (poss : List ℕ)
    (hkeys : (cut.flatMap fun r => r.opens.map fun o => o.1.tree - p.nums.firstTree) = ts.map key) :
    keyed p cut (groupsAt (groupTrees ts log c) poss) = ts.flatMap (dealtOf key log c poss) := by
  unfold keyed
  rw [hkeys]
  exact zip_flat key log c poss ts

/-- `Dealt` (ReadTrees.lean) holds at `dealtOf`. hr: the sampled positions are below 2 ^ a. hl, hk,
hw: T has the depth `log t` and the key `key t`, and the columns `c t x` have the width of T. -/
theorem dealt_term (F a : ℕ) (poss : List ℕ) (hr : ∀ x ∈ poss, x < 2 ^ a) (key log : ℕ → ℕ)
    (c : ℕ → ℕ → List UInt64) (t : ℕ) (T : OnBytes.Tree) (hl : T.shape.logN = log t)
    (hk : T.number - F = key t)
    (hw : ∀ x, x < 2 ^ log t → (c t x).length = T.shape.mainWidth + T.shape.maskWidth) :
    Dealt F (Positions.ofDraws a poss) T (dealtOf key log c poss t) := by
  have hown : (Blk.ownList T (Positions.ofDraws a poss)).toList =
      Fmt.listOf (poss.map (· % 2 ^ log t)) := by
    rw [ownList_eq, hl]
    exact ownAt_ofDraws a (log t) poss hr
  refine ⟨?_, ?_⟩
  · rw [← Array.length_toList, hown]
    simp [dealtOf, groupAt]
  · rw [hown, hk]
    unfold Own.colsStand dealtOf groupAt
    refine List.all_eq_true.2 fun q hq => ?_
    rw [List.map_map] at hq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
    simp only [List.getElem_zip, List.getElem_map, Function.comp, beq_self_eq_true, Bool.true_and,
      beq_iff_eq]
    refine hw _ ?_
    have hm : (Fmt.listOf (poss.map (· % 2 ^ log t)))[i]'(by simpa using hi) ∈
        Fmt.listOf (poss.map (· % 2 ^ log t)) := List.getElem_mem _
    obtain ⟨z, -, e⟩ := List.mem_map.1 ((Fmt.listOf_mem _ _).1 hm)
    rw [← e]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-- **The view's half at the term's own dealt columns.** `ReadView` (ReadPub.lean) holds at
`dealtOf` and at the keyed groups that `groupsAt` makes of `groupTrees`. The three hypotheses are
explained in the head of this file. -/
theorem readView_term (p : P12) (cut : List Fmt.DeclaredRound) (places : Array (ℕ × ℕ)) (a : ℕ)
    (poss : List ℕ) (key log : ℕ → ℕ) (c : ℕ → ℕ → List UInt64) (TT : ℕ → OnBytes.Tree)
    (hkeys : (cut.flatMap fun r => r.opens.map fun o => o.1.tree - p.nums.firstTree) =
      (treesAt places).map key)
    (hr : ∀ x ∈ poss, x < 2 ^ a)
    (hT : ∀ t ∈ treesAt places, (TT t).shape.logN = log t ∧
      (TT t).number - p.nums.firstTree = key t ∧
      ∀ x, x < 2 ^ log t → (c t x).length = (TT t).shape.mainWidth + (TT t).shape.maskWidth) :
    ReadView p.nums.firstTree (Positions.ofDraws a poss) places TT (dealtOf key log c poss)
      (keyed p cut (groupsAt (groupTrees (treesAt places) log c) poss)) :=
  ⟨fun x hx => by
      have k : x ∈ listOfT poss := by simpa [Positions.ofDraws] using hx
      rw [listOfT_eq, Fmt.listOf_mem] at k
      simpa [Positions.ofDraws] using k,
    fun t ht => dealt_term _ a poss hr key log c t (TT t) (hT t ht).1 (hT t ht).2.1 (hT t ht).2.2,
    keyed_groups p cut _ key log c poss hkeys⟩

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.zip_flat
#print axioms ProofFile.Honest.K12.keyed_groups
#print axioms ProofFile.Honest.K12.dealt_term
#print axioms ProofFile.Honest.K12.readView_term
#print axioms ProofFile.Honest.K12.dealtOf
