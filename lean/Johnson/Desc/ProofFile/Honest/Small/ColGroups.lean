-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Small/ColGroups.lean: the groups of columns that a sub-protocol's
`decide` is given, written out as the tables' own columns at the listed positions. The frame puts
the columns that declared rounds read into one list (`readsOf`, `fillCols`, Honest/Frame.lean);
`Block.step` cuts the columns that it takes off that list into groups (`regroup`, at the lengths of
the groups of `groupsOf`, Johnson/Desc/Block.lean). `colGroups` defines the groups from the tables,
and `regroup_cols` shows that the cut list is `colGroups` wherever `fillCols` returns with the empty
list as its second argument, that is, with no fallback column to use where a read has no words. The
last section says which tables `Env.add` (Honest/Side.lean) holds after rounds were played. General
in the rounds, the challenges and the tables: no kind of sub-protocol, no part of the prover's
(`Placed`) and no prover is named.

  `regroup_cols`: where `fillCols (readsOf chain ft stored tree rs ds) [] = .ok cols`, the list
    cols, cut by the lengths of the groups of `groupsOf ft rs ds`, is `colGroups stored tree rs ds`
  `add_new`: in `E.add l`, the table of the chain's own tree number `E.sent + n` is entry n of the
    played rounds' tables (`l.flatMap (·.tables)`), in the order of sending; it is `none` where the
    list has no entry n or that entry is `none`. Stated without the sender's place, which
    `colGroups` does not read
  `colGroups stored tree rs ds`: a definition with code: round by round, one group for each stored
    tree that the round opens (its field `stored`), then one for each other tree (its field
    `opens`). A group lists (position, column) over the positions that `groupsOf` lists: it is the
    recursion of `groupsOf` with (position, column) where that has (key, position, width). The
    column is the empty list where the parameter `stored` or `tree` returns `none`
  `words_at_hand`: under the hypothesis of `regroup_cols`, every read that `readsOf` lists has its
    `words`. So there no column of `colGroups` is empty because a table is missing; that consequence
    is not stated as a theorem. The other direction, from tables that are there with the stated
    widths to reads whose words have the stated width: `reads_at_hand` (Honest/Law/Fill.lean)
  `regroup_groups`: on lists: a list of groups, flattened, mapped to columns by f and cut again by
    the groups' lengths, is the same groups, each entry as the position and words of its column
  `readGroups`: a definition with code: the reads of `readsOf`, kept in groups
  `reads_flat`: `readsOf` is `readGroups`, flattened
  `groups_lengths`: the groups of `groupsOf` and of `readGroups` have the same lengths, one by one
  `groups_cols`: `readGroups`, with `(r.pos, r.words.getD [])` for each read r, is `colGroups`
  `add_stored`, `add_taken`, `add_old`: `E.add l` has the stored columns of E, its trees that are
    taken over from another chain, and its own trees of a number below `E.sent`, unchanged
  `tables_only`: `tablesOf l` (Honest/Frame.lean) without the senders' places is
    `l.flatMap (·.tables)`

By what. `fillCols_nil_ok` (Honest/Law/StratCols.lean): where `fillCols q []` returns, the columns
are `(r.key, r.pos, r.words.getD [])` over the reads r of q, and every read has its `words`.
`regroup_cols` rewrites by its first conjunct, then by `reads_flat`, `groups_lengths`,
`regroup_groups` and `groups_cols`; `words_at_hand` is its second conjunct. The statements on
`Env.add` unfold its definition, `add_new` with `tables_only`.

Limits. Statements on lists only. Whether `fillCols` returns is not treated here (`filled`,
Honest/Law/Fill.lean); where it does not, `regroup_cols` and `words_at_hand` hold vacuously, and
`colGroups` still has a value. No statement here names `Block.step` or `decide`: that `Block.step`
returns just where `decide` returns at the list cut in this way is `step_iff_decide`
(Honest/Law/Cut.lean), under hypotheses of its own. Nothing on the field `sent` of `E.add l`.
Nothing on the values that a column holds or on what they mean. No property of a protocol is stated:
nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Law.StratCols
import Johnson.Desc.ProofFile.Honest.Side

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Small
open VerifiableInference.Desc (OpenedColumn Place regroup groupsOf)

/-- The columns that declared rounds read, in groups: one group for each stored tree that a round
opens, then one for each other tree; each entry is (position, column). The column is `[]` where
`stored` or `tree` returns `none`. -/
def colGroups (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) :
    List Fmt.DeclaredRound → List Fmt.Drawn → List (List (Nat × List UInt64))
  | d :: ds, R :: Rs =>
    (d.stored.map fun s =>
      (Fmt.listOf ((Fmt.partOf s R.poss).map (· % 2 ^ s.sh.a))).map fun x =>
        (x, (stored s.item x).getD [])) ++
    (d.opens.map fun o =>
      (Fmt.listOf (R.poss.map (· % 2 ^ o.1.a))).map fun x =>
        (x, ((tree o.2).map (·.2.col x)).getD [])) ++
    colGroups stored tree ds Rs
  | _, _ => []

/-- A list of groups, flattened, mapped to columns by f and cut again by the groups' lengths, is the
same groups, each entry as the position and words of its column. -/
theorem regroup_groups {α : Type} (f : α → OpenedColumn) : ∀ G : List (List α),
    regroup (G.map (·.length)) ((G.flatMap id).map f) =
      G.map fun g => g.map fun r => ((f r).2.1, (f r).2.2)
  | [] => rfl
  | g :: G => by
    rw [List.map_cons, List.flatMap_cons, List.map_append, List.map_cons]
    show (((id g).map f ++ (G.flatMap id).map f).take g.length).map (fun c => (c.2.1, c.2.2)) ::
      regroup (G.map (·.length)) (((id g).map f ++ (G.flatMap id).map f).drop g.length) = _
    have hl : ((id g).map f).length = g.length := by rw [List.length_map]; rfl
    rw [List.take_left' hl, List.drop_left' hl, regroup_groups f G, List.map_map]
    rfl

/-- The reads of `readsOf` (Honest/Frame.lean), kept in groups: `map` over a round's stored trees
and openings where `readsOf` has `flatMap`. -/
def readGroups (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) :
    List Fmt.DeclaredRound → List Fmt.Drawn → List (List Read)
  | d :: ds, R :: Rs =>
    (d.stored.map fun s =>
      (Fmt.listOf ((Fmt.partOf s R.poss).map (· % 2 ^ s.sh.a))).map fun x =>
        (⟨Fmt.storedKey s.item, x, some s.item, none, none, stored s.item x, s.sh.W⟩ : Read)) ++
    (d.opens.map fun o =>
      (Fmt.listOf (R.poss.map (· % 2 ^ o.1.a))).map fun x =>
        (⟨o.1.tree - ft, x, none, some (srcOf chain o.2), (tree o.2).map (·.1),
          (tree o.2).map (·.2.col x), o.1.W⟩ : Read)) ++
    readGroups chain ft stored tree ds Rs
  | _, _ => []

section
variable (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
  (tree : Fmt.TreeSource → Option (Place × Table))

theorem reads_flat : ∀ (rs : List Fmt.DeclaredRound) (ds : List Fmt.Drawn),
    readsOf chain ft stored tree rs ds = (readGroups chain ft stored tree rs ds).flatMap id
  | [], _ => by simp [readsOf, readGroups]
  | _ :: _, [] => by simp [readsOf, readGroups]
  | d :: rs, R :: ds => by
    simp only [readsOf, readGroups, List.flatMap_append, reads_flat rs ds, List.flatMap_map, id]

theorem groups_lengths : ∀ (rs : List Fmt.DeclaredRound) (ds : List Fmt.Drawn),
    (groupsOf ft rs ds).map (·.length) = (readGroups chain ft stored tree rs ds).map (·.length)
  | [], _ => by simp [groupsOf, readGroups]
  | _ :: _, [] => by simp [groupsOf, readGroups]
  | d :: rs, R :: ds => by
    simp only [groupsOf, readGroups, List.map_append, groups_lengths rs ds, List.map_map,
      Function.comp_def, List.length_map]

theorem groups_cols : ∀ (rs : List Fmt.DeclaredRound) (ds : List Fmt.Drawn),
    ((readGroups chain ft stored tree rs ds).map fun g => g.map fun r => (r.pos, r.words.getD [])) =
      colGroups stored tree rs ds
  | [], _ => by simp [colGroups, readGroups]
  | _ :: _, [] => by simp [colGroups, readGroups]
  | d :: rs, R :: ds => by
    simp only [colGroups, readGroups, List.map_append, groups_cols rs ds, List.map_map,
      Function.comp_def]

/-- **The columns that `fillCols` returns, cut by the lengths of the groups of `groupsOf`, are the
tables' own columns at the listed positions.** hc: `fillCols` returns with the empty list as its
second argument. The parameters are those of `readsOf` (Honest/Frame.lean). -/
theorem regroup_cols {rs : List Fmt.DeclaredRound} {ds : List Fmt.Drawn} {cols : List OpenedColumn}
    (hc : fillCols (readsOf chain ft stored tree rs ds) [] = .ok cols) :
    regroup ((groupsOf ft rs ds).map (·.length)) cols = colGroups stored tree rs ds := by
  rw [(fillCols_nil_ok _ _ hc).1, reads_flat, groups_lengths chain ft stored tree, regroup_groups,
    groups_cols]

/-- Where `fillCols` returns with the empty list as its second argument, every read has its `words`.
-/
theorem words_at_hand {rs : List Fmt.DeclaredRound} {ds : List Fmt.Drawn} {cols : List OpenedColumn}
    (hc : fillCols (readsOf chain ft stored tree rs ds) [] = .ok cols) :
    ∀ r ∈ readsOf chain ft stored tree rs ds, r.words.isSome = true :=
  (fillCols_nil_ok _ _ hc).2

end

/-! ## After rounds that were played (`Env.add`) -/

theorem add_stored (E : Env) (l : List Played) : (E.add l).stored = E.stored := rfl

theorem add_taken (E : Env) (l : List Played) (c k : Nat) :
    (E.add l).tree (.taken c k) = E.tree (.taken c k) := rfl

theorem add_old (E : Env) (l : List Played) {n : Nat} (h : n < E.sent) :
    (E.add l).tree (.own n) = E.tree (.own n) :=
  if_pos h

theorem tables_only : ∀ l : List Played,
    (tablesOf l).map (Option.map (·.2)) = l.flatMap (·.tables)
  | [] => rfl
  | p :: l => by
    have ih := tables_only l
    unfold tablesOf at ih ⊢
    rw [List.flatMap_cons, List.flatMap_cons, List.map_append, ih, List.map_map]
    congr 1
    refine (List.map_congr_left fun t _ => ?_).trans (List.map_id _)
    cases t <;> rfl

/-- **In `E.add l` the tables of the chain's next own trees are the played rounds' tables, in the
order of sending.** -/
theorem add_new (E : Env) (l : List Played) (n : Nat) :
    ((E.add l).tree (.own (E.sent + n))).map (·.2) = ((l.flatMap (·.tables))[n]?).bind id := by
  show (if E.sent + n < E.sent then E.tree (.own (E.sent + n))
    else ((tablesOf l)[E.sent + n - E.sent]?).bind id).map (·.2) = _
  rw [if_neg (by omega), Nat.add_sub_cancel_left, ← tables_only, List.getElem?_map]
  cases (tablesOf l)[n]? with
  | none => rfl
  | some t => rfl

end ProofFile.Honest.Small

#print axioms ProofFile.Honest.Small.regroup_groups
#print axioms ProofFile.Honest.Small.regroup_cols
#print axioms ProofFile.Honest.Small.words_at_hand
#print axioms ProofFile.Honest.Small.add_new
#print axioms ProofFile.Honest.Small.colGroups
#print axioms ProofFile.Honest.Small.readGroups
#print axioms ProofFile.Honest.Small.reads_flat
#print axioms ProofFile.Honest.Small.groups_lengths
#print axioms ProofFile.Honest.Small.groups_cols
#print axioms ProofFile.Honest.Small.add_stored
#print axioms ProofFile.Honest.Small.add_taken
#print axioms ProofFile.Honest.Small.add_old
#print axioms ProofFile.Honest.Small.tables_only
