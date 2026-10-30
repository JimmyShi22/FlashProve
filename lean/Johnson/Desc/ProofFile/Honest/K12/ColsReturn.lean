-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/ColsReturn.lean: the columns that a proximity test's declared
rounds read are filled: `fillCols` (the frame, Johnson/Desc/ProofFile/Honest/Frame.lean) returns a
list of columns, with no stored run to fall back on, at the tables that are available after the
test's rounds were played. This is `cols_return`. For the trees that the test's own rounds send, the
proof shows that a table is available, with the width that FitsAll.lean in this folder computes; for
the trees from before the test that is a hypothesis. General: at every job, input, front, family of
coins, list of challenges, list of declared rounds and structure of available tables, under the four
hypotheses below. `playsOn_k12` (PlaysK12.lean in this folder) calls it. Two definitions, each a
test that returns a Bool, and one theorem.

In the list: a job J (`TestJob`, Test.lean in this folder) is what a caller supplies for its test.
Its plan, also called its place, is `J.p` (`P12`, Johnson/Desc/K12/Frame.lean: the test's
parameters). The term is `testAll J w fr C D` (Test.lean), a function of the job, the prover's input
w, the front fr (`Front`, Johnson/Desc/ProofFile/Honest/Sum.lean: what precedes the test), the coins
C (`TestCoins`) and the challenges D by the round's number. `msgAt J w fr C D i` (Parts.lean in this
folder) is the message (`Sending`, the frame) of round number i, taken from the term. It has one
table where `depthAt J i` (Test.lean) gives a depth: such a round is said to send a tree, and is
called a sending round. `sentBefore J r` (SentTables.lean in this folder) counts the sending rounds
below r. `widthsOf J.fresh.isNone J.p.nums.stages` (FitsAll.lean) lists a width for each round of
the test. `byNo ds` (PlayedTerm.lean in this folder) is the list ds as a function of the round's
number. A declared round (`Fmt.DeclaredRound`, Decl/Declared.lean) lists its stored parts (`stored`) and
its openings (`opens`). An opening o is a tree's shape `o.1` (`Fmt.Shape`, Fmt/Plan.lean), whose
field `W` is the declared width, and a source `o.2` (`Fmt.TreeSource`, Decl/Declared.lean): `own n`,
tree number n of those that this chain sends, or `taken c q`, a tree that the chain has taken over:
number q of those that chain number c sends. The available tables are a structure E (`Env`,
Johnson/Desc/ProofFile/Honest/Side.lean): the stored tables' columns (`stored`), the table for a
source, with its sender's place (`tree`), and how many trees the chain has sent so far (`sent`).
`E.add l` is the same after the played rounds l (`Played`, the frame): their tables are the chain's
next own trees. A table (`Table`, the frame) has its width in the field `words`. `readsOf` (the
frame) lists what declared rounds read at given challenges. `fillCols` at such a list and the empty
list `[]` returns, for each read, its key, its position and its own words; it returns an error where
a read's table is not available, or where a column has another number of words than the round
declares.

  `cols_return`: under the four hypotheses below there is a list cols such that `fillCols` at
    `readsOf chain ft (E.add l).stored (E.add l).tree decls ds` and `[]` returns cols. The numbers
    chain and ft are free parameters
  `oldSrc sent`: a definition: a test on a source: whether it is from before the test; such a source
    is called old. It is true at every `taken c q`, and at `own n` just where n < sent. The number
    sent is a free parameter; `cols_return` takes `E.sent`
  `newWideB J decls sent`: a definition. On the plan: every declared opening whose source is not old
    opens the tree of a sending round of the test, by the count of sending rounds in front of it, at
    that tree's width. As Lean has it: for every opening o of every round of decls,
    `oldSrc sent o.2` is true, or `o.2` is `own n` and there is a number r below the length of decls
    at which `depthAt J r` gives a depth, sent + `sentBefore J r` is n, and the width that
    `widthsOf` lists at r (0 beyond the list's end) is `o.1.W`. Of the job it reads only `J.p` and
    whether `J.fresh` is `none`; decls and sent are free parameters

By what. `cols_return` is `filled` (Johnson/Desc/ProofFile/Honest/Law/Fill.lean): the columns are
filled if each stored table that the rounds declare, at every position in range, and each tree that
they open is available with the declared width. The condition on stored tables is vacuous by hst. At
an old source the table is the one of hold, since `E.add l` leaves the chain's earlier trees and the
trees taken over as they were (`add_old`, `add_taken`,
Johnson/Desc/ProofFile/Honest/Small/ColGroups.lean). At any other source hnew gives a sending round
r. The tables of the chain's next trees are the played rounds' tables in the order of sending
(`add_new`, same file), which by hT are the messages' tables; among these the table of round r has
the index `sentBefore J r` (`sent_table`, SentTables.lean). Its field `words` is the length, at
position 0, of the column that the term lists at round r (`tableOf`, TableCol.lean in this folder;
`treeAt`, SentTables.lean), and that is the width that `widthsOf` lists at r (`width_treeAt`,
FitsAll.lean).

Hypotheses of `cols_return`. hT: the tables of the rounds in l are, round by round, those of
`msgAt J w fr C (byNo ds) i` for i below the number of declared rounds, each under `some`. hst: no
declared round has a stored part. hold: for every declared opening whose source is old at `E.sent`,
`E.tree` has a table for that source whose `words` is the declared width. hnew:
`newWideB J decls E.sent` is true.

Limits.
- hT, hst, hold and hnew are hypotheses: none of them is proved here.
- No play is called here: l is a free parameter. hT has the form of the second conclusion of
  `played_term` (PlayedTerm.lean), which has hypotheses of its own.
- decls is a free parameter: nothing here ties it to the rounds that the place declares.
- There is no hypothesis on the length of ds: `readsOf` reads only as many rounds as ds has
  challenges, and none at the empty list.
- Only widths are compared. An opening's depth and its tree's number (the fields `a` and `tree` of
  its shape) and a table's `logLength` are compared with nothing here.
- Where every opened source is old at sent, `newWideB` is true and compares nothing: every opened
  tree is then left to hold.
- Nothing on what the columns hold (see ColsTerm.lean), on a decision, on completeness, on soundness
  or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.FitsAll
import Johnson.Desc.ProofFile.Honest.Small.ColGroups
import Johnson.Desc.ProofFile.Honest.Law.Fill

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open VerifiableInference.Desc VerifiableInference.Desc.K12
open ProofFile.Honest.Small (add_new add_old add_taken add_stored)

variable {W X : Type}

/-- A source is from before the test: a tree that the chain has taken over, or the chain's own tree
of a number below `sent`. -/
def oldSrc (sent : ℕ) : Fmt.TreeSource → Bool
  | .own n => decide (n < sent)
  | .taken _ _ => true

/-- Every declared opening whose source is not old (`oldSrc`) has the source `own n`, where n is
`sent` plus the number of sending rounds below some sending round r, and declares the width that
`widthsOf` lists at r. The number r is below the number of declared rounds. -/
def newWideB (J : TestJob W X) (decls : List Fmt.DeclaredRound) (sent : ℕ) : Bool :=
  decls.all fun d => d.opens.all fun o => oldSrc sent o.2 ||
    match o.2 with
    | .own n => (List.range decls.length).any fun r => (depthAt J r).isSome &&
        (sent + sentBefore J r == n) &&
        ((widthsOf J.fresh.isNone J.p.nums.stages).getD r 0 == o.1.W)
    | .taken _ _ => false

/-- **The columns are filled**: at the tables that are available after the played rounds l,
`fillCols` returns with nothing to fall back on. hT: the tables of l are those of the term's
messages. hst: no declared round has a stored part. hold: for each old source that is opened a table
is available with the declared width. hnew: `newWideB` is true. -/
theorem cols_return (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (ds : List Fmt.Drawn)
    (decls : List Fmt.DeclaredRound) (E : Env) (l : List Played) (chain ft : ℕ)
    (hT : l.map (·.tables) = (List.range decls.length).map fun i =>
      (msgAt J w fr C (byNo ds) i).tables.map some)
    (hst : ∀ d ∈ decls, d.stored = [])
    (hold : ∀ d ∈ decls, ∀ o ∈ d.opens, oldSrc E.sent o.2 = true →
      ∃ pt, E.tree o.2 = some pt ∧ pt.2.words = o.1.W)
    (hnew : newWideB J decls E.sent = true) :
    ∃ cols, fillCols (readsOf chain ft (E.add l).stored (E.add l).tree decls ds) [] =
      .ok cols := by
  refine filled chain ft _ _ decls ds fun d hd => ⟨fun s hs => ?_, fun o ho => ?_⟩
  · rw [hst d hd] at hs
    cases hs
  · by_cases hO : oldSrc E.sent o.2 = true
    · obtain ⟨pt, h1, h2⟩ := hold d hd o ho hO
      refine ⟨pt, ?_, h2⟩
      cases hσ : o.2 with
      | own n =>
        rw [hσ] at hO h1
        rw [add_old E l (of_decide_eq_true hO)]
        exact h1
      | taken c q =>
        rw [hσ] at h1
        rw [add_taken]
        exact h1
    · unfold newWideB at hnew
      have k := List.all_eq_true.1 (List.all_eq_true.1 hnew d hd) o ho
      rw [Bool.or_eq_true] at k
      rcases k with k | k
      · exact absurd k hO
      · cases hσ : o.2 with
        | taken c q =>
          rw [hσ] at k
          cases k
        | own n =>
          rw [hσ] at k
          obtain ⟨r, hr, k⟩ := List.any_eq_true.1 k
          simp only [Bool.and_eq_true, beq_iff_eq] at k
          obtain ⟨⟨k1, k2⟩, k3⟩ := k
          obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 k1
          have e1 : l.flatMap (·.tables) = (List.range decls.length).flatMap fun i =>
              (msgAt J w fr C (byNo ds) i).tables.map some := by
            rw [List.flatMap_def, hT, ← List.flatMap_def]
          have e2 := add_new E l (sentBefore J r)
          rw [e1, sent_table J w fr C (byNo ds) decls.length r a (List.mem_range.1 hr) ha,
            k2] at e2
          cases ht : (E.add l).tree (.own n) with
          | none =>
            rw [ht] at e2
            cases e2
          | some u =>
            rw [ht] at e2
            have e3 : u.2 = tableOf a (treeAt J w fr C (byNo ds) r) := Option.some.inj e2
            refine ⟨u, rfl, ?_⟩
            rw [e3, ← k3, ← width_treeAt J w fr C (byNo ds) r]
            rfl

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.cols_return
#print axioms ProofFile.Honest.K12.oldSrc
#print axioms ProofFile.Honest.K12.newWideB
