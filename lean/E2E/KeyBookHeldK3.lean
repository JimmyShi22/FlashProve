-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyBookHeldK3.lean: two separate definitions that list the parts of a lookup's honest prover are
shown equal, item by item. `spansOf f` (E2E/KeyBookFace.lean) lists the lookup's spans. A span
(`Span`) is a range of the lookup's rounds that is one part: one round in which nothing is sent and
challenges are sampled (`draw`), or one masked sumcheck (`sum`). From this list the entries of the
book for a lookup are computed (`bookEntries`), and the cut at a lookup's place in the key file's
book (`KeyPub.cuts`, E2E/KeyBook.lean). `stages f` (Johnson/Desc/ProofFile/Honest/K3/Stages.lean)
lists the stages (`Stage`: a part of the lookup, by name). From that list the lookup's list of
honest parts is built (`lookRow`, Johnson/Desc/ProofFile/Honest/K3/Row.lean). f is a face
(`K3.Face`, Johnson/Desc/First/Look/K3LookupGeneral.lean): a lookup's public numbers. The book (`ProverCoinCounts`, in
the frame, Johnson/Desc/ProofFile/Honest/Frame.lean) is the public table of how many coins each part
(`Part`) of an honest prover has, and of how the rounds at each place are cut into parts. A place
(`Place`) says where in a protocol description a sub-protocol is. An entry of the book (`Ahead`)
names a range of the coins of one part, the owner (`Ahead.owner`), that one other part, the spender
(`Ahead.spender`), is given too. All statements are general in the face; the two main theorems hold
at every face with at least two planes. The file has two definitions, theorems, and two tests at a
small example face (the lines that begin with `#guard`: Lean's evaluator runs them when the file is
compiled, the kernel does not check them, and they prove nothing).

Why. The frame rejects a list of parts at a place unless the parts' numbers of moves, one move for
each round, are the book's cut for that place (`chainSteps`). It gives a part a range of another
part's coins only if the part states the name and the count of the book's entry (`lend`). A book is
a check only if it is computed separately from the definitions of the prover's parts, so `spansOf`
does not call `stages`. This file shows that the two lists agree, stage by stage.

  `spans_of_stages`: at every face f with at least two planes, `(stages f).map (spanOf f)` is
    `spansOf f`: the stages, each written as a span, are the spans of the book's list, in the same
    order: the same calls, the same names and numbers of sampled elements, the same flags
  `cut_spans`: at every face f with at least two planes, the cut of the lookup's rounds by their
    names (`cutOfNames`, Johnson/Desc/ProofFile/Honest/BookOf.lean, at the kind K3 and the names of
    `entriesV f`, Johnson/Desc/First/Look/Via/Rounds.lean) is `(spansOf f).map Span.rounds`: the
    spans' numbers of rounds
  `entries_held`, `rounds_held`, `counts_held`: at every face and every stage, the stage written as
    a span has the stage's rounds as entries of the plan (`Stage.entries`), its number of rounds
    (`Stage.rounds`) and its two counts of hidden values, that is, of scalars that are sent under a
    mask entry: those before the end values (`Span.run` is `Stage.own`) and the end values
    (`Span.ends` is `Stage.tail`)
  `stated_counts`: the counts that the part of a stage (`partOf`, Row.lean in the folder of
    Stages.lean) states in its field `spends` are, in order, the counts of `Span.spends`
    (E2E/KeyBookRow.lean) at the stage written as a span. It holds at all parameters R, J and a of
    `partOf`, every `Seat` S (the lookup's place and the two owners, each with its name), every
    stage and every part number i. The counts only: see the first limit
  `spanOf f s`: a definition: the stage s written as a span. A stage that has a call (`Stage.call`)
    is a masked sumcheck at that call, with the flag `lastKey f s`. The flag says that the mask
    entries of the sumcheck's end values are coins of the second owner (`Seat.key`). Every other
    stage is one round, with the stage's name and its number of sampled elements
  `lastKey f s`: a definition: the stage is the masked sumcheck of the last level of the key tree of
    a part of the keys (an element of `Face.parts`)
  `levelCall_held`: the call of a product tree's level with m variables is the same in both files
    (`ProofFile.Honest.K3.levelCall`, Stages.lean; `levelCall`, E2E/KeyBookFace.lean)
  `map_ties`, `map_splits`, `map_tabs`, `map_keys`: lemmas for `spans_of_stages`: the stages `tie`;
    the stages `split`; `tab` with `tabLine`; `key` with `keyLine`: each of these four lists,
    written as spans, is the matching piece of `spansOf f`

By what. `spans_of_stages` unfolds both lists and rewrites by the four lemmas; these use
`levelCall_eq`, `map_range_const` and `flatMap_zipIdx_fst`
(Johnson/Desc/ProofFile/Honest/K3/RowLaw.lean). `rounds_held` uses `entries_length` (same file).
`cut_spans` is `cut_stages` (Johnson/Desc/ProofFile/Honest/K3/RowCut.lean), which has the same cut
as the stages' numbers of rounds, with `spans_of_stages` and `rounds_held`. The other proofs unfold
definitions: `Stage.call`, `Stage.draws`, `Stage.rounds` (Stages.lean); `Stage.name`,
`Stage.entries`, `Stage.own`, `Stage.tail`, `partOf` (Row.lean); `sumPart`, `ownRun`, `endRuns`
(Johnson/Desc/ProofFile/Honest/Sum.lean); `frontOf`, `keysOf`, `backOf`, `levels`
(E2E/KeyBookFace.lean).

Limits.
- The names are not compared. `partOf` names both ranges of coins that a masked sumcheck's part
  spends after the segment's mask row (`sumName`, `endName`, Row.lean; `maskRowRun`,
  Johnson/Desc/ProofFile/Honest/ForKinds.lean). The key file's book names them after the
  multiplicities' mask rows (`countsMaskRun`) and, for the end values of the last level of each key
  tree, after the index-mask message (`indexMaskRun`): see `seatOfLookup`, E2E/KeyBook.lean. `lend`
  returns an error where the name that a part states is not the entry's. So the frame rejects
  `lookRow` at that book. This is read off the definitions: it is not stated in Lean. A part that
  takes the owners' names as a parameter is defined in
  Johnson/Desc/ProofFile/Honest/K3/RowOwned.lean (`partOfOwned`, `lookRowOwned`, `keyOwners`). This
  file does not import it, and nothing here compares its names with the book's.
- `stated_counts` compares with `Span.spends`, not with the book's entries. That the entries which
  name a part as their spender have the names and counts of `Span.spends` is `named_lay`
  (E2E/KeyBookRow.lean), which is not called here. Nor does `stated_counts` say that i is the
  stage's number in `stages`.
- At a face with fewer than two planes the two lists differ: `stages f` has no stage `tie`, and
  `spansOf f`, like the library's `entriesV f`, has one masked sumcheck in that position. The two
  main theorems say nothing of such a face. A face that passes `Face.ok` has at least two planes
  (`two_le_planes_of_ok`, RowLaw.lean).
- Apart from a level's call, both lists take their calls from the same definitions (`noVar`,
  `leafVars`, `bitsCall`, Via/Rounds.lean), and both sides count by the same `ownRun` and `endRuns`.
  So nothing here is a check of these.
- `cut_spans` cuts the names of `entriesV f`. How that list relates to the rounds of the key file's
  link is in the limits of E2E/KeyBookFace.lean.
- This file imports RowCut.lean and, through it, RowLaw.lean, Row.lean and Stages.lean of the folder
  Johnson/Desc/ProofFile/Honest/K3/, and does not compile without these four. If `stages`, one of
  the functions on `Stage` or `partOf` changes there, the proofs here, which unfold them, can fail.
- No property of a protocol is stated: nothing on completeness, soundness or hiding.
-/
import E2E.KeyBookRow
import Johnson.Desc.ProofFile.Honest.K3.RowCut

set_option autoImplicit false

namespace AtPublicFiles.KeyBook
open OnBytes (zeroE)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.K3 (Face entriesV noVar)
open ProofFile.Honest (Due ownRun endRuns cutOfNames)
open ProofFile.Honest.K3 (Stage stages)

/-- The stage is the masked sumcheck of the last level of a key tree: `key i m` with m + 1 equal to
element number i of `f.parts`, the number of levels of that tree. -/
def lastKey (f : Face) : Stage → Bool
  | .key i m => m + 1 == f.parts.getD i 0
  | _ => false

/-- A stage written as a span: a masked sumcheck at the stage's call, with the flag `lastKey f s`;
or, if the stage has no call, one round with the stage's name and number of sampled elements. -/
def spanOf (f : Face) (s : Stage) : Span :=
  match s.call f with
  | some k => .sum k (lastKey f s)
  | none => .draw s.name (s.draws f)

/-! ## The two lists are equal -/

theorem levelCall_held (m : Nat) : ProofFile.Honest.K3.levelCall m = levelCall m :=
  ProofFile.Honest.K3.levelCall_eq m

theorem map_ties (f : Face) (n : Nat) :
    ((List.range (n + 1)).map Stage.tie).map (spanOf f) =
      [.sum (noVar 3 3) false] ++ List.replicate n (.sum (noVar 3 2) false) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_cons, List.map_map, List.map_map]
  have : ((spanOf f ∘ Stage.tie) ∘ Nat.succ) = fun _ => Span.sum (noVar 3 2) false := by
    funext i; rfl
  rw [this, ProofFile.Honest.K3.map_range_const]
  rfl

theorem map_splits (f : Face) (n : Nat) :
    ((List.range n).map Stage.split).map (spanOf f) =
      List.replicate n (.sum (noVar 2 2) false) := by
  rw [List.map_map]
  have : (spanOf f ∘ Stage.split) = fun _ => Span.sum (noVar 2 2) false := by
    funext i; rfl
  rw [this, ProofFile.Honest.K3.map_range_const]

theorem map_tabs (f : Face) :
    ((List.range f.d).flatMap fun l => [Stage.tab l, Stage.tabLine l]).map (spanOf f) =
      levels f.mu f.d false := by
  rw [List.map_flatMap]
  unfold levels
  congr 1
  funext l
  show [Span.sum (ProofFile.Honest.K3.levelCall (f.mu + l)) false, Span.draw "LINE" 1] = _
  rw [levelCall_held]
  rfl

theorem map_keys (f : Face) :
    (f.parts.zipIdx.flatMap fun x =>
      (List.range x.1).flatMap fun m => [Stage.key x.2 m, Stage.keyLine x.2 m]).map (spanOf f) =
      keysOf f := by
  rw [List.map_flatMap]
  unfold keysOf
  rw [← ProofFile.Honest.K3.flatMap_zipIdx_fst (fun v => levels 0 v true) f.parts 0]
  rw [List.flatMap_def, List.flatMap_def]
  congr 1
  apply List.map_congr_left
  intro x hx
  have hx' : f.parts.getD x.2 0 = x.1 := by
    have := List.mem_zipIdx_iff_getElem?.1 (show (x.1, x.2) ∈ f.parts.zipIdx from hx)
    simp [List.getD_eq_getElem?_getD, this]
  rw [List.map_flatMap]
  unfold levels
  congr 1
  funext m
  show [Span.sum (ProofFile.Honest.K3.levelCall m) (m + 1 == f.parts.getD x.2 0), Span.draw "LINE" 1] = _
  rw [levelCall_held, hx', Nat.zero_add, Bool.true_and]

/-- **The stages, each written as a span, are the spans of the book's list, in the same order.**
Hypothesis: the face has at least two planes. -/
theorem spans_of_stages (f : Face) (h : 2 ≤ f.planes) : (stages f).map (spanOf f) = spansOf f := by
  have hp : f.planes - 1 = (f.planes - 2) + 1 := by omega
  have hs : (if f.shifted then [Stage.shift] else []).map (spanOf f) =
      if f.shifted then [Span.draw "LKP shift" 1] else [] := by
    cases f.shifted <;> rfl
  unfold stages spansOf frontOf backOf
  simp only [List.map_append, hs, hp, map_ties, map_splits, map_tabs, map_keys, List.append_assoc]
  rfl

/-! ## Consequences -/

theorem entries_held (f : Face) (s : Stage) : (spanOf f s).entries = Stage.entries f s := by
  unfold spanOf Stage.entries
  cases s.call f <;> rfl

/-- A stage written as a span has the stage's number of rounds. -/
theorem rounds_held (f : Face) (s : Stage) : (spanOf f s).rounds = s.rounds f := by
  unfold Span.rounds
  rw [entries_held, ProofFile.Honest.K3.entries_length]

/-- A stage written as a span has the stage's two counts of hidden values: those before the end
values, and the end values. -/
theorem counts_held (f : Face) (s : Stage) :
    (spanOf f s).run = s.own f ∧ (spanOf f s).ends = s.tail f := by
  unfold spanOf Stage.own Stage.tail
  cases s.call f <;> exact ⟨rfl, rfl⟩

/-- **The cut of the lookup's rounds by their names is the list of the spans' numbers of rounds.**
Hypothesis: the face has at least two planes. -/
theorem cut_spans (f : Face) (h : 2 ≤ f.planes) :
    cutOfNames .K3 ((entriesV f).map (·.name)) = (spansOf f).map Span.rounds := by
  rw [ProofFile.Honest.K3.cut_stages f h, ← spans_of_stages f h, List.map_map]
  apply List.map_congr_left
  intro s _
  exact (rounds_held f s).symm

/-- The counts that the part of a stage states in `spends` are the counts of `Span.spends` at the
stage written as a span. The names are not compared. -/
theorem stated_counts {V W : Type} (R : ProofFile.Honest.K3.Reads) (J : ProofFile.Honest.K3.LookJobs W)
    (a : ProofFile.Honest.K3.At) (S : Seat) (s : Stage) (i : Nat) :
    (ProofFile.Honest.K3.partOf (V := V) R J a s i).spends.map (·.2) =
      ((spanOf a.face s).spends S i).map (·.2) := by
  unfold ProofFile.Honest.K3.partOf spanOf
  cases hk : s.call a.face with
  | none => rfl
  | some k =>
    show ((_, (⟨0, ownRun k⟩ : Due)) :: endRuns _ k.ends).map (·.2) =
      ((_, (⟨0, ownRun k⟩ : Due)) :: endRuns _ k.ends).map (·.2)
    cases k.ends <;> rfl

-- Tests at the small example face `toyFace` (E2E/KeyBookFace.lean): it has 16 stages, and `lastKey`
-- is true at the stages number 5 and 9, from 0. A test in that file finds the same two numbers as
-- the parts that spend the second owner's coins.
#guard (stages toyFace).length == 16
#guard ((stages toyFace).zipIdx.filter fun x => lastKey toyFace x.1).map (·.2) == [5, 9]

end AtPublicFiles.KeyBook

#print axioms AtPublicFiles.KeyBook.spans_of_stages
#print axioms AtPublicFiles.KeyBook.rounds_held
#print axioms AtPublicFiles.KeyBook.counts_held
#print axioms AtPublicFiles.KeyBook.cut_spans
#print axioms AtPublicFiles.KeyBook.stated_counts
#print axioms AtPublicFiles.KeyBook.lastKey
#print axioms AtPublicFiles.KeyBook.spanOf
#print axioms AtPublicFiles.KeyBook.levelCall_held
#print axioms AtPublicFiles.KeyBook.map_ties
#print axioms AtPublicFiles.KeyBook.map_splits
#print axioms AtPublicFiles.KeyBook.map_tabs
#print axioms AtPublicFiles.KeyBook.map_keys
#print axioms AtPublicFiles.KeyBook.entries_held
