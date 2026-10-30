-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/ExactFresh/Whole.lean: CONDITIONAL: the text of `Good.exact`
(Honest/Side.lean) WITHOUT ITS PREMISE ON `m.opened` (`ExactMember`, Honest/Small/Field.lean), at
the LAST TWO parts of the row of the layers' own rounds (kind K4): part 17 · 15 and the merge, part
18 · 16 (a part's two numbers: see AtParts.lean's head); then at EVERY member of a side whose row is
K4's; and `Good` at that side as one term, AT A := B := THE SENTENCE THAT NEVER HOLDS (False). Two
definitions; statements and proofs.

  `k4_closed_17`      part 17 in the first group of layers: one round that sends one scalar.
      (Part 15 in a later group is a quiet round: `k4_exact_quiet`, AtParts.lean.)
  `k4_closed_18_16`   the merge.
  `k4KindsAll`, `k4StatedAllB`   the sorts of ALL the row's parts; the test on a sub-protocol's
      rounds, part by part, at `betaMarked`.
  `seated_is`, `k4KindsAll_fair`, `k4_kind_all`, `k4Sided_length`   lists, sorts and shapes:
      `k4KindsAll` held against the row.
  `k4_closed_all`     **every member of K4's side.**
  `k4_fresh_all`      the identity on `fresh` at every member.
  `k4_good`, `k4_good_seated`   **`Good` as one term, at A := B := False**; at the side that
      `Side.seated` makes.

Limits. Each statement on `exact` is an equation of two laws over uniform coins, at one member by
itself, all else fixed in front of the coins: what the part shows over the runs that it spends, and
what its simulator yields over its own coins. `ExactMember` binds the state m by "∀": so the three
statements that end in it are at every value of `m.opened` at which On holds. EACH OF THE ROW's
SEVEN MASKED SUMCHECKS SPENDS TWO RUNS UNDER TWO NAMES, "sum" and "ends": at six both are of the
segment's mask row; AT THE MERGE ALONE THEY ARE OF TWO MESSAGES: "sum" of the segment's mask row,
"ends" of the index-mask message. Which part owns each is the book's to say. In each equation the
two runs are sampled as a product: THAT THEY ARE SO WHERE THEY ARE SPENT IS NOT SAID HERE. The
statement at the merge is one call of the law on the frame's masked sumcheck's part IN ITS FORM
UNDER THE LIBRARY's `shapeOk` (`exact_sumPart_field`, Honest/SumLaw/SumExact.lean), which the
merge's shape passes at every plan; that at part 17 · 15 is one call of the law on the frame's round
of scalars (in the first group of layers) or on its quiet round (in a later group) (Honest/Small/).
AT THE ROW (`k4_closed_all`, and so `k4_good`) ALL SEVEN MASKED SUMCHECKS, THE MERGE AMONG THEM, GO
THROUGH `closed_of_kind` (Closed.lean), WHICH CALLS THE FORM UNDER `shapeFair`: they need that form
at two (where the two premises on the plan's numbers are gone: see Closed.lean's head) and call it
at seven; `k4_closed_17` and `k4_closed_18_16` are called by no file that its writers know of: they
and the row's statement are the same instances twice. The statements on `exact` are conditional on
`StatedBy`, and at a masked sumcheck on `betaMarked`, at the rounds at which the member is seated:
THAT THE ROUNDS OF ANY DESCRIPTION's MEMBER MEET THEM IS NOT SHOWN (what is shown:
Law/ExactFresh/AtSide.lean: all rounds with the entries of the verifier's table and no oracle
message meet them); Law/ExactFresh/WholeTest.lean (no part of the library yet) evaluates
`k4StatedAllB`, and the premises of `k4_good` together, at a small synthetic plan alone. That a
description's member meets the place and the two counts, or its book the test `noneSpent`, is not
shown here (the count of rounds at the side that `k4Side` makes: `k4Side_count`,
Law/ExactFresh/AtSideGood.lean). `k4_good` IS `Good` AT A := B := fun _ _ _ _ => False: SO ITS
FIELDS plays AND acc ARE MET FOR NOTHING (they hold vacuously): NOTHING IS SAID ON THE PLAYING OR ON
WHAT THE VERIFIER ACCEPTS. ITS FIELD fresh IS AN IDENTITY THAT HOLDS OF ANY PART OF WHICH NOTHING IS
SPENT: TRUE AND EMPTY: IT IS NOT fresh AT THE OWNERS OF THE RUNS THAT K4 SPENDS. OF ITS FIELD fits
TWO OF THREE CLAUSES ARE PREMISES HERE. WHAT THE TERM ADDS IS exact, CONDITIONAL ON THE TEST ON THE
ROUNDS. IT IS NO LAW MORE THAN `k4_fits`, `k4_closed_all`, `k4_fresh_all`; a caller at another A
takes these. On and bud are True: they shut out no state and no position: the fields' own other
premises stay (at exact: `m.seen = front.seen`, `drawsFit`, `front.holds`, not stopped by the second
stop), AND THE TERM's exact IS ASKED ONLY WHERE `m.opened` IS WHAT front HOLDS FOR THE READS OF pre.
pre IS A FREE LETTER: a list of triples (a chain's number, a `firstTree`, declared rounds), of which
`readsBefore` (Honest/Side.lean) makes the reads of these rounds at the challenges that front holds
of that chain. NOTHING IS ASKED OF IT, AND NOTHING TIES IT TO A DESCRIPTION OR TO A PLAYER: WHERE
THE PREMISE FAILS, AS IT MAY AT A PLAYER's STATES IF pre IS NOT THE ROUNDS WHOSE COLUMNS THAT PLAYER
HANDS, THE TERM's exact ASKS NOTHING. AT A STATE WHOSE `opened` IS `none`, as the players that hand
no columns have it (`run`, `midAt`, Honest/Frame.lean), the premise holds, at whatever pre, only
where front lacks a column for one of these reads. The proof drops the premise (`exactAt_of_exact`,
Honest/Small/Field.lean): so at each pre the term's exact says no more than `k4_closed_all`. In the
first two statements the type Pb is free: a statement says something only where a face exists. The
statements say nothing on whether a job or a value is the protocol's.
What a caller still owes beside these equations, and none of it is shown here: `fresh` AT THE OWNERS
of the runs that are spent: the sender of the segment's mask row, and, for the merge's "ends", the
sender of the index-mask message: where one part sends both messages, one sentence on the pair; else
two, and then besides that the two runs are jointly uniform; that the book lends these runs; that no
coin stands in two runs; the condition on a job that reads what has been seen: on the items of the
rounds shown it stands in the head of Honest/Sum.lean; on the opened columns, which a job is handed
with them, the head of Honest/SumLaw/SumExact.lean leaves it to the caller; `exact` at the parts
that carry these coins later. Of the row's jobs and values one alone reads what has been seen, the
job of part 11 · 9: it reads the rounds shown (`fr.seen.rounds`) and not the opened columns.

Kin. `k4_fresh_all` IS A CASE OF `fresh_at` (Honest/K14/GoodCalls.lean, of other writers): the same
premise and the same end, there at any two types V and W, here at `Local` and Pb := Xi. `seated_is`:
`block_of_seated` (Honest/K3/Law/Keep/SideKeep.lean, of other writers) has, from the same
hypothesis, which sub-protocol was found, the row and the fall: its clause on the row is this one's
first; this one's second follows from its first. NEARER, at a row with its letters: `side_ok`
(Honest/Law/Rule/Members.lean, the frame's) has both clauses, and that the sub-protocol is of the
list, from `Lettered.side`, which is `Side.seated` at the letters' place and row; `side_place`
(Honest/Law/OwedRule.lean, the frame's) has the second. `k4_closed_all`: the like at the output
head's row is `head_exact_all` (Honest/K6/Law/GoodRowSum.lean). `Good` as one term at A := False
stands for other kinds, among others: `k5_good` and `k5_good_seated` (Honest/K5/Law/Good.lean,
SLot5.lean), `good_rows` (Honest/K14/GoodSeated.lean), `head_good_all`
(Honest/K6/Law/GoodRowSum.lean: B is free there): of other writers. K6's has `pre` as a free letter,
as here; HOW K5's AND K14's BIND `pre` WAS NOT HELD: the writer had these three files in the form in
which `Good` had no such letter. None of these eight files lies beneath this one, and none of these
statements is called. In this folder: `k4_closed_17` and `k4_closed_18_16`: see Limits.
`k4_kind_all` and `k4KindsAll_fair` go through all the row's numbers anew: at the numbers that
`k4Kinds` lists they say what `k4_kind_of` (Join.lean) and `k4Kinds_fair` (Closed.lean) say, and
call neither. `k4_closed_all` at the members but the last two has the end of `k4_closed_row`
(Closed.lean), under a test that reads two parts' rounds more, and does not call it.
`k4_good_seated` stands again at the side that `k4Side` makes, as `k4_good_side`
(Law/ExactFresh/AtSideGood.lean), which lies above this file. Sought: by statement, to the letter
and up to the bound letters, and by short name, among the theorems of the library as it lay with the
writer, and by short name among the definitions under Honest/: no hit. The search by statement does
not see a statement that has a binder in front of the colon where ours has it behind, or the other
way round. That search does not see letters that a "variable" line brings: `fresh_at` was found by
the name `noneSpent`, the others by `ExactMember`, `Good` and `Side.seated`; `side_ok` and
`side_place`, which name `Lettered.side`, by a reader, by the text of their ends; those in this
folder by a reader. Not sought: twins of the two definitions in other letters.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.ExactFresh.Closed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Oracle Place)
open VerifiableInference.Desc.Part.MaskedSum (Call)
open ProofFile.Honest.Small (ExactMember FreshMember noneSpent scalarsPart_exact_lift stated_scalars_of)
open ProofFile.Honest.SumLaw (StatedBy betaMarked shapeFair exact_sumPart_field)

section
variable {S Cl W₀ Rc Xi Tr X Pb : Type}
  (φ : Face (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Pb)
  (σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) (chain firstTree : Nat)
  (On : (u : Member (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) → CsAll u.part.carries →
    Mid (Local W₀ Rc Xi Tr) X → Before → Prop)
  (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop)
  (Q : K4Pub) (cells : Tr → Cells) (weights : W₀ → Weights) (tokens : Xi → Array Nat)
  (look : List Fmt.Drawn → OnBytes.Model.Forest.Heard)
  (j : Nat) (rs : List (Fmt.DeclaredRound × List Oracle))

/-- **Part 17 in the first group of layers: the embedding's value, one scalar in a round by
itself.** CONDITIONAL on `StatedBy` at the member's round. At every number j and all rounds rs, and
at every Q, of a later group too. -/
theorem k4_closed_17 (h0 : StatedBy [1] rs) :
    ExactMember φ σ chain firstTree On bud
      ⟨j, rs, k4Lift Q cells weights tokens look
        (k4Scalars Q 1 (fun Q w p => [embValue Q w p]) j),
        scalarsSim (k4Addr Q j) 1⟩ :=
  scalarsPart_exact_lift φ σ chain firstTree On bud j _ rs (k4Addr Q j) _ _ _ _ _ _
    (stated_scalars_of h0)

/-- **Part 18 · 16: the merge: the one part whose two runs are of two messages**: its run "sum" is
of the segment's mask row, its run "ends" of the index-mask message; which part owns each is the
book's to say. In the equation the two are sampled as a product: that they are so where they are
spent is not said here. CONDITIONAL on `StatedBy` and on `betaMarked` at the member's rounds, and on
nothing else. At every number j and all rounds rs. -/
theorem k4_closed_18_16
    (h0 : StatedBy (scalarsOf (k4PlainShape Q.P.wsLay.lk 1 1)) rs)
    (hY : betaMarked (k4PlainShape Q.P.wsLay.lk 1 1) rs = true) :
    ExactMember φ σ chain firstTree On bud
      ⟨j, rs, k4Lift Q cells weights tokens look
        (k4Sum Q (k4PlainShape Q.P.wsLay.lk 1 1) indexMaskRun jobMerge j),
        sumSim (k4Addr Q j) (k4PlainShape Q.P.wsLay.lk 1 1)⟩ :=
  exact_sumPart_field φ σ chain firstTree On bud (fun _ => ())
    (k4Wit Q cells weights tokens look) (fun _ => ()) (fun x _ => x) (fun _ _ => rfl) (fun _ => rfl)
    _ _ (k4SumJob _ fun w fr => jobMerge Q w (ptsOf Q w fr.heard))
    (shapeOk_plain _ (Nat.le_refl 1) (Nat.le_refl 1)) rs h0 hY j (k4Addr Q j)

end

/-- **The sorts of all the row's parts**, in order. -/
def k4KindsAll (Q : K4Pub) : List K4Kind :=
  k4Kinds Q ++ [if Q.g == 0 then .lone 1 else .quiet, .ms (k4PlainShape Q.P.wsLay.lk 1 1)]

/-- **The test on the rounds of a sub-protocol, at all the row's parts**: public data alone. Rounds
behind the row's are not read; `Side.fits` counts them. -/
def k4StatedAllB (Q : K4Pub) (rs : List (Fmt.DeclaredRound × List Oracle)) : Bool :=
  statedWalk betaMarked (k4KindsAll Q) rs

/-! ## Lists, sorts and shapes: helpers -/

/-- The side that `Side.seated` makes has the row that it was handed, and stands at the place. -/
theorem seated_is {S Cl V W X Pb : Type} {bs : List (VerifiableInference.Desc.Block S Cl)}
    {a : Place} {row : List (Part V W X × Sim Pb)} {fs : List (Fall S)}
    {σ : Side S Cl V W X Pb} (h : Side.seated bs a row fs = some σ) :
    σ.row = row ∧ σ.block.place = a := by
  unfold Side.seated at h
  cases hf : bs.find? (fun b => b.place == a) with
  | none =>
    rw [hf] at h
    cases h
  | some b =>
    rw [hf] at h
    obtain rfl := Option.some.inj h
    have hp : (b.place == a) = true :=
      List.find?_some (p := fun c : VerifiableInference.Desc.Block S Cl => c.place == a) hf
    exact ⟨rfl, eq_of_beq hp⟩

/-- **The shapes that `k4KindsAll` lists pass `shapeFair`**, at every plan. -/
theorem k4KindsAll_fair (Q : K4Pub) {i : Nat} {k : Call}
    (hx : (k4KindsAll Q)[i]? = some (.ms k)) : shapeFair k = true := by
  unfold k4KindsAll k4Kinds at hx
  by_cases h : (Q.g == 0) = true
  · simp only [h, ↓reduceIte] at hx
    exact match i, hx with
    | 0, hx => by cases Option.some.inj hx
    | 1, hx => by cases Option.some.inj hx
    | 2, hx => by cases Option.some.inj hx
    | 3, hx => by cases Option.some.inj hx
    | 4, hx => by cases Option.some.inj hx
    | 5, hx => by
      obtain rfl := K4Kind.ms.inj (Option.some.inj hx)
      exact shapeFair_level _
    | 6, hx => by cases Option.some.inj hx
    | 7, hx => by cases Option.some.inj hx
    | 8, hx => by
      obtain rfl := K4Kind.ms.inj (Option.some.inj hx)
      exact shapeFair_token _ _ (by decide)
    | 9, hx => by
      obtain rfl := K4Kind.ms.inj (Option.some.inj hx)
      exact shapeFair_token _ _ (Nat.le_refl 1)
    | 10, hx => by cases Option.some.inj hx
    | 11, hx => by
      obtain rfl := K4Kind.ms.inj (Option.some.inj hx)
      exact shapeFair_plain _ _ (by decide)
    | 12, hx => by
      obtain rfl := K4Kind.ms.inj (Option.some.inj hx)
      exact shapeFair_level _
    | 13, hx => by cases Option.some.inj hx
    | 14, hx => by cases Option.some.inj hx
    | 15, hx => by
      obtain rfl := K4Kind.ms.inj (Option.some.inj hx)
      exact shapeFair_level _
    | 16, hx => by cases Option.some.inj hx
    | 17, hx => by cases Option.some.inj hx
    | 18, hx => by
      obtain rfl := K4Kind.ms.inj (Option.some.inj hx)
      exact shapeFair_plain _ _ (Nat.le_refl 1)
    | n + 19, hx => by simp at hx
  · rw [Bool.not_eq_true] at h
    simp only [h, Bool.false_eq_true, ↓reduceIte] at hx
    exact match i, hx with
    | 0, hx => by cases Option.some.inj hx
    | 1, hx => by cases Option.some.inj hx
    | 2, hx => by cases Option.some.inj hx
    | 3, hx => by
      obtain rfl := K4Kind.ms.inj (Option.some.inj hx)
      exact shapeFair_level _
    | 4, hx => by cases Option.some.inj hx
    | 5, hx => by cases Option.some.inj hx
    | 6, hx => by
      obtain rfl := K4Kind.ms.inj (Option.some.inj hx)
      exact shapeFair_token _ _ (by decide)
    | 7, hx => by
      obtain rfl := K4Kind.ms.inj (Option.some.inj hx)
      exact shapeFair_token _ _ (Nat.le_refl 1)
    | 8, hx => by cases Option.some.inj hx
    | 9, hx => by
      obtain rfl := K4Kind.ms.inj (Option.some.inj hx)
      exact shapeFair_plain _ _ (by decide)
    | 10, hx => by
      obtain rfl := K4Kind.ms.inj (Option.some.inj hx)
      exact shapeFair_level _
    | 11, hx => by cases Option.some.inj hx
    | 12, hx => by cases Option.some.inj hx
    | 13, hx => by
      obtain rfl := K4Kind.ms.inj (Option.some.inj hx)
      exact shapeFair_level _
    | 14, hx => by cases Option.some.inj hx
    | 15, hx => by cases Option.some.inj hx
    | 16, hx => by
      obtain rfl := K4Kind.ms.inj (Option.some.inj hx)
      exact shapeFair_plain _ _ (Nat.le_refl 1)
    | n + 17, hx => by simp at hx

section
variable {W₀ Rc Xi Tr X : Type} (Q : K4Pub) (cells : Tr → Cells) (weights : W₀ → Weights)
  (tokens : Xi → Array Nat) (look : List Fmt.Drawn → OnBytes.Model.Forest.Heard)

/-- **The row's part number i is of the sort that `k4KindsAll` lists at i.** -/
theorem k4_kind_all {i : Nat} {x : K4Kind} (hx : (k4KindsAll Q)[i]? = some x) :
    ∃ y, (k4Sided (Rc := Rc) (X := X) Q cells weights tokens look)[i]? = some y ∧
      x.Of Q cells weights tokens look i y := by
  unfold k4KindsAll k4Kinds at hx
  unfold k4Sided k4Row k4RowIn k4Sims k4Sorts k4Shapes
  by_cases h : (Q.g == 0) = true
  · simp only [h, ↓reduceIte] at hx ⊢
    exact match i, hx with
    | 0, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, rfl⟩
    | 1, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, rfl⟩
    | 2, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, rfl⟩
    | 3, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, _, rfl⟩
    | 4, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, rfl⟩
    | 5, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, _, rfl, _, _, rfl⟩
    | 6, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, rfl⟩
    | 7, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, _, rfl⟩
    | 8, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, _, rfl, _, _, rfl⟩
    | 9, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, _, rfl, _, _, rfl⟩
    | 10, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, rfl⟩
    | 11, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, _, rfl, _, _, rfl⟩
    | 12, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, _, rfl, _, _, rfl⟩
    | 13, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, rfl⟩
    | 14, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, rfl⟩
    | 15, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, _, rfl, _, _, rfl⟩
    | 16, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, rfl⟩
    | 17, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, _, rfl⟩
    | 18, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, _, rfl, _, _, rfl⟩
    | n + 19, hx => by simp at hx
  · rw [Bool.not_eq_true] at h
    simp only [h, Bool.false_eq_true, ↓reduceIte] at hx ⊢
    exact match i, hx with
    | 0, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, rfl⟩
    | 1, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, _, rfl⟩
    | 2, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, rfl⟩
    | 3, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, _, rfl, _, _, rfl⟩
    | 4, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, rfl⟩
    | 5, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, _, rfl⟩
    | 6, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, _, rfl, _, _, rfl⟩
    | 7, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, _, rfl, _, _, rfl⟩
    | 8, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, rfl⟩
    | 9, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, _, rfl, _, _, rfl⟩
    | 10, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, _, rfl, _, _, rfl⟩
    | 11, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, rfl⟩
    | 12, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, rfl⟩
    | 13, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, _, rfl, _, _, rfl⟩
    | 14, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, rfl⟩
    | 15, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, rfl⟩
    | 16, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, _, rfl, _, _, rfl⟩
    | n + 17, hx => by simp at hx

/-- The row has as many parts as `k4KindsAll` lists. -/
theorem k4Sided_length :
    (k4Sided (Rc := Rc) (X := X) Q cells weights tokens look).length = (k4KindsAll Q).length := by
  unfold k4KindsAll k4Kinds k4Sided k4Row k4RowIn k4Sims k4Sorts
  cases (Q.g == 0) <;> rfl

end

section
variable {S Cl W₀ Rc Xi Tr X : Type}
  (pre : List (Nat × Nat × List Fmt.DeclaredRound))
  (φ : Face (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Xi)
  (σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) (Bk : ProverCoinCounts) (ord : List Place)
  (chain firstTree : Nat)
  (On : (u : Member (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) → CsAll u.part.carries →
    Mid (Local W₀ Rc Xi Tr) X → Before → Prop)
  (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop)
  (Q : K4Pub) (cells : Tr → Cells) (weights : W₀ → Weights) (tokens : Xi → Array Nat)
  (look : List Fmt.Drawn → OnBytes.Model.Forest.Heard)

/-- **Every member of K4's side**, under one test on the rounds of the side's own sub-protocol.
CONDITIONAL: see the head. -/
theorem k4_closed_all (hr : σ.row = k4Sided Q cells weights tokens look)
    (h0 : k4StatedAllB Q (σ.block.rounds.zip σ.block.oracles) = true) :
    ∀ u ∈ σ.members, ExactMember φ σ chain firstTree On bud u := by
  intro u hu
  obtain ⟨t, y, hy, rfl⟩ := membersOf_at σ.row 0 _ u hu
  have hy' := hy
  rw [hr] at hy'
  have ht : t < (k4KindsAll Q).length := by
    rw [← k4Sided_length (Rc := Rc) (X := X) Q cells weights tokens look]
    exact (List.getElem?_eq_some_iff.1 hy').1
  have hx := List.getElem?_eq_getElem ht
  generalize (k4KindsAll Q)[t] = x at hx
  obtain ⟨y', hy'', hof⟩ := k4_kind_all (Rc := Rc) (X := X) Q cells weights tokens look hx
  obtain rfl : y' = y := Option.some.inj (hy''.symm.trans hy')
  simp only [Nat.zero_add]
  exact closed_of_kind φ σ chain firstTree On bud Q cells weights tokens look hof
    (fun k hk => k4KindsAll_fair Q (hk ▸ hx)) _
    (walk_member Q cells weights tokens look betaMarked (k4KindsAll Q) σ.row
      (fun i x hi => hr ▸ k4_kind_all (Rc := Rc) (X := X) Q cells weights tokens look hi) _ h0 hx
      hy)

/-- **The identity on `fresh` at every member.** At every side of these types: nothing of K4 is in
it. TRUE AND EMPTY, and not `fresh` at the owners of the runs that K4 spends: see the head.
CONDITIONAL on a test on the book at every member's address. -/
theorem k4_fresh_all
    (hb : ∀ u ∈ σ.members, noneSpent Bk ⟨σ.block.place, u.number⟩ = true) :
    ∀ u ∈ σ.members, FreshMember φ σ Bk ord bud u :=
  fun u hu => k4_fresh_once φ σ Bk ord bud u (hb u hu)

/-- **`Good` at K4's row, as one term, AT A := B := THE SENTENCE THAT NEVER HOLDS (False): SO plays
AND acc HOLD VACUOUSLY. fresh IS AN IDENTITY THAT HOLDS OF ANY PART OF WHICH NOTHING IS SPENT: IT IS
NOT fresh AT THE OWNERS OF THE RUNS THAT K4 SPENDS. OF fits, TWO OF THREE CLAUSES ARE PREMISES HERE.
WHAT THE TERM ADDS IS exact, CONDITIONAL ON THE TEST ON THE ROUNDS. NO LAW MORE THAN `k4_fits`,
`k4_closed_all`, `k4_fresh_all`: A CALLER AT ANOTHER A TAKES THESE.** On and bud are True.
pre: A FREE LETTER, OF WHICH NOTHING IS ASKED, TIED TO NO DESCRIPTION AND TO NO PLAYER. exact alone
reads it, in its premise that `m.opened` is what front holds for the reads of pre: WHERE THAT
PREMISE FAILS THE TERM's exact ASKS NOTHING. The proof drops the premise: at each pre the term's
exact says no more than `k4_closed_all`.
CONDITIONAL: the side's row is K4's; its sub-protocol stands at K4's place, has as many rounds as
the row has moves and as many lists of oracle messages; these rounds pass the test part by part; no
entry of the book by which a part spends names a member as owner. -/
theorem k4_good (hr : σ.row = k4Sided Q cells weights tokens look)
    (hp : σ.block.place = k4Place Q)
    (hl : σ.block.rounds.length = ((k4RowIn Q).map (·.moves.length)).sum)
    (ho : σ.block.oracles.length = σ.block.rounds.length)
    (h0 : k4StatedAllB Q (σ.block.rounds.zip σ.block.oracles) = true)
    (hb : ∀ u ∈ σ.members, noneSpent Bk ⟨σ.block.place, u.number⟩ = true) :
    Good pre φ σ Bk ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False)
      (fun _ _ _ _ => True) (fun _ _ _ => True) :=
  ⟨k4_fits σ Q cells weights tokens look hr hp hl ho, fun _ _ _ _ _ h => h.elim,
    fun _ _ _ _ _ h => h.elim,
    fun u hu => Small.exactAt_of_exact pre
      (k4_closed_all φ σ chain firstTree (fun _ _ _ _ => True) (fun _ _ _ => True) Q cells weights
        tokens look hr h0 u hu),
    k4_fresh_all φ σ Bk ord (fun _ _ _ => True) hb⟩

/-- **The same at the side that `Side.seated` makes** of a list of sub-protocols, K4's place, K4's
row and whatever falls: AT A := B := THE SENTENCE THAT NEVER HOLDS (False): SO plays AND acc HOLD
VACUOUSLY. fresh IS AN IDENTITY THAT HOLDS OF ANY PART OF WHICH NOTHING IS SPENT: IT IS NOT fresh AT
THE OWNERS OF THE RUNS THAT K4 SPENDS. OF fits, TWO OF THREE CLAUSES ARE PREMISES HERE. WHAT THE
TERM ADDS IS exact, CONDITIONAL ON THE TEST ON THE ROUNDS. NO LAW MORE THAN `k4_fits`,
`k4_closed_all`, `k4_fresh_all`: A CALLER AT ANOTHER A TAKES THESE.** On and bud are True.
pre: A FREE LETTER, OF WHICH NOTHING IS ASKED, TIED TO NO DESCRIPTION AND TO NO PLAYER. exact alone
reads it, in its premise that `m.opened` is what front holds for the reads of pre: WHERE THAT
PREMISE FAILS THE TERM's exact ASKS NOTHING. The proof drops the premise: at each pre the term's
exact says no more than `k4_closed_all`.
CONDITIONAL: as `k4_good`, but for the row and the place, which are that side's own. -/
theorem k4_good_seated {bs : List (VerifiableInference.Desc.Block S Cl)} {fs : List (Fall S)}
    (hσ : Side.seated bs (k4Place Q) (k4Sided Q cells weights tokens look) fs = some σ)
    (hl : σ.block.rounds.length = ((k4RowIn Q).map (·.moves.length)).sum)
    (ho : σ.block.oracles.length = σ.block.rounds.length)
    (h0 : k4StatedAllB Q (σ.block.rounds.zip σ.block.oracles) = true)
    (hb : ∀ u ∈ σ.members, noneSpent Bk ⟨σ.block.place, u.number⟩ = true) :
    Good pre φ σ Bk ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False)
      (fun _ _ _ _ => True) (fun _ _ _ => True) :=
  k4_good pre φ σ Bk ord chain firstTree Q cells weights tokens look (seated_is hσ).1
    (seated_is hσ).2 hl ho h0 hb

end

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4_closed_17
#print axioms ProofFile.Honest.K4.k4_closed_18_16
#print axioms ProofFile.Honest.K4.k4KindsAll
#print axioms ProofFile.Honest.K4.k4StatedAllB
#print axioms ProofFile.Honest.K4.seated_is
#print axioms ProofFile.Honest.K4.k4KindsAll_fair
#print axioms ProofFile.Honest.K4.k4_kind_all
#print axioms ProofFile.Honest.K4.k4Sided_length
#print axioms ProofFile.Honest.K4.k4_closed_all
#print axioms ProofFile.Honest.K4.k4_fresh_all
#print axioms ProofFile.Honest.K4.k4_good
#print axioms ProofFile.Honest.K4.k4_good_seated
