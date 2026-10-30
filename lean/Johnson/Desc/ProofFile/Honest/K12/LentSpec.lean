-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/LentSpec.lean: two statements, L-5 and L-6, on the step from the
random values that a part of a proximity test's prover is given to the `TestCoins` (Test.lean) that
its moves pass on, as eleven named `Prop`s, with the definitions that they need. No statement is
proved here. `Spec.first_reads_in` is proved (`first_reads_in`, LentLaw3.lean). No statement of this
library concludes any of the other ten as it stands here, and these are under no test. Parts stand
in other letters: of `Spec.lent_mem`, the second part's clause is `mem_rest`, and the first part's,
at the job `jobL`, `mem_first_L` (AtProof/SeamL.lean); of `Spec.lent_parts`, the moves at the
readers `firstRd` and `restCoins` (`first_moves`, and, at two stages or more, `rest_moves`,
HalfSteps.lean), tied to `firstPartBy` and `restPartBy` at tm := `testAll J` alone
(`firstPartBy_testAll`, `restPartBy_testAll`, PartsByLaw.lean); of `Spec.first_meets`, what is had
in another form is told at Parts.lean and PartsBy.lean. It imports Mathlib.

A part states three counts: the values of its own (`takes`), the stretches that it spends, and the
stretches that it carries (`Part`, Johnson/Desc/ProofFile/Honest/Frame.lean). Its moves are given
values of just these counts (`Handed`). The two parts of PartsBy.lean turn them into a `TestCoins`
by three functions: `restCoins` (Parts.lean) in the second part, and two functions that are written
out inside `firstPartBy`, named here `rdOwn` (the first fold sends its own fresh table) and
`rdEarlier` (the table was sent before the test).

  `LentAt`, `readLent`, `lentAll`   an entry of what a part is given; the value there; all entries
                 within the three counts
  `TestSrc`, `TestCoins.readAll`, `allTest`   a number of a `TestCoins`, the members' values
                 included; the value there; all numbers within the counts (`allSrc`, KeptSpec.lean,
                 and each member's stated count)
  `rdOwn`, `rdEarlier`   the first part's two functions, under names
  `lentRest`, `lentOwn`, `lentEarlier`   for each number of the `TestCoins`: the entry that it is
                 read from; none where the function writes 0
  `Spec.lent_parts`   the named functions are the parts' own: `firstPartBy` is built with `rdOwn` or
                 `rdEarlier`, and every move of `restPartBy` with `restCoins`
  `Spec.lent_reads`   the value at a number is the value at its entry, or 0 where it has none
  `Spec.lent_perm`, `Spec.lent_nodup`   where the list of stages is not empty: on the numbers within
                 the counts the map to entries is a rearrangement of `lentAll`, which has no repeat:
                 one to one, within the counts that the part states, and onto. (At an empty list the
                 first stage counts as a stage of zeros, both parts state a count of 1, and `allSrc`
                 is empty.)
  `Spec.lent_free`   the entries within the counts can be set one by one. Without it "one to one"
                 would end at the names of entries: `readLent` is made of the readers `stretchOf`
                 and `stretches` (Coins.lean), which the parts use
  `Spec.lent_fibres`   every choice of values at the entries within the counts is had from equally
                 many things given
  `Spec.lent_mem`   a member's values, of both fields, are the carried stretch of its number
  `Spec.first_reads_in`   L-6: `Spec.first_reads` (KeptSpec.lean) with hypotheses within the counts
                 alone, at the job of a `ManyJob`; a member of the list is still compared whole, in
                 both fields and beyond its stated count
  `Spec.test_reads_in`   the like of `Spec.test_reads`, for all rounds of the test
  `Spec.first_meets`   L-6 between the two parts' own `TestCoins`, where both parts are given the
                 same values at the entries of each number within the counts
  `Spec.kept_lent`   from a kept address to an entry of what the second part is given: different
                 addresses have different entries, within the counts

The two written zeros. In the first part the switches' values (`rest`) are 0, and, where the table
was sent before the test, so are the table's tails. The first part is given neither: they are among
what the second part is given. So the first part's `TestCoins` holds 0 at numbers at which the
second part's holds a value. `Spec.first_reads` (KeptSpec.lean) says, where the stages pass
`StagesOk` and for `testAll`, that the messages of the first part's rounds do not depend on these
numbers. Its hypotheses are equations of whole functions, and between the two parts' `TestCoins`
these fail outside the counts, even where both parts are given the same values: at the member number
after the last (0 against the fresh table's stretch), and, where the table was sent before the test,
at the coefficients from 2 k + 1 on (0 against the tails). Hence L-6. At a general `TestJob`, and at
a `RunJob`, the rows are a function of all members' values, so L-6 is stated at a `ManyJob`, whose
rows read the members of its list alone. Where `StagesOk` fails nothing is said on the zeros. The
readers write two more kinds of 0: beyond a count, and beyond the list of stretches.

Limits.
- Statements only. `rdOwn` and `rdEarlier` repeat two functions of `firstPartBy`; `Spec.lent_parts`
  is the statement that they agree. At `tm := testAll J` the parts are Parts.lean's
  (`firstPartBy_testAll`, `restPartBy_testAll`, PartsByLaw.lean).
- `LentAt`, `lentAll` and `allTest` list values of the extension field. A member's values of the
  base field are covered by `Spec.lent_mem` alone. The test's own counts have none.
- The maps are one to one on `allTest`, not on all numbers. In `restCoins`: a coefficient from 2 k +
  1 on is a tail's entry; a tail's entry beyond its row's length is the next row's; the member
  number after the last is the fresh table's stretch; a tail's row beyond the table is 0. That the
  result does not depend on the first two and the last is L-1 and L-2 (KeptSpec.lean), where the
  stages pass `StagesOk`; on the side of `testAll` at `R.toTest` alone (`Spec.test_reads`). These
  say nothing on the member number after the last: `Spec.test_reads` asks that all members' values
  agree. For it: `Spec.first_reads_in` and `Spec.test_reads_in`, at the job of a `ManyJob` alone.
- The counts are those that the part states. `lendPart` and `lend` (Frame.lean) refuse a part whose
  `takes`, or an entry whose name or count, is not the book's: that is the frame's code; no
  statement here says it.
- The border in the carried stretch of the fresh table (2 k + 1, then rows of Z.r entries) is
  computed from the job's first stage. Where the table was sent before the test, nothing here says
  that its sender laid it by the same k, h and Z.r (for the shared chain: FitShared.lean).
- `allTest` counts a member by the count that the job states. Nothing here says that this is what
  its rows read (for the shared chain: `dueOf`, `Spec.mem_reads`).
- `Spec.lent_fibres` and `Spec.lent_free` speak of all three counts at once; at fixed carried
  stretches they are had at an empty list of carried stretches. The B of `Spec.lent_fibres` is not
  named by the statement.
- Which values of which owner a stretch holds is the book's matter (`lendRow`, Frame.lean). Two
  stretches that one part carries may hold the same values. Nothing here says that the stretch from
  which the first part reads the coefficients and the stretch from which the second part reads them
  hold the same values.
- None of the statements says that values are distinct, or how they are sampled. Nothing on
  completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.KeptSpec
import Johnson.Desc.ProofFile.Honest.K12.PartsBy
import Johnson.Desc.ProofFile.Honest.K12.RunMany

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes.Slice (GE)

variable {W X : Type}

/-! ## 1 What a part is given, and what its moves pass on -/

/-- An entry, of the extension field, of what a part is given: number n of its own values, of the
stretch number i that it spends, or of the stretch number i that it carries. -/
inductive LentAt where
  | own (n : ℕ)
  | spent (i n : ℕ)
  | carried (i n : ℕ)
  deriving DecidableEq, Repr

/-- The value at an entry; 0 beyond a count, and beyond the list of stretches. -/
def readLent {takes : Due} {spends carries : List (String × Due)}
    (c : Handed takes spends carries) : LentAt → GE
  | .own n => (stretchOf c.1).e n
  | .spent i n => (stretches spends c.2.1 i).e n
  | .carried i n => (stretches carries c.2.2 i).e n

/-- All entries within the three counts. -/
def lentAll (takes : Due) (spends carries : List (String × Due)) : List LentAt :=
  (List.range takes.e).map .own ++
    (spends.zipIdx.flatMap fun d => (List.range d.1.2.e).map (.spent d.2)) ++
    carries.zipIdx.flatMap fun d => (List.range d.1.2.e).map (.carried d.2)

/-- A number of a `TestCoins`: one outside the members' values, or number n of member t's. -/
inductive TestSrc where
  | at (x : CoinSrc)
  | mem (t n : ℕ)
  deriving DecidableEq, Repr

/-- The value at a number. Declared in the namespace of `TestCoins`, ProofFile.Honest.K12, so that
`C.readAll` can be written. -/
def _root_.ProofFile.Honest.K12.TestCoins.readAll (C : TestCoins) : TestSrc → GE
  | .at x => C.read x
  | .mem t n => (C.mem t).e n

/-- All numbers within the counts: `allSrc`, and each member's stated count. -/
def allTest (J : TestJob W X) : List TestSrc :=
  (allSrc J.p.nums.stages).map .at ++
    J.members.zipIdx.flatMap fun m => (List.range m.1.2.2.e).map (.mem m.2)

/-! ## 2 The three functions, and where each number is read from -/

/-- The function in `firstPartBy` where the first fold sends its own fresh table. Its field `rest`
is no random value but the constant 0. Where the stages pass `StagesOk`, the messages of the first
part's rounds, computed by `testAll`, do not depend on it (L-4, `Spec.first_reads`; at the job of a
`ManyJob` L-6, `Spec.first_reads_in`). Where they do not pass, nothing is said. -/
def rdOwn (J : TestJob W X)
    (c : Handed ⟨0, dueFresh J.s₀⟩ [] (memberRuns J ⟨J.p.place, 0⟩)) : TestCoins :=
  ⟨(stretchOf c.1).e, tailsIn J.s₀ (stretchOf c.1).e, stretches _ c.2.2, fun _ => 0⟩

/-- The function in `firstPartBy` where the fresh table was sent before the test. Its fields `tails`
and `rest` are no random values but the constant 0. Where the stages pass `StagesOk`, the messages
of the first part's rounds, computed by `testAll`, do not depend on them (L-4, `Spec.first_reads`;
at the job of a `ManyJob` L-6, `Spec.first_reads_in`). Where they do not pass, nothing is said. -/
def rdEarlier (J : TestJob W X)
    (c : Handed ⟨0, 0⟩ [spentRun J] (memberRuns J ⟨J.p.place, 0⟩)) : TestCoins :=
  ⟨(stretchOf c.2.1.1).e, fun _ _ => 0, stretches _ c.2.2, fun _ => 0⟩

/-- The second part: the fresh table's stretch is the carried one after the members'. -/
def lentRest (J : TestJob W X) : TestSrc → LentAt
  | .at (.hide n) => .carried J.members.length n
  | .at (.tails b n) => .carried J.members.length (2 * J.s₀.k + 1 + b * J.s₀.Z.r + n)
  | .at (.rest n) => .own n
  | .mem t n => .carried t n

/-- The first part, where the fold sends its own fresh table. -/
def lentOwn (J : TestJob W X) : TestSrc → Option LentAt
  | .at (.hide n) => some (.own n)
  | .at (.tails b n) => some (.own (2 * J.s₀.k + 1 + b * J.s₀.Z.r + n))
  | .at (.rest _) => none
  | .mem t n => some (.carried t n)

/-- The first part, where the fresh table was sent before the test. -/
def lentEarlier : TestSrc → Option LentAt
  | .at (.hide n) => some (.spent 0 n)
  | .at (.tails _ _) => none
  | .at (.rest _) => none
  | .mem t n => some (.carried t n)

/-! ## 3 The statements -/

/-- The named functions are the parts' own. -/
def Spec.lent_parts : Prop :=
  ∀ (V W X : Type) (J : TestJob W X) (tm : Term W X),
    (J.fresh = none → (firstPartBy J tm : Part V W X) =
      { takes := ⟨0, dueFresh J.s₀⟩, spends := [], carries := memberRuns J ⟨J.p.place, 0⟩
        bad := fun _ _ => none, hid := fun _ _ _ => none, badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
        moves := movesBy J tm (rdOwn J) 0 (firstLen J.p.nums.stages) }) ∧
    (∀ a, J.fresh = some a → (firstPartBy J tm : Part V W X) =
      { takes := ⟨0, 0⟩, spends := [spentRun J], carries := memberRuns J ⟨J.p.place, 0⟩
        bad := fun _ _ => none, hid := fun _ _ _ => none, badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
        moves := movesBy J tm (rdEarlier J) 0 (firstLen J.p.nums.stages) }) ∧
    ∀ mv ∈ (restPartBy J tm : Part V W X).moves, ∃ i, mv = moveBy J tm (restCoins J) i

/-- The value at a number is the value at its entry, or 0 where it has none. -/
def Spec.lent_reads : Prop :=
  ∀ (W X : Type) (J : TestJob W X) (x : TestSrc),
    (∀ c, (restCoins J c).readAll x = readLent c (lentRest J x)) ∧
    (∀ c, (rdOwn J c).readAll x = ((lentOwn J x).map (readLent c)).getD 0) ∧
    ∀ c, (rdEarlier J c).readAll x = ((lentEarlier x).map (readLent c)).getD 0

/-- On the numbers within the counts the map to entries is one to one, within the counts that the
part states, and onto, where the list of stages is not empty. In the first part's two clauses the
numbers that have no entry are left out. -/
def Spec.lent_perm : Prop :=
  ∀ (W X : Type) (J : TestJob W X), J.p.nums.stages ≠ [] →
    ((allTest J).map (lentRest J)).Perm
      (lentAll ⟨0, dueRest J.p.nums.stages⟩ [] (memberRuns J ⟨J.p.place, 1⟩ ++ [freshRun J])) ∧
    ((allTest J).filterMap (lentOwn J)).Perm
      (lentAll ⟨0, dueFresh J.s₀⟩ [] (memberRuns J ⟨J.p.place, 0⟩)) ∧
    ((allTest J).filterMap lentEarlier).Perm
      (lentAll ⟨0, 0⟩ [spentRun J] (memberRuns J ⟨J.p.place, 0⟩))

/-- `lentAll` has no repeat, so that `Spec.lent_perm` says "one to one". -/
def Spec.lent_nodup : Prop :=
  ∀ (takes : Due) (spends carries : List (String × Due)), (lentAll takes spends carries).Nodup

/-- The entries within the three counts can be set one by one: for every choice of a value at each
entry there is something that a part can be given which has these values. So no two of these entries
are one coordinate of what is given, and none is a written 0. -/
def Spec.lent_free : Prop :=
  ∀ (takes : Due) (spends carries : List (String × Due)) (v : LentAt → GE),
    ∃ c : Handed takes spends carries, ∀ a ∈ lentAll takes spends carries, readLent c a = v a

/-- Up to a one-to-one renaming of what a part can be given, reading the entries within the three
counts is the projection from a product onto its first factor. So every choice of values at these
entries is had from equally many things given: as many as B has members. The statement asks only
that there is such a B; what is given of the base field is meant. It implies `Spec.lent_free`. -/
def Spec.lent_fibres : Prop :=
  ∀ (takes : Due) (spends carries : List (String × Due)),
    ∃ (B : Type) (e : Handed takes spends carries ≃
        ({a : LentAt // a ∈ lentAll takes spends carries} → GE) × B),
      ∀ c a, (e c).1 a = readLent c a.1

/-- L-6. `Spec.first_reads` (KeptSpec.lean) with hypotheses within the counts alone, at the job of a
`ManyJob` (RunMany.lean): the coefficients below 2 k + 1, the members of the list, and, where the
first fold sends its own fresh table, that table's tails within its rows. A member of the list is
still compared whole: both fields, beyond its stated count too. -/
def Spec.first_reads_in : Prop :=
  ∀ (W X : Type) (A : ManyJob W X) (w : W) (fr : Front X) (C C' : TestCoins) (D : ℕ → Fmt.Drawn)
    (i : ℕ), StagesOk A.p.nums.stages = true → i < firstLen A.p.nums.stages →
    (∀ n < 2 * A.s₀.k + 1, C.hide n = C'.hide n) → (∀ t < A.mems.length, C.mem t = C'.mem t) →
    (A.fresh.isNone = true → ∀ b < 2 ^ A.s₀.h, ∀ q < A.s₀.Z.r, C.tails b q = C'.tails b q) →
    msgAt A.toRun.toTest w fr C D i = msgAt A.toRun.toTest w fr C' D i

/-- `Spec.test_reads` (KeptSpec.lean) with hypotheses within the counts alone, at the job of a
`ManyJob`: the members of the list, each compared whole, and the numbers of `allSrc`. So no round of
the test, of either part, depends on the member number after the last. -/
def Spec.test_reads_in : Prop :=
  ∀ (W X : Type) (A : ManyJob W X) (w : W) (fr : Front X) (C C' : TestCoins) (D : ℕ → Fmt.Drawn),
    StagesOk A.p.nums.stages = true → (∀ t < A.mems.length, C.mem t = C'.mem t) →
    (∀ x ∈ allSrc A.p.nums.stages, C.read x = C'.read x) →
    testAll A.toRun.toTest w fr C D = testAll A.toRun.toTest w fr C' D

/-- From a kept address (KeptSpec.lean) to an entry of what the second part is given. The value at
any address of `sortedOf` at `restCoins J c` is the value at an entry, encoded. Where the stages
pass `StagesOk`, the kept addresses have different entries, all within the counts that the part
states. -/
def Spec.kept_lent : Prop :=
  ∀ (W X : Type) (J : TestJob W X),
    (∀ c a, (sortedOf J.p.nums.stages (restCoins J c)).read a =
      OnBytes.Slice.ofE (readLent c (lentRest J (.at (srcOf J.p.nums.stages a))))) ∧
    (StagesOk J.p.nums.stages = true →
      ((keptOf J.p.nums.stages).map fun a => lentRest J (.at (srcOf J.p.nums.stages a))).Nodup ∧
      ∀ a ∈ keptOf J.p.nums.stages, lentRest J (.at (srcOf J.p.nums.stages a)) ∈
        lentAll ⟨0, dueRest J.p.nums.stages⟩ [] (memberRuns J ⟨J.p.place, 1⟩ ++ [freshRun J]))

/-- L-6 between the two parts' own `TestCoins`, at the job J of a `ManyJob`. Where what the first
part is given (c) and what the second part is given (c') have the same value at the entries of each
number within the counts, and the members' values of the base field are the same, the messages of
the first part's rounds are the same at both. -/
def Spec.first_meets : Prop :=
  ∀ (W X : Type) (A : ManyJob W X) (J : TestJob W X), J = A.toRun.toTest →
    ∀ (w : W) (fr : Front X) (D : ℕ → Fmt.Drawn) (i : ℕ)
      (c' : Handed ⟨0, dueRest J.p.nums.stages⟩ [] (memberRuns J ⟨J.p.place, 1⟩ ++ [freshRun J])),
    StagesOk J.p.nums.stages = true → i < firstLen J.p.nums.stages →
    (J.fresh.isNone = true → ∀ c,
      (∀ x ∈ allTest J, ∀ a, lentOwn J x = some a → readLent c a = readLent c' (lentRest J x)) →
      (∀ t < J.members.length, (stretches _ c.2.2 t).f = (stretches _ c'.2.2 t).f) →
      msgAt J w fr (rdOwn J c) D i = msgAt J w fr (restCoins J c') D i) ∧
    (J.fresh.isSome = true → ∀ c,
      (∀ x ∈ allTest J, ∀ a, lentEarlier x = some a → readLent c a = readLent c' (lentRest J x)) →
      (∀ t < J.members.length, (stretches _ c.2.2 t).f = (stretches _ c'.2.2 t).f) →
      msgAt J w fr (rdEarlier J c) D i = msgAt J w fr (restCoins J c') D i)

/-- A member's values, of both fields, are the carried stretch of its number. -/
def Spec.lent_mem : Prop :=
  ∀ (W X : Type) (J : TestJob W X),
    (∀ c, (restCoins J c).mem = stretches _ c.2.2) ∧ (∀ c, (rdOwn J c).mem = stretches _ c.2.2) ∧
    ∀ c, (rdEarlier J c).mem = stretches _ c.2.2

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.LentAt
#print axioms ProofFile.Honest.K12.Light.readLent
#print axioms ProofFile.Honest.K12.Light.lentAll
#print axioms ProofFile.Honest.K12.Light.TestSrc
#print axioms ProofFile.Honest.K12.TestCoins.readAll
#print axioms ProofFile.Honest.K12.Light.allTest
#print axioms ProofFile.Honest.K12.Light.rdOwn
#print axioms ProofFile.Honest.K12.Light.rdEarlier
#print axioms ProofFile.Honest.K12.Light.lentRest
#print axioms ProofFile.Honest.K12.Light.lentOwn
#print axioms ProofFile.Honest.K12.Light.lentEarlier
#print axioms ProofFile.Honest.K12.Light.Spec.lent_parts
#print axioms ProofFile.Honest.K12.Light.Spec.lent_reads
#print axioms ProofFile.Honest.K12.Light.Spec.lent_perm
#print axioms ProofFile.Honest.K12.Light.Spec.lent_nodup
#print axioms ProofFile.Honest.K12.Light.Spec.lent_free
#print axioms ProofFile.Honest.K12.Light.Spec.lent_fibres
#print axioms ProofFile.Honest.K12.Light.Spec.first_reads_in
#print axioms ProofFile.Honest.K12.Light.Spec.test_reads_in
#print axioms ProofFile.Honest.K12.Light.Spec.kept_lent
#print axioms ProofFile.Honest.K12.Light.Spec.first_meets
#print axioms ProofFile.Honest.K12.Light.Spec.lent_mem
