-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/RunOf.lean: the input of `runBy` (RunBy.lean) computed from a
`TestJob` (what a caller of the reference definition `testAll` supplies, Test.lean), the prover's
input w, what precedes the test, and the random values. With it `runBy` and `testAll` can be
compared at any job: `runBy_eq` (RunByEq.lean). Definitions only. It imports Mathlib through
Test.lean.

  `sortedOf`     the random values of `testAll` (`TestCoins`), grouped by use, encoded
  `firstOf`      a first stage's state over the field (`PS`), tabulated as lists of words
  `RunIn.ofTest`   the input

`sortedOf` repeats the offsets of `coinsOf` and `hideAt` (Coins.lean). `tiesBy_of` (RunByTies.lean)
proves that the two agree, where the stages pass `okFrom`.

Limits.
- `RunIn.ofTest` evaluates the job's functions over the field and encodes each value, once for each
  entry. The trees are the job's own; the argument of `trees` is ignored. Every read of a coin
  recomputes `marksAt`. For rows and trees computed on words see RunJob.lean.
- Several subtractions in `sortedOf` truncate (i - 1, i - 2, k - 1, (n - 1) / 2 - 1, the pad's - 1).
  So some addresses read coins that belong to other addresses: under i = 1 the main and mask tails,
  the free entries, the pad and the masking word read from the first switch's coins; `hide` at n =
  1, 2 repeats n = 3, 4 (at k = 1: n = 0, 3). By the text of `keptOf` (KeptSpec.lean; no lemma) none
  of these addresses is kept where there are two stages or more; that over stages that pass
  `StagesOk` the result of a run at `Seams.lib` does not depend on them would follow from
  `Spec.kept_reads` (KeptSpec.lean), which no statement of this library concludes.
- At every switch `nextBy` lists more free entries than `csOwnG` keeps. Under `sortedOf` the first
  dropped address holds the pad's value (see `CoinTie`, RunBySpec.lean), and the others hold the
  values that follow it in the list of the switches' values: the mask tails', the next riders', and,
  at seven of the eight lists of stages in PlacesSmall.lean and PlacesFull.lean
  (Johnson/Desc/K12/Law/), also the next switch's (counted by hand from the written lists; no
  lemma). So a lemma on random values must speak of the addresses that are kept. That `sortedOf`
  reads these from different numbers of the `TestCoins`, within the counts, where the stages pass
  `StagesOk`, is stated in KeptSpec.lean (`Spec.src_reads`, `Spec.kept_perm`, `Spec.src_nodup`) and
  proved in KeptLaw2.lean. Nothing says that two numbers hold two values.
- Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Test
import Johnson.Desc.ProofFile.Honest.K12.Run

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes.Slice (GE ofE)
open Johnson.Prover.Link (PS)
open Fmt.M1.Own (PSt)

variable {W X : Type}

/-- **The random values of `testAll`, grouped by use.** i counts the stages from 1, so it means
entry i - 1 of the list. The hiding polynomial's coefficients have the numbers of
`Fmt.M1.Own.hideOf`: 0 for the constant, 2 l + t for variable l (from 1) at degree t. -/
def sortedOf (stages : List Fmt.M1.Stage) (C : TestCoins) : Sorted :=
  let s (i : ℕ) : Fmt.M1.Stage := stages.getD (i - 1) default
  let m (i : ℕ) : Marks := marksAt stages (i - 2)
  let c (n : ℕ) : Fmt.M1.E := ofE (C.rest n)
  let hide (i n : ℕ) : Fmt.M1.E := if i = 1 then ofE (C.hide n) else c ((m i).ride + n)
  { main := fun i b n => c ((m i).main + b * (s i).C.r + n)
    mask := fun i b n => c ((m i).mask + b * (s i).Z.r + n)
    hide := fun i n =>
      if n = 0 then hide i (2 * ((s i).k - 1))
      else if (n - 1) / 2 < (s i).k then
        hide i (2 * ((n - 1) / 2 - 1) + (n - 2 * ((n - 1) / 2) - 1))
      else hide i (2 * ((s i).k - 1) + (n - 2 * ((n - 1) / 2)))
    fresh := fun i b n =>
      if i = 1 then ofE (C.tails b n) else c ((m i).ride + (2 * (s i).k + 1) + b * (s i).Z.r + n)
    free := fun i n => c ((m i).free + n)
    pad := fun i => c ((m i).free + freeRoom (stages.getD (i - 2) default) (s i) - 1)
    word := fun i j n =>
      match j with
      | 0 => c ((m i).ride + (s i).C.r + n)
      | 1 => c ((m i).ride + (s i).C.r + (s i).C.l + n)
      | 2 => c ((m i).ride + n)
      | _ => c ((m i).ride + (s i).C.r + (s i).C.l + (s i).Z.l + n) }

/-- A first stage's state, tabulated. The fresh table's two fields stay empty: `runBy` fills them.
-/
def firstOf (s : Fmt.M1.Stage) (P : PS) : PSt :=
  { M := (List.range (2 ^ s.k)).map fun b =>
      (List.range s.C.l).map fun c => ofE (P.tabM (b + 2 ^ s.k * c))
    Rh := (List.range (2 ^ s.k)).map fun b => (List.range s.C.r).map fun q => ofE (P.tM b q)
    W := (List.range (2 ^ s.h)).map fun b =>
      (List.range s.Z.l).map fun c => ofE (P.tabZ (b + 2 ^ s.h * c))
    Sg := (List.range (2 ^ s.h)).map fun b => (List.range s.Z.r).map fun q => ofE (P.tZ b q)
    P := [], Pi := [] }

/-- **The input of `runBy` computed from a `TestJob`.** -/
def RunIn.ofTest (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) : RunIn :=
  { p := J.p, own := J.fresh.isNone, door := J.rec₀ w fr
    first := firstOf J.s₀ (J.rows₀ w fr C.mem)
    trees := fun _ => J.trees₀ w fr C.mem (J.first w fr C)
    coin := sortedOf J.p.nums.stages C }

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.sortedOf
#print axioms ProofFile.Honest.K12.Light.firstOf
#print axioms ProofFile.Honest.K12.Light.RunIn.ofTest
