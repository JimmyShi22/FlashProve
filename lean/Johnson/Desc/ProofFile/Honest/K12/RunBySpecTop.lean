-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/RunBySpecTop.lean: the main statement `Spec.runBy_eq`, and three
lemmas that need Test.lean or RunOf.lean, each stated as a named `Prop`. Their proofs: RunByEq.lean
and RunByTies.lean. The hypothesis `StagesOk`: RunBy.lean. The relations and the other lemmas:
RunBySpec.lean.

  `Spec.runBy_eq`   for every job, prover's input, random values and sampled challenges: if the
                 stages pass `StagesOk`, the rounds, the trees (as functions on all positions) and
                 the opened columns of `runBy` at `Seams.lib` and at the input `RunIn.ofTest`
                 (RunOf.lean) are those of `testAll` (Test.lean)
  `Spec.own_col`, `Spec.ties_of`, `Spec.first_tab`   the three lemmas

Limits. Statements only. The warnings (`RunOut.no`) are not covered. At `RunIn.ofTest` the trees
that hold the first stage's rows are the job's own `trees₀`, the term that `testAll` uses too: so
for the columns opened at the first switch `Spec.runBy_eq` compares a term with itself. Nothing on
completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.RunOf
import Johnson.Desc.ProofFile.Honest.K12.RunBySpec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open Johnson.Prover.Link (PS)
open Fmt.M1 (Stage)
open Fmt.M1.Own (PSt syms words)
open H2K.Pub (sgOf)

/-- Where the stages pass `StagesOk`, `runBy` at `Seams.lib` and `RunIn.ofTest` gives the rounds,
trees and opened columns of `testAll`. The warnings are left out. -/
def Spec.runBy_eq : Prop :=
  ∀ (W X : Type) (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn),
    StagesOk J.p.nums.stages = true →
    (runBy Seams.lib (RunIn.ofTest J w fr C) D).toB = testAll J w fr C D

/-- If `Tab` holds, the column of a fresh table that has a tree to itself is the same words whether
computed on words (`syms`) or over the field (`freshCol`). -/
def Spec.own_col : Prop :=
  ∀ (s : Stage) (P : PS) (p : PSt), Tab s false P p →
    (fun x => (syms s.Z (Fmt.M1.cp s.Z x) p.P p.Pi).flatMap words) = freshCol (sgOf s) P

/-- If the stages pass `okFrom`, `sortedOf` and `coinsOf` give the same random values: `CoinTies`
from the first stage on, and `HideTie` at the first stage. -/
def Spec.ties_of : Prop :=
  ∀ (s : Stage) (rest : List Stage) (C : TestCoins), okFrom s rest = true →
    CoinTies (sortedOf (s :: rest) C) (coinsOf (s :: rest) C.hide C.rest) 0 s rest ∧
      (rest ≠ [] → HideTie (sortedOf (s :: rest) C) (coinsOf (s :: rest) C.hide C.rest) 0 s)

/-- If the stages pass `okFrom` and there are at least two, `Tab` holds at the first stage, between
`TestJob.first` and the lists that `runBy` starts from at `RunIn.ofTest`. -/
def Spec.first_tab : Prop :=
  ∀ (W X : Type) (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (s : Stage)
    (rest : List Stage), J.p.nums.stages = s :: rest → rest ≠ [] → okFrom s rest = true →
    Tab s false (J.first w fr C)
      { firstOf s (J.rows₀ w fr C.mem) with
        P := (ridersBy .two (sortedOf (s :: rest) C) 1 s false).1
        Pi := (ridersBy .two (sortedOf (s :: rest) C) 1 s false).2 }

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.Spec.runBy_eq
#print axioms ProofFile.Honest.K12.Light.Spec.own_col
#print axioms ProofFile.Honest.K12.Light.Spec.ties_of
#print axioms ProofFile.Honest.K12.Light.Spec.first_tab
