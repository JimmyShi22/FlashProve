-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K11/Mark/Statement.lean: A MARK AT THE MERGE OF THE CLAIMS ON THE
WEIGHTS: "THE FACTOR OF THE SUMMAND, OR THE CHALLENGE OF A ROUND IN A COLUMN BIT, IS 0": three
definitions with code, and STATEMENTS: two, each a definition of a proposition. NOTHING IS PROVED IN
THIS FILE, and neither is one of the library's goals: they are lemmas' statements.

Why. The verifier refuses nothing at these rounds. The event is counted all the same: a count at the
batching behind the head's link wants that the merge's one claim bears, on each slot that it alone
names, a coefficient other than 0; these coefficients are products of the lk + 1 elements that the
merge's rounds number 1 to lk + 1 draw, and of the challenge of the round in the further variable
(Johnson/Desc/K11/Live/RunStatement.lean), whose entry declares that it is drawn by the rule that
never gives 0 (`mergeEntries`, Johnson/Desc/First/Fork/MergeKind.lean): that one is not listed. A
mark (`Mark`, Honest/Law/Marks.lean) is a place, a test on challenges alone, and a stated share.

  `mergeBad dr`            the test at one round's drawn value: it holds not just one field element;
                           or that element's words are not below the prime; or it is 0
  `mergeListed lk`         the numbers of the listed rounds: 1 to lk + 1
  `headMergeMark P`        the mark: the kind's place · "some listed round's drawn value is bad", on
                           the member's own challenges alone · the share
                           2 (lk + 1) (2 ^ 128 + 1) ^ 3 of p ^ 3 (2 ^ 128) ^ 3, p the prime: A
                           STATED NUMBER
  `HeadMergeMarkDebt`      ds: the data of the member's rounds. Where each listed round of ds draws
                           one field element and nothing else, and its entry's positions have at
                           most 64 bits: the sentence that is owed for a mark (`MarkDebt`,
                           Honest/Law/CoverJoin.lean), at strings of hash blocks, at whatever is
                           handed of the challenges in front, at the stated share's value
  `HeadMergeMarkSilent`    where the mark says nothing at the rounds' drawn values, and every
                           element that a round from number lk + 2 on has drawn reads other than 0:
                           every element of `laterDraws rs`
                           (Johnson/Desc/K11/Live/BehindStatement.lean) reads other than 0

Limits. That ds is the data of the description's rounds is not said. The share has a factor 2 to
spare: the law that is called counts "0 or 1". The uniform law on the rounds' messages is named, not
derived. That the challenge of the round in the further variable reads other than 0 is a premise
here. No number is evaluated. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Part
import Johnson.Desc.K11.Live.BehindStatement
import Johnson.P1K8R.MarkRounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes (E)
open OnBytes.Maker (RDT)
open OnBytes.Model (Reading)
open VerifiableInference.Desc.K9H (notZero)
open VerifiableInference.Desc.First.K8.Honest (OneElem)
open Johnson.Desc.First.ForkMerge (HeadMergeP)
open Johnson.Desc.First.ForkMerge.Live (laterDraws)

/-- **The test at one round's drawn value.** -/
def mergeBad (dr : Fmt.Drawn) : Bool :=
  match dr.elems with
  | [t] => !notZero (E.ofTriple t)
  | _ => true

/-- **The listed rounds.** -/
def mergeListed (lk : Nat) : List Nat := List.range' 1 (lk + 1)

/-- **The mark.** -/
def headMergeMark (P : HeadMergeP) : Mark :=
  { place := headMergePlace P
    test := fun _ own =>
      if P1K8.anyBad mergeBad (fun i => decide (i ∈ mergeListed P.lay.lk)) 0 own then
        some "the merge: the summand's factor or a round's challenge is 0"
      else none
    share := ⟨2 * (mergeListed P.lay.lk).length * (2 ^ 128 + 1) ^ 3,
      _root_.Code.pGold ^ 3 * (2 ^ 128) ^ 3⟩ }

/-- The statement of the mark's sentence. Not proved here; a lemma's statement, none of the
library's goals. -/
def HeadMergeMarkDebt : Prop :=
  ∀ (P : HeadMergeP) (ds : List RDT) (Q : List Fmt.Drawn → Prop),
    (∀ i d, ds[i]? = some d → i ∈ mergeListed P.lay.lk →
      OneElem d.entry d.kind ∧ d.entry.logN ≤ 64) →
    MarkDebt (_root_.Run.ckP .two) (headMergeMark P) ds Q (headMergeMark P).share.val

/-- The statement where the mark says nothing. Not proved here; a lemma's statement, none of the
library's goals. -/
def HeadMergeMarkSilent : Prop :=
  ∀ (P : HeadMergeP) (fr : List Fmt.Drawn) (rs : List Fmt.RoundView),
    (headMergeMark P).test fr (rs.map (·.drawn)) = none →
    (∀ i r, rs[i]? = some r → P.lay.lk + 2 ≤ i →
      ∀ e ∈ r.drawn.elems.map E.ofTriple, Reading.gl.val e ≠ 0) →
    ∀ e ∈ laterDraws rs, Reading.gl.val e ≠ 0

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.mergeBad
#print axioms ProofFile.Honest.K11.mergeListed
#print axioms ProofFile.Honest.K11.headMergeMark
#print axioms ProofFile.Honest.K11.HeadMergeMarkDebt
#print axioms ProofFile.Honest.K11.HeadMergeMarkSilent
