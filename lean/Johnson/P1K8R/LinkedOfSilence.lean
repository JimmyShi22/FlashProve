-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/LinkedOfSilence.lean: THE TEST `linkedK6T` ON THE CHALLENGES OF THE SUB-PROTOCOL "THE
OUTPUT HEAD's OWN ROUNDS" (Johnson/Desc/ProofFile/Honest/K6/LinkedTest.lean), WHERE IT NAMES NO
FAILING CLAUSE: NO COORDINATE OF THE THREE POINTS THAT IT READS IS 0 OR 1 IN THE FIELD. On plain
data: no block, no state, no prover. Lemmas; NONE OF THE LIBRARY's GOALS. Nothing on completeness,
soundness or hiding.

  `notBit_fine`   `val_ne_of_word` (Johnson/Desc/K8/Honest/ReadsLiveOf.lean), `val_ne_one`
      (Johnson/P1K8R/PlanesOfSilence.lean)
  `all_of_says`, `drawsOk_of_rounds`   by the definitions
  `sumR_ok`   elemOf_ok (Johnson/Desc/ProofFile/Honest/K6/GoodLaw/Tie.lean)
  **`linked_fine`**   headClausesOn_all (Johnson/Desc/ProofFile/Honest/K6/GoodRounds.lean)
Kin: that kind's authors' linkedT_of_silent, linkedT_of_silent_fit, linkedK6T_iff, linkedBad_field
(Johnson/Desc/ProofFile/Honest/K6/LinkedMark.lean): the mark's silence gives the test's yes and, at
challenges that fit, words below the prime; the test round by round; from the words 0 and 1 to the
field's 0 and 1 at one element. NOT CALLED: that file stands over two more that do not lie with us;
`all_of_says` is a second text of a lemma of theirs that it calls (headFirstNo_isSome). Their rd_ne
(GoodLaw/Tie.lean) is `val_ne_of_word` at their own reading. Their drawsOk_of_canonical
(GoodLaw/Runs.lean) is `drawsOk_of_rounds`' NEAR TWIN: from their own sentence on rounds
(Head.Law.Canonical) where this is from the library's test `okRoundsE`; that file does not lie
beneath this one. Here: from the test's silence to "reads neither 0 nor 1" at each coordinate of the
three points as arrays.
Limits. As that test's own file says: NO THEOREM TIES THE TEST TO THE VERIFIER's `selfLinked`; nor
does this file. That the words are below the prime and that the test names no clause are premises.
Nothing on any measure. It stands over files of the kind "the output head's own rounds" on the
honest side.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.DigitsOfSilence
import Johnson.Desc.ProofFile.Honest.K6.LinkedTest
import Johnson.Desc.ProofFile.Honest.K6.GoodRounds
import Johnson.Desc.ProofFile.Honest.K6.GoodLaw.Tie
import Johnson.Top.H.Keep.CEndPoint
import Johnson.Top.H.K3LawKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.Kinds (Head.Par)
open VerifiableInference.OnPublicFiles (okRoundsE)
open ProofFile.Honest.K6 (headNotBit headFirstNo elemOf elemsOf headSumR headLt headLs headLPd
  linkedK6TSays linkedK6TClauses headClausesOn_all)
open ProofFile.Honest.K6.GoodLaw (drawsOk elemOf_ok)

/-- A word below the prime that is neither the word 0 nor the word 1 reads neither 0 nor 1. -/
theorem notBit_fine (w : E) (hok : OnBytes.okE w = true) (hb : headNotBit w = true) : Fine w := by
  unfold headNotBit at hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne] at hb
  exact ⟨val_ne_of_word w hok hb.1, val_ne_one w hok hb.2⟩

/-- Where no clause is named as failing, all hold. -/
theorem all_of_says (l : List (String × Bool)) (h : headFirstNo l = none) :
    l.all (·.2) = true := by
  unfold headFirstNo at h
  rw [Option.map_eq_none_iff, List.find?_eq_none] at h
  refine List.all_eq_true.2 fun c hc => ?_
  have k := h c hc
  simpa using k

/-- A sumcheck's variables' challenges, where every sampled word is below the prime. -/
theorem sumR_ok (p : Head.Par) (i n : Nat) (own : List Fmt.Drawn) (hok : drawsOk own = true) :
    ∀ w ∈ (headSumR p i n own).toList, OnBytes.okE w = true := by
  intro w hw
  unfold headSumR at hw
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hw
  exact elemOf_ok own hok _

/-- **WHERE THE TEST `linkedK6T` (Johnson/Desc/ProofFile/Honest/K6/LinkedTest.lean) NAMES NO FAILING
CLAUSE AT CHALLENGES WHOSE WORDS ARE BELOW THE PRIME: NO COORDINATE OF ITS THREE POINTS READS 0 OR
1**: the last ls + lt challenges of the sumcheck on the squares; the first lt of the head's own; the
lt of the one on the products. -/
theorem linked_fine (p : Head.Par) (own : List Fmt.Drawn) (hok : drawsOk own = true)
    (hs : linkedK6TSays p own = none) :
    (∀ w ∈ ((headSumR p 2 (headLPd p + headLt p) own).extract (headLPd p - headLs p)
      (headLPd p + headLt p)).toList, Fine w) ∧
    (∀ w ∈ (headSumR p 7 (headLt p) own).toList, Fine w) ∧
    ∀ w ∈ (headSumR p 5 (headLt p) own).toList, Fine w := by
  have ha := all_of_says _ hs
  unfold linkedK6TClauses at ha
  simp only [List.all_append, Bool.and_eq_true, headClausesOn_all] at ha
  obtain ⟨⟨a2, a7⟩, a5⟩ := ha
  refine ⟨fun w hw => ?_, fun w hw => ?_, fun w hw => ?_⟩
  · exact notBit_fine w (sumR_ok p 2 _ own hok w (Fo.Tp.mem_extract hw))
      (List.all_eq_true.1 a2 w hw)
  · exact notBit_fine w (sumR_ok p 7 _ own hok w hw) (List.all_eq_true.1 a7 w hw)
  · exact notBit_fine w (sumR_ok p 5 _ own hok w hw) (List.all_eq_true.1 a5 w hw)

/-- The library's test on rounds' words gives that kind's test on what the rounds show. -/
theorem drawsOk_of_rounds (R : List Fmt.RoundView) (h : okRoundsE R = true) :
    drawsOk (R.map (·.drawn)) = true := by
  unfold drawsOk
  refine List.all_eq_true.2 fun d hd => ?_
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hd
  unfold okRoundsE at h
  have k := List.all_eq_true.1 h r hr
  rw [Bool.and_eq_true] at k
  unfold ProofFile.Honest.K6.elemsOf
  rw [List.all_map]
  exact k.2

end P1K8

#print axioms P1K8.notBit_fine
#print axioms P1K8.all_of_says
#print axioms P1K8.sumR_ok
#print axioms P1K8.linked_fine
#print axioms P1K8.drawsOk_of_rounds
