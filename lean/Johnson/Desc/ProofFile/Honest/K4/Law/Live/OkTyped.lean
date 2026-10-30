-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/Live/OkTyped.lean: CONDITIONAL.

What is here. WHO GIVES THE HYPOTHESIS hok OF `k4_tapeLive` (Law/Live/TapeOfMark.lean): that the
three words of a round's one drawn element lie below the prime. THREE DOORS, EACH A CALL OF A LAW OF
THE LIBRARY, AND A CARRIER; EACH OF THE FOUR ENDS IN hok TO ITS LETTER; nothing of K4 (the
sub-protocol of the feed-forward layers' own rounds) is in them.
(1) `k4_hok_of_words`: from the words themselves: each of the three words of every drawn element is
below `fieldPrimeWord` (Johnson/Desc/Block.lean): the form in which the description's own tests have it. By
the library's `ok_of_lt` (Johnson/Top/H0/MergeLaw/Beta.lean). (2) `k4_hok_of_okView`: from the
description's test on a view's words (`viewWordsBelowPrime`), at rounds that are among that view's. By the
library's `words_of_okViewW` (the same file). (3) `k4_hok_of_view`: at rounds that are among those
of the view of a written transcript, at the library's challenge kit at the release's field (`ckP
.two`, Run/PlanPull.lean). By the library's `rvT_okE` (Johnson/Desc/First/Att/K05SeamOut.lean),
which holds of a plain draw and of a draw by the rule that never gives 0 alike, in a round of one
element and in a round of many. (4) the carrier, `k4_hok_noDigest`: from the rounds as they are
handed to the rounds without the sealed digest, which a block is shown (by unfolding: the digest is
no element): `k4_nz_of_step` (Law/Live/NzOfStep.lean) asks hok at the first, `k4_tapeLive` at the
second. It imports two files of the library, those named in (1) and (3), and no other. Statements
with their proofs.

  `k4_hok_of_words`   **hok, from words below `fieldPrimeWord`.**
  `k4_hok_of_okView`   hok, from the description's test on a view's words.
  `k4_hok_of_view`   hok, at the rounds of the view of a written transcript.
  `k4_hok_noDigest`   hok at the rounds gives hok at the rounds without the sealed digest.

Not shown here. THAT THE ROUNDS WHICH THE FRAME HANDS K4's MEMBER IN A RUN MEET ONE OF THE THREE
PREMISES (hw · h with hrs · hrs): NOT TYPED HERE; its writers have found no file of the library that
types it (sought by the names words_of_… | …_words and by ends «okE … = true» under
Johnson/Desc/ProofFile/Honest, Johnson/Desc/First/Att, Johnson/Top/H0 and Johnson/P1K8R; not
beyond). The nearest found: `stepYes_words` (Johnson/P1K8R/StepOut.lean): at an accepting step of a
block under `below`, in the verifier's walk, the words of the step's own rounds lie below the prime:
a yes of that walk is its premise; Honest/K9/K4TextsHanded.lean is said by its own writers to give
hw at the rounds of K4's own step, from the silence of the mark on the fit (`fit_at_silent`) and a
lemma `words_of_drawsFit`: not read here. WHERE THE ROOTS LIE, by reading of the frame's files (Lean
has not checked it): for (1): the frame's test on challenges (`Draws.due`, `drawFit`:
Honest/Frame.lean) asks of every round, among its clauses, these very words and `drawsMarkedNonzeroHaveNonzeroWords`; «at every
list of challenges» means there: at every list that passes it · for (2): `run_words`
(Honest/Law/Run.lean) has `viewWordsBelowPrime` at a run's views with no yes of the verifier, under that test on
the challenges, at a run with nothing to fall back on alone · for (3): `views_of_stratC`
(Honest/Law/StratRunC.lean). The cuts from a run's whole list to K4's member's own rounds are not
typed; where a sub-protocol's own side is proved none is needed: `Good.plays` and `Good.acc`
(Honest/Side.lean) take `drawsFit` at the member's own declared rounds as a premise. At a typed
challenge the library has the general law on what is shown (`H2K.Fit.fitsDrawn`,
Johnson/Desc/K12/Law/FitWritten.lean; `collect_okE`, K05SeamOut.lean): not called here. In other
letters, `okE (E.ofTriple x)`, the library's `words_of_fit` (Honest/K6/Law/OutAtRow.lean) has the
words of every drawn element below the prime wherever `drawsFit` accepts; so has `draws_small`
(Law/OkAtStand.lean): neither is called here. Nothing on how the challenges are distributed.
No property is claimed.
-/
import Johnson.Desc.First.Att.K05SeamOut
import Johnson.Top.H0.MergeLaw.Beta

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4.Live
open _root_.Run (ckP)
open OnBytes.Maker (RDT rvT uLT)
open VerifiableInference.Desc (noDigest viewWordsBelowPrime fieldPrimeWord)
open VerifiableInference.Desc.First.Att.P (rvT_okE)
open VerifiableInference.Desc.First.MergeLaw (ok_of_lt words_of_okViewW)

/-- CONDITIONAL: on hw. **THE HYPOTHESIS hok OF `k4_tapeLive`, TO ITS LETTER, FROM WORDS BELOW
`fieldPrimeWord`.** -/
theorem k4_hok_of_words (rs : List Fmt.RoundView)
    (hw : ∀ r ∈ rs, ∀ x ∈ r.drawn.elems, x.1 < fieldPrimeWord ∧ x.2.1 < fieldPrimeWord ∧ x.2.2 < fieldPrimeWord) :
    ∀ r ∈ rs, ∀ t, r.drawn.elems = [t] → Fmt.Fld.two.okE t = true := by
  intro r hr t ht
  obtain ⟨h1, h2, h3⟩ := hw r hr t (by rw [ht]; exact List.mem_singleton.2 rfl)
  simp [Fmt.Fld.okE, ok_of_lt h1, ok_of_lt h2, ok_of_lt h3]

/-- CONDITIONAL: on h and hrs. The hypothesis hok of `k4_tapeLive`, to its letter, at rounds that
are among those of a view which passes the description's test on words. -/
theorem k4_hok_of_okView {v : Fmt.View} (h : viewWordsBelowPrime v = true) (rs : List Fmt.RoundView)
    (hrs : ∀ r ∈ rs, r ∈ v.rounds) :
    ∀ r ∈ rs, ∀ t, r.drawn.elems = [t] → Fmt.Fld.two.okE t = true :=
  k4_hok_of_words rs fun r hr => words_of_okViewW h r (hrs r hr)

/-- CONDITIONAL: on hrs. The hypothesis hok of `k4_tapeLive`, to its letter, at rounds that are
among those of the view of a written transcript, at the kit `ckP .two`. -/
theorem k4_hok_of_view (ds : List RDT) (τ : Iop.Tr (uLT (ckP .two) ds)) (rs : List Fmt.RoundView)
    (hrs : ∀ r ∈ rs, r ∈ rvT (ckP .two) ds τ) :
    ∀ r ∈ rs, ∀ t, r.drawn.elems = [t] → Fmt.Fld.two.okE t = true := by
  intro r hr t ht
  exact rvT_okE ds τ r (hrs r hr) t (by rw [ht]; exact List.mem_singleton.2 rfl)

/-- CONDITIONAL: on h. hok at the rounds gives hok at the rounds without the sealed digest. -/
theorem k4_hok_noDigest (mine : List Fmt.RoundView)
    (h : ∀ r ∈ mine, ∀ t, r.drawn.elems = [t] → Fmt.Fld.two.okE t = true) :
    ∀ r ∈ mine.map noDigest, ∀ t, r.drawn.elems = [t] → Fmt.Fld.two.okE t = true := by
  intro r hr t ht
  obtain ⟨r0, hr0, rfl⟩ := List.mem_map.1 hr
  exact h r0 hr0 t ht

end ProofFile.Honest.K4.Live

#print axioms ProofFile.Honest.K4.Live.k4_hok_of_words
#print axioms ProofFile.Honest.K4.Live.k4_hok_of_okView
#print axioms ProofFile.Honest.K4.Live.k4_hok_of_view
#print axioms ProofFile.Honest.K4.Live.k4_hok_noDigest
