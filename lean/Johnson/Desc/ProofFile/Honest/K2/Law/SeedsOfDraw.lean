-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/SeedsOfDraw.lean: the kind "the code switch" (K2): THE PREMISE
`seeds` OF `ExactAsks` AND `FreshAsks` (Honest/K2/Exact.lean, Fresh.lean), AT THE KIND's OWN FIRST
ROUND: a challenge that the round's entry can draw (`drawFit`, Honest/Frame.lean) holds seeds that
fit (`seedsFit`, Honest/K2/Exact.lean), its last clause too: no factor is 0. FIRST UNDER TWO PUBLIC
EQUATIONS ON THE PLACE's NUMBERS; THEN WITH THESE TWO PAID, AT NUMBERS THAT THE LIBRARY's MAKER
MADE, FROM THE FIRST ENTRY's TEST ON THE PLAN. Five statements with their proofs: calls; no
definition. NOTHING ON A ROUND OF SEEDS IS PROVED ANEW.

WHY `drawFit` BARS A FACTOR 0 THERE. It asks the format's own test `drawsMarkedNonzeroHaveNonzeroWords`
(Johnson/Desc/Block.lean): the drawn elements that the format marks as never 0 are not three words
0. Which these are follows from the round's kind, and the kind from the round's NAME (`Fmt.kindOf`,
Decl/Declared.lean). The kind's first round bears the name "SEND seed" (`First.K2.rounds`,
Johnson/Top/H0/Tw/K2C/Kind.lean), the one name of the kind "seeds"; there the format marks each
seed's factor (`Fmt.dsElems`, `Fmt.dsSeeds`, Fmt/Rules6Draws.lean).

  `seedsFit_of_drawFit` at ANY declared round of the kind "seeds" that draws seeds * (coordinates +
                    1) elements, seeds of them never 0: `drawFit` gives `seedsFit`
  `seeds_at_numbers` so at the kind's own two rounds at numbers q, in the very form of the field
                    `seeds`, under the two equations h₁, h₂
  `seeds_at_place` the same at `roundsAt` (Honest/K2/Rows.lean), the rounds that the kind's lot of
                    rows hands its simulator, where the place has numbers
  `seeds_of_rule` h₁ AND h₂ PAID: from the rule by which the library makes the two counts (nonZero
                    := samples; seeds := samples * (the greatest cube among the sampled messages +
                    1)) and the first entry's test on the plan (`planOk1`,
                    Johnson/Desc/Sending/Send.lean)
  `seeds_of_nums` and the rule paid too, at numbers n that the maker `numsAt`
                    (Johnson/Desc/ProofFile/Lot/K2OfPlan.lean) returned: at n's own codes and list

By, all sealed: the library's `zip_factors` (Johnson/Prover/Send/Factors.lean): the induction over
the seeds · ours, on the verifier's side, under Johnson/Desc/K2/Honest/Returns/: `dsElems_tied`
(DrawFits.lean) · `nonZero_of_entry` (DrawTies.lean) · `tie_of_rule` (DrawMade.lean) ·
`numsAt_draws` (DrawReached.lean). Kin, not called: `rounds_give` (DrawFits.lean) has the last
clause at the kind's own rounds from `roundsFit`, the test that `Block.step` runs, under the same
two equations: this file has it from `drawFit`, in the form that the two lists of premises ask ·
`cut_nz`, `seeds_nz` (Johnson/Desc/K14/Honest/YesRounds.lean): the induction a second time in the
library, and the clause at the shared sending's rounds · `seeds_of_six`
(Honest/K2/Law/MidAsks.lean): `seedsFit_of_drawFit` at one seed of five coordinates ·
`sendingPar_sent` (Honest/K2/Law/Counts.lean): a step of `seeds_of_rule`, made there by `simp` ·
`factorV_of_fits` (Johnson/Desc/First/Shape/SwitchLinkFactor.lean): the last clause on the
verifier's side, from `roundsFit` and two tests on a link, ending in a test. A CALLER:
`seeds_at_switch` (Honest/K2/Law/SeedsAtSwitch.lean) calls `seeds_at_numbers` at the two fields
`seedsNo` and `nonZeroNo` of the record at a switch, which are h₁ and h₂.

Limits. `seeds_of_nums` SPEAKS AT THE NUMBERS' OWN CODES AND LIST (n.codes, n.sent). THE FIELD
`seeds` SPEAKS AT THE PLACE's (p.sizes.codes, switchSent p.sizes p.others): THAT THESE ARE THE
NUMBERS' IS SHOWN NOWHERE HERE. Nor that the numbers q of `roundsAt` bear n's two counts, nor that
the entry's test says yes at a plan: three public facts, shown at no place of a plan here. WHERE
EACH OF THEM MIGHT BE HAD (this file uses none of it): the list and the codes: `place_nums`
(Honest/K2/Law/SentIsBlocks.lean), `place_codes` (Honest/K2/Law/PlaysAtPlan.lean) and the library's
`numsAt_codes` (Johnson/P1K2R/HstInScope.lean) · the two counts: the text by which the lot makes a
place's numbers out of n lays both in as they are (`p2With`,
Johnson/Desc/ProofFile/Lot/K2OfPlan.lean) · the entry's test: the library's `link_entry_reached`
(Johnson/AtFull/Shape/LinkLeftNums.lean) has it under the head, at the switches into groups 1 to 23,
at a state that is reached there. "Not 0" is said of the three machine words, as `seedsFit` says it
(`isZeroE`); that every word is below the prime is its second clause. Nothing on the other premises
of the two lists. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Rows
import Johnson.Desc.K2.Honest.Returns.DrawReached

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open OnBytes (OracleNotice)
open OnBytes.Params (cubeBitsOf)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First.K2 (P2 rounds par9)
open VerifiableInference.Desc.First.K2Caller (sampledOf)
open VerifiableInference.Desc.First.Send (planOk1)
open VerifiableInference.Desc.K2.Honest.Returns (dsElems_tied nonZero_of_entry tie_of_rule
  numsAt_draws)
open Johnson.Prover.Send (zip_factors)

/-- **AT A ROUND OF SEEDS A CHALLENGE THAT CAN BE DRAWN HOLDS SEEDS THAT FIT.** hk: the round's name
is of the kind "seeds". h₁, h₂: it draws and marks as many elements as the sending counts. -/
theorem seedsFit_of_drawFit {codes : OnBytes.Codes} {sent : Array OracleNotice}
    (d₁ : Fmt.DeclaredRound) (hk : Fmt.kindOf d₁.entry.name = some .seeds)
    (h₁ : d₁.entry.drawE =
      (sendingPar codes sent).seeds * ((sendingPar codes sent).coordinates + 1))
    (h₂ : d₁.entry.drawNZ = (sendingPar codes sent).seeds) (d : Fmt.Drawn)
    (hd : drawFit d₁ d = true) : seedsFit codes sent d.elems := by
  simp only [drawFit, Bool.and_eq_true] at hd
  obtain ⟨⟨⟨⟨⟨⟨⟨hl, -⟩, -⟩, -⟩, -⟩, hz⟩, hw⟩, -⟩ := hd
  have hl' : d.elems.length =
      (sendingPar codes sent).seeds * ((sendingPar codes sent).coordinates + 1) := by
    simpa [h₁] using hl
  refine ⟨hl', ?_, ?_⟩
  · intro t ht
    have h₃ := List.all_eq_true.1 hw t ht
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h₃
    exact ⟨h₃.1.1, h₃.1.2, h₃.2⟩
  · by_cases h0 : (sendingPar codes sent).seeds = 0
    · intro s hs
      rw [h0] at hs
      cases hs
    · unfold VerifiableInference.Desc.drawsMarkedNonzeroHaveNonzeroWords at hz
      rw [hk, Option.any_some, dsElems_tied _ (sendingPar codes sent) h0 h₁ h₂] at hz
      exact zip_factors _ _ d.elems hl' hz

/-- **AT THE KIND's OWN ROUNDS**, in the form of the field `seeds`. -/
theorem seeds_at_numbers (q : P2) {codes : OnBytes.Codes} {sent : Array OracleNotice}
    (h₁ : q.seeds = (sendingPar codes sent).seeds * ((sendingPar codes sent).coordinates + 1))
    (h₂ : q.nonZero = (sendingPar codes sent).seeds) :
    ∀ r ∈ ((rounds q).zip [q.sent, []]).head?, ∀ d : Fmt.Drawn,
      drawFit r.1 d = true → seedsFit codes sent d.elems := by
  intro r hr d hd
  obtain rfl : ((rounds q).headD default, q.sent) = r := by
    simpa [rounds] using hr
  refine seedsFit_of_drawFit _ ?_ h₁ h₂ d hd
  show Fmt.kindOf "SEND seed" = some .seeds
  decide

/-- **AT THE ROUNDS THAT THE LOT OF ROWS HANDS ITS SIMULATOR.** -/
theorem seeds_at_place (Z : Pub) (G : Ground) (a : Place) {q : P2} (hq : numbersAt Z G a = some q)
    {codes : OnBytes.Codes} {sent : Array OracleNotice}
    (h₁ : q.seeds = (sendingPar codes sent).seeds * ((sendingPar codes sent).coordinates + 1))
    (h₂ : q.nonZero = (sendingPar codes sent).seeds) :
    ∀ r ∈ (roundsAt Z G a).head?, ∀ d : Fmt.Drawn,
      drawFit r.1 d = true → seedsFit codes sent d.elems := by
  unfold roundsAt
  rw [hq]
  exact seeds_at_numbers q h₁ h₂

/-- **THE TWO EQUATIONS PAID**: from the makers' rule for the two counts and the first entry's test
on the plan. -/
theorem seeds_of_rule (q : P2) {codes : OnBytes.Codes} {sent : Array OracleNotice} (samples : Nat)
    (hN : q.nonZero = samples)
    (hS : q.seeds = samples *
      ((sampledOf sent.toList).foldl (fun c n => max c (cubeBitsOf codes n.shape)) 0 + 1))
    (he : planOk1 none sent (par9 q).eSeed = true) :
    ∀ r ∈ ((rounds q).zip [q.sent, []]).head?, ∀ d : Fmt.Drawn,
      drawFit r.1 d = true → seedsFit codes sent d.elems := by
  have hs : (sendingPar codes sent).sent = sent := by
    simp [sendingPar, VerifiableInference.Desc.K1.Par.sent]
  refine seeds_at_numbers q (tie_of_rule q (sendingPar codes sent) samples hN ?_ ?_)
    (nonZero_of_entry q (sendingPar codes sent) sent hs he)
  · rw [hs]
    exact hS
  · rw [hs]
    exact he

/-- **AT NUMBERS THAT THE LIBRARY's MAKER RETURNED**: at their own codes and list. -/
theorem seeds_of_nums {Pp : P1K2.Prep} {link : Option Nat} {n : P1K2.Nums}
    (hn : P1K2.numsAt Pp link = some n) (q : P2) (hs : q.seeds = n.seeds)
    (hz : q.nonZero = n.nonZero) (he : planOk1 none n.sent (par9 q).eSeed = true) :
    ∀ r ∈ ((rounds q).zip [q.sent, []]).head?, ∀ d : Fmt.Drawn,
      drawFit r.1 d = true → seedsFit n.codes n.sent d.elems :=
  seeds_of_rule q Pp.z.set.samples (hz.trans (numsAt_draws hn).1) (hs.trans (numsAt_draws hn).2) he

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.seedsFit_of_drawFit
#print axioms ProofFile.Honest.K2.Law.seeds_at_numbers
#print axioms ProofFile.Honest.K2.Law.seeds_at_place
#print axioms ProofFile.Honest.K2.Law.seeds_of_rule
#print axioms ProofFile.Honest.K2.Law.seeds_of_nums
