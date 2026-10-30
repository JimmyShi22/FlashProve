-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Loose/H2K12/LastTypedOfLaid.lean:
THE NAMED CONDITION LastTypedAt (K12LawR.lean)
FROM THE VERIFIER's OWN ENTRY TESTS: in the goals' scope, where the proof file's value is laid
behind the list of fourteen entry tests, the sized stages of the first chain's last proximity test
are the typed list. An assembly of other files' lemmas: NO DEFINITION, NO NEW MATHEMATICS.

WHAT IT IS NOT, FIRST.
(1) IT IS TRUE OVER THE VERIFIER's ENTRY TESTS, A LIST OF FOURTEEN ROWS, AND OVER THAT LIST ALONE:
the condition comes of the yes of its ninth row, madeRow (THE ROAD, below). LPFD.lawsAsk,
LPFD.Full.proofDataAndDecisionOfPublicFiles and FlashProve.protocolDataWellFormed are names whose meaning turns with that list: whoever calls
a theorem of this file stands over that list too.
(2) NO EXAMPLE BY A THEOREM OF THIS FILE. By evaluations, not shown here, the first thirteen rows
accept at five sets of public files in scope; of the fourteenth row this file holds no word.
OF protocolDataWellFormed (the third theorem's premise: it also asks the list of rounds' and
the key file's values and a test on the three together) OVER THE FOURTEEN-ROW LIST K12's FILES HOLD
NO EVALUATION.
(3) In scope only. At files outside the goals' scope nothing is said.
(4) The typed list and the written sizes were laid by two programs from prints of one planner (the
program that makes the lists of rounds): their agreement (last_written) is no second witness.
No soundness of a verifier is claimed. Nothing on hiding.

IS THE CONCLUSION HAD FOR NOTHING? LastTypedAt says "at every value that ProofFile.pubPlain returns ...".
Where the proof file's value is laid, pubPlain does return (the first lemma's second witness), so
the condition speaks of a value.

THE ROAD, AND WHERE EACH STEP LIES.
  laid, in scope => the row madeRow accepts at what ProofFile.pureRoad.pub returns:
    LPFD.Full.laidPOf_pins_scope (Johnson/Goal/Numbers/LaidPinsInScope.lean).
    pureRoad.pub is pubPlain by the structure's field.
  the row's yes => the law form's yes => the yes of the test on the sizes: pinnedAt_of_row,
    sized_of_made (Johnson/Desc/Ok/PlanWritten/MadeTestLaws.lean).
  that yes, in scope => what the planner sized for a proof file is the written value, whole:
    sized_in_scope (Johnson/Goal/Numbers/KeyInScope.lean).
  the written value's last test has the typed stages: H2K.Sizes.last_written
    (Johnson/Desc/K12/Law/Sizes/WrittenIsTyped.lean): by Lean's kernel.
  protocolDataWellFormed's yes => the proof file's value is laid at the format's second hash function:
    FlashProve.theLive_made (Johnson/Goal/Description/Live.lean).

  last_of_madeRow      in scope, at what pubPlain returns, from the row's yes: the equation.
  lastTypedAt_of_laid  * in scope, from proofDataAndDecisionOfPublicFiles's return, at every function in the second hash
                       function's place: LastTypedAt. pubPlain is one function with one return: the
                       value of the condition and the value at which the row accepts are one.
  lastTypedAt_of_live  * the same at the verifier's own gate: from InScope Z and
                       protocolDataWellFormed (asDescriptionFiles Z).

-/
import Johnson.Loose.H2K12.K12LawR
import Johnson.Goal.Numbers.LaidPinsInScope
import Johnson.Desc.Ok.PlanWritten.MadeTestLaws
import Johnson.Desc.K12.Law.Sizes.WrittenIsTyped
import Johnson.Goal.Description.Live

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12

/-- In scope, at what `pubPlain` returns, where the row `madeRow` accepts: the sized stages of the
first chain's last proximity test are the typed list. -/
theorem last_of_madeRow {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {Zp : ProofFile.Pub}
    (hs : VerifierAndGoals.InScope Z = true) (hZ : ProofFile.pubPlain o Z.pol Z.lay Z.KL = .ok Zp)
    (h : VerifiableInference.PlanWritten.madeRow Zp = true) :
    Zp.made.p.chains.made.sized.proof.last.stages = H2K.Member.szLFull := by
  have e : Zp.p.chains.made.sized.proof = VerifiableInference.PlanWritten.proofSizedFull :=
    VerifiableInference.PlanWritten.sized_in_scope hs
      (show ProofFile.pureRoad.pub o Z.pol Z.lay Z.KL = .ok Zp from hZ)
      (VerifiableInference.PlanWritten.sized_of_made
        (VerifiableInference.PlanWritten.pinnedAt_of_row (by rw [h, Bool.or_true])))
  show Zp.p.chains.made.sized.proof.last.stages = H2K.Member.szLFull
  rw [e]
  exact H2K.Sizes.last_written

/-- **In scope, where the proof file's value is laid behind the fourteen entry tests, the named
condition holds.** NO EXAMPLE BY A THEOREM OF THIS FILE. -/
theorem lastTypedAt_of_laid {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} (hs : VerifierAndGoals.InScope Z = true)
    (h : LPFD.Full.proofDataAndDecisionOfPublicFiles o Z.pol Z.lay Z.KL = .ok (D, r)) :
    LastTypedAt o Z.pol Z.lay Z.KL := by
  obtain ⟨_, Z₀, _, hZ₀, hm, _⟩ := LPFD.Full.laidPOf_pins_scope hs h
  intro Zp hZp
  obtain rfl : Zp = Z₀ := Except.ok.inj (hZp.symm.trans hZ₀)
  exact last_of_madeRow hs hZp hm

/-- **The same at the verifier's own gate.** NO EXAMPLE BY A THEOREM OF THIS FILE; of
`protocolDataWellFormed` over the fourteen entry tests K12's files hold no evaluation. -/
theorem lastTypedAt_of_live (Z : VerifierAndGoals.PublicFiles) (hs : VerifierAndGoals.InScope Z = true)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) :
    LastTypedAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL := by
  obtain ⟨_, P, _, _, hP, _⟩ := FlashProve.theLive_made (VerifierAndGoals.asDescriptionFiles Z) hl
  exact lastTypedAt_of_laid (D := P.1) (r := P.2) hs hP

end H2K12

#print axioms H2K12.last_of_madeRow
#print axioms H2K12.lastTypedAt_of_laid
#print axioms H2K12.lastTypedAt_of_live
