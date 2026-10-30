-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/ExactSend.lean: kind K14: THE FIELD exact OF THE FRAME's RECORD
Good (Honest/Side.lean) AT THE PARTS OF THE TWO SENDINGS OF THE BATCH's SHARED ROUNDS: the four
statements of Honest/K14/ExactStated.lean, and the averaging line, AS THEOREMS. Each is one call:
the implication of Honest/K14/ExactOfRows.lean at the shared sending's law at the rows (rowsExact,
Johnson/SendSim/At/RowsExact.lean).

  shownOneLaw     at fixed challenges and fixed positions within the count, what a sending's part
                  shows, over its own coins, has one distribution at any two stands at which the
                  job's vectors are the same in both rounds
  exactAtSending, exactAtU, exactAtOmega   the field exact beside sendingSim: general in the job; at
                  "send o_u"; at "send o_omega"
  shownAveraged   the stand sampled first, by any distribution, then the part's coins: what the part
                  shows does not hang on the stand: at a job whose shapes pass the test, a
                  sub-protocol that declares the part's messages, challenges that the two rounds can
                  sample and positions within the count, SameData at every cause

WHAT IS LEFT, WITH EVERY ONE OF THEM. What a part shows is not all that a run shows of its messages:
the proximity tests behind the sendings, and of o_omega each request's own test, are handed these
messages' coins; nothing is said here of what they show; at as many distinct positions modulo the
main code's length as a carrier's tail has entries, what the part shows, columns and answers
together, fixes the carrier's coins, given the data: nothing of them is left to cover what the parts
behind show (reckoned by hand; no Lean statement says so) · the simulator's rows meet none of the
later constraints on these messages (Honest/K14/ExactDefs.lean) · not to be quoted without the
owner's sentence (the field fresh) at both sendings · the challenges and the positions are fixed
before the coins are sampled · that the sentence at entry holds where a run stands, and that a run's
positions are within the count, is not shown in this file (the first, out of the frame's sentence on
where a run stands, which nothing shows to hold along a run: Honest/K14/OnSending.lean; of the
second, the count at the positions that the frame lays at one request's challenges, not at a run's:
Honest/K14/BudRows.lean) · that the premises are met together at one side is not shown in this file
· one request: that the positions of all requests of a batch together are within the count is shown
by nothing · they range over every data, right or wrong · nothing on the committed table's own OOD
answers or columns, on roots, salts or paths.
WHICH PREMISES THE PROOFS READ. Of the field's own premises: the sentence at entry, the test on the
challenges, the bound on positions. READ BY NO PROOF, so without a negative theorem: that the rounds
seen are the front's; the front's test on what it holds; the stop (so the chain's number and the
first tree's too); in ShownOneLaw the premise on the declared rounds (the statement has the test on
the challenges at these rounds already); of the test on shapes the clause that trees can be laid.
What they rest on. The premises are those of the statements: Honest/K14/ExactStated.lean names each;
the averaging line's: its own docstring. They rest on files that are no part of the release's
library: another kind's laws on what a sending shows (rowsExact and the files beneath it in
Johnson/SendSim) and this kind's own. This file states no goal of the release. No property is
claimed.
-/
import Johnson.Desc.ProofFile.Honest.K14.ExactOfRows
import Johnson.SendSim.At.RowsExact

set_option autoImplicit false
set_option relaxedAutoImplicit false

-- An instance of the library (Cb.instNonemptyPGD, Cb/Obj/LdObjectReqStd.lean) is offered to every
-- search for Nonempty and sends it after a field that nothing determines; it is struck here.
attribute [-instance] Cb.instNonemptyPGD

namespace ProofFile.Honest.K14
open ProofFile.Honest.K1 (dueR)
open OnBytes.SendSim.At (rowsExact shownR budAt)

/-- **At fixed challenges that the two rounds can sample and fixed positions within the count, what
a sending's part shows, over its own coins, has one distribution at any two stands at which the
job's vectors are the same in both rounds.** The statement, with what is left beside it:
ShownOneLaw, Honest/K14/ExactStated.lean. -/
theorem shownOneLaw : ShownOneLaw := shownOneLaw_of_rows rowsExact

/-- **The field exact at a sending's part beside sendingSim**, general in the job. The statement,
with what is left beside it: ExactAtSending, Honest/K14/ExactStated.lean. -/
theorem exactAtSending : ExactAtSending := exactAtSending_of_rows rowsExact

/-- **The field exact at "send o_u".** The statement, with what is left beside it: ExactAtU,
Honest/K14/ExactStated.lean. NOT TO BE QUOTED WITHOUT THE OWNER's SENTENCE at that part. -/
theorem exactAtU : ExactAtU := exactAtU_of_rows rowsExact

/-- **The field exact at "send o_omega".** The statement, with what is left beside it: ExactAtOmega,
Honest/K14/ExactStated.lean. NOT TO BE QUOTED WITHOUT THE OWNER's SENTENCE at that part. -/
theorem exactAtOmega : ExactAtOmega := exactAtOmega_of_rows rowsExact

/-- **THE AVERAGING LINE.** Let the stand in front of the part (so the index, the index committer's
coins and the key) be sampled FIRST, by any distribution p over any type of causes, through any
function stand: so a key that is MADE of the committer's coins is one case. THE CHALLENGES, THE
POSITIONS, THE JOB AND THE SIDE ARE ONE AT ALL CAUSES: they are fixed before the stand is sampled;
where they hang on the cause this line says nothing. ASKED: at a job whose shapes pass the test, a
sub-protocol that declares the part's messages, challenges that the two rounds can sample and
POSITIONS WITHIN THE COUNT; SameData at every cause. Then the part's own coins are sampled. The pair
(cause, what the part shows) has the distribution in which the second is what the shared sending's
two moves show at no data, over coins of their own: it does not hang on the cause. THIS IS THE FORM
IN WHICH THE LAW AT EVERY FIXED STAND MAY BE AVERAGED. IN EVERY CASE THE INNER DISTRIBUTION RANGES
OVER THE PART's OWN COINS ALONE: the committer's coins enter through the cause, and in no other way.
THE UNSAFE FORM IS ANOTHER, AND DOES NOT FOLLOW: a law in which the committer's coins are sampled in
the place of the part's own, under a key that is a free variable. A case of this line in which the
key is held fixed while the committer's coins vary speaks of stands that no run reaches: there the
key is not made of the coins. -/
theorem shownAveraged {S Cl X Pb W ι : Type} (p : PMF ι) (J : SendJob)
    (hfit : sendShapeFits J = true) (wit : W → Ask) (φ : Face Empty W Pb)
    (σ : Side S Cl Empty W X Pb) (sim : Sim Pb) (hd : SendDeclared σ.block J)
    (stand : ι → Mid W X) (hsame : ∀ i, SameData J (stand i).st.heard) (ds : List Fmt.Drawn)
    (hds : drawsFit (VerifiableInference.Desc.K1.rounds J.Q) ds = true)
    (asks : List (List (List Nat))) (hb : budAt J.Q asks) :
    (p.bind fun i => (Prob.unif (Cs (sendingPart J).takes)).map fun c =>
        (i, σ.shows φ (sendingMember σ J wit sim) (c, (), ()) (stand i) ds asks)) =
      p.bind fun i => (Prob.unif (Cs (dueR J.Q (rideBySort J)))).map fun c =>
        (i, some (shownR J.Q 0 (rideBySort J) (fun _ _ _ => none) ds asks c)) :=
  shown_averaged rowsExact p J hfit wit φ σ sim hd stand hsame ds hds asks hb

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.shownOneLaw
#print axioms ProofFile.Honest.K14.exactAtSending
#print axioms ProofFile.Honest.K14.exactAtU
#print axioms ProofFile.Honest.K14.exactAtOmega
#print axioms ProofFile.Honest.K14.shownAveraged
