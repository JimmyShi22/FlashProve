-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/ExactStated.lean: kind K14: FOUR STATEMENTS, EACH AS THE
DEFINITION OF A PROPOSITION, WITH NO PROOF IN THIS FILE: the field exact of the frame's record Good
(Honest/Side.lean) at the parts of the two sendings of the batch's shared rounds, beside the
simulator of Honest/K14/ExactDefs.lean. That each follows from the shared sending's law at the rows
(Spec.rowsExact, Johnson/SendSim/At/Sim.lean) is shown in Honest/K14/ExactOfRows.lean; the four as
theorems: Honest/K14/ExactSend.lean. THIS FILE STATES NO GOAL OF THE RELEASE: the four count as
none.

  ExactAtSending  the field at a side whose row is a sending's part, general in the job
  ExactAtU, ExactAtOmega   the field at "send o_u" and at "send o_omega", general in the shared
                  rounds' parameters
  ShownOneLaw     at fixed challenges and fixed positions within the count: what a sending's part
                  shows has one distribution at any two stands at which SameData holds

A stand: where the chain's run stands in front of the part (Mid, Honest/Frame.lean): the input, the
challenges heard, what was handed on, the rounds seen.

The simulator is another text of a sending than the part: so each of the first three also says that
the two texts show one distribution. The fourth names no simulator.

WITH EVERY ONE OF THE FOUR. What a part shows is not all that a run shows of its messages: the
proximity tests behind the sendings, and of o_omega each request's own test, are handed these
messages' coins; nothing is said here of what they show · the simulator's rows meet none of the
later constraints on these messages (Honest/K14/ExactDefs.lean) · not to be quoted without the
owner's sentence (the field fresh) · the challenges and the positions are fixed before the coins are
sampled · the count on a carrier's main rows is meant to have no slack: that the statements fail at
one distinct position more of such a message's tree is in general not proved; at as many distinct
positions modulo the main code's length as a carrier's tail has entries, what the part shows,
columns and answers together, fixes the carrier's coins, given the data: nothing of them is left to
cover what the parts behind show (reckoned by hand; no Lean statement says so); the count on mask
rows serves the owner's sentence and the proof: these statements are not known to need it · the
statements range over every data, right or wrong: so they say nothing on whether the data are the
protocol's · no property is claimed.

What is assumed. hfit: the one test on the two sendings' shapes (sendingsFit,
Honest/K14/SendingsShapes.lean; in the general form its clause for one sending, sendShapeFits).
hrow: the side's row is the part beside sendingSim. hr: the sub-protocol declares the shared
sending's two rounds at the job's own parameters: from it and the frame's test on challenges: the
first challenge holds just the seeds, and no seed's factor is 0. hd: SendDeclared
(Honest/K14/SendingsPlay.lean): the part's messages fit what the sub-protocol states. hbud: the
bound on positions gives the count budAt (Johnson/SendSim/At/Sim.lean): of each message in a tree,
of its main rows at most as many distinct positions modulo the main code's length as that code's
tail has entries; the like for its mask rows. These five are on public data. hOn: the sentence at
the part's entry gives SameData (at the two sendings: pointApart): what is asked of that sentence
reads the job and the challenges heard. That clause serves the proof of the statements
(Honest/K14/ExactDefs.lean says why); it is not known to be needed. The widest sentence at entry and
the widest bound that meet the two implications are pointApart and budAt themselves:
Honest/K14/ExactRows.lean lays these.
NO PREMISE READS THE INPUT. The index, the index committer's coins and the key are the three fields
of one variable, the input, which is fixed before either distribution is formed; the distributions
are over the part's own coins and over the simulator's own.
What is not claimed. In this file: that any of the four holds. That a run's positions are within the
count. That the positions which all requests of a batch read of one tree are together within it: the
frame's run (Honest/Frame.lean) is of one request; the positions are a free variable here, so the
statements bear such a union; nothing shows that it is within the count. That the premises are met
at a description of the release. Anything on the committed table's own OOD answers or columns, which
no part here shows; on roots, salts or paths; on what is or is not hidden.
-/
import Johnson.Desc.ProofFile.Honest.K14.ExactDefs
import Johnson.Desc.ProofFile.Honest.K14.SendingsShapes
import Johnson.Desc.ProofFile.Honest.Small.Field

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open ProofFile.Honest.Small (ExactMember)
open OnBytes.SendSim.At (budAt)

/-- **The field exact of Good at a side whose row is a sending's part beside sendingSim.** A
STATEMENT, NOT A THEOREM IN THIS FILE; its proof: exactAtSending, Honest/K14/ExactSend.lean. At a
stand at which the job's vectors are the same in both rounds, at fixed challenges that the two
rounds can sample and fixed positions within the count: what THIS part shows, over its own coins,
has the distribution of what the simulator tells over its own. WHAT THE PART SHOWS IS NOT ALL THAT A
RUN SHOWS OF ITS MESSAGES: the parts behind it that are handed these messages' coins show more;
nothing is said here of what they show. NOT TO BE QUOTED WITHOUT THE OWNER's SENTENCE (the field
fresh). The challenges and the positions are fixed before the coins are sampled. THE COUNT ON A
CARRIER's MAIN ROWS IS MEANT TO HAVE NO SLACK: that the statement fails at one distinct position
more of such a message's tree is in general not proved. The count on mask rows serves the owner's
sentence and this statement's proof; no datum stands in a mask row, and this statement is not known
to need it. It ranges over every data, right or wrong. No property is claimed. -/
def ExactAtSending : Prop :=
  ∀ (S Cl X Pb W : Type) (J : SendJob) (_hfit : sendShapeFits J = true) (wit : W → Ask)
    (φ : Face Empty W Pb) (σ : Side S Cl Empty W X Pb)
    (_hrow : σ.row = [(liftSend wit (sendingPart J), sendingSim J ⟨σ.block.place, 0⟩)])
    (_hr : σ.block.rounds = VerifiableInference.Desc.K1.rounds J.Q)
    (_hd : SendDeclared σ.block J) (chain firstTree : Nat)
    (On : (u : Member Empty W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (_hOn : ∀ u ca m front, On u ca m front → SameData J m.st.heard)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop)
    (_hbud : ∀ ds asks, bud 0 ds asks → budAt J.Q asks),
    ∀ u ∈ σ.members, ExactMember φ σ chain firstTree On bud u

/-- **The field exact of Good at "send o_u"**, general in the shared rounds' parameters. A
STATEMENT, NOT A THEOREM IN THIS FILE; its proof: exactAtU, Honest/K14/ExactSend.lean. At a stand at
which the number of challenges heard is not the number of "LIN point", at fixed challenges that the
two rounds can sample and fixed positions within the count: what THIS part shows, over its own
coins, has the distribution of what the simulator tells over its own. WHAT THE PART SHOWS IS NOT ALL
THAT A RUN SHOWS OF ITS MESSAGES: the proximity test on G_u behind it is handed these messages'
coins; nothing is said here of what it shows. NOT TO BE QUOTED WITHOUT THE OWNER's SENTENCE (the
field fresh). The challenges and the positions are fixed before the coins are sampled. THE COUNT ON
A CARRIER's MAIN ROWS IS MEANT TO HAVE NO SLACK: that the statement fails at one distinct position
more of such a message's tree is in general not proved. The count on mask rows serves the owner's
sentence and this statement's proof; no datum stands in a mask row, and this statement is not known
to need it. It ranges over every data, right or wrong. No property is claimed. -/
def ExactAtU : Prop :=
  ∀ (S Cl X Pb W₀ Rc Ky : Type) (A : SendPub) (_hfit : sendingsFit A.P = true)
    (wit : Common W₀ Rc Ky → Ask) (φ : Face Empty (Common W₀ Rc Ky) Pb)
    (σ : Side S Cl Empty (Common W₀ Rc Ky) X Pb)
    (_hrow : σ.row =
      [(liftSend wit (sendingPart (jobU A)), sendingSim (jobU A) ⟨σ.block.place, 0⟩)])
    (_hr : σ.block.rounds = VerifiableInference.Desc.K1.rounds (jobU A).Q)
    (_hd : SendDeclared σ.block (jobU A)) (chain firstTree : Nat)
    (On : (u : Member Empty (Common W₀ Rc Ky) X Pb) → CsAll u.part.carries →
      Mid (Common W₀ Rc Ky) X → Before → Prop)
    (_hOn : ∀ u ca m front, On u ca m front → pointApart A m.st.heard)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop)
    (_hbud : ∀ ds asks, bud 0 ds asks → budAt (jobU A).Q asks),
    ∀ u ∈ σ.members, ExactMember φ σ chain firstTree On bud u

/-- **The field exact of Good at "send o_omega"**, general in the shared rounds' parameters. A
STATEMENT, NOT A THEOREM IN THIS FILE; its proof: exactAtOmega, Honest/K14/ExactSend.lean. At a
stand at which the number of challenges heard is not the number of "LIN point", at fixed challenges
that the two rounds can sample and fixed positions within the count: what THIS part shows, over its
own coins, has the distribution of what the simulator tells over its own. WHAT THE PART SHOWS IS NOT
ALL THAT A RUN SHOWS OF ITS MESSAGES: both proximity tests behind it, and each request's own test,
are handed these messages' coins; nothing is said here of what they show. NOT TO BE QUOTED WITHOUT
THE OWNER's SENTENCE (the field fresh). The challenges and the positions are fixed before the coins
are sampled. THE COUNT ON A CARRIER's MAIN ROWS IS MEANT TO HAVE NO SLACK: that the statement fails
at one distinct position more of such a message's tree is in general not proved. The count on mask
rows serves the owner's sentence and this statement's proof; no datum stands in a mask row, and this
statement is not known to need it. It ranges over every data, right or wrong. No property is
claimed. -/
def ExactAtOmega : Prop :=
  ∀ (S Cl X Pb W₀ Rc Ky : Type) (A : SendPub) (_hfit : sendingsFit A.P = true)
    (wit : Common W₀ Rc Ky → Ask) (φ : Face Empty (Common W₀ Rc Ky) Pb)
    (σ : Side S Cl Empty (Common W₀ Rc Ky) X Pb)
    (_hrow : σ.row =
      [(liftSend wit (sendingPart (jobOmega A)), sendingSim (jobOmega A) ⟨σ.block.place, 0⟩)])
    (_hr : σ.block.rounds = VerifiableInference.Desc.K1.rounds (jobOmega A).Q)
    (_hd : SendDeclared σ.block (jobOmega A)) (chain firstTree : Nat)
    (On : (u : Member Empty (Common W₀ Rc Ky) X Pb) → CsAll u.part.carries →
      Mid (Common W₀ Rc Ky) X → Before → Prop)
    (_hOn : ∀ u ca m front, On u ca m front → pointApart A m.st.heard)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop)
    (_hbud : ∀ ds asks, bud 0 ds asks → budAt (jobOmega A).Q asks),
    ∀ u ∈ σ.members, ExactMember φ σ chain firstTree On bud u

/-- **At one fixed list of challenges that the two rounds can sample and one fixed list of positions
within the count, what a sending's part shows, over its own coins, has one distribution at any two
stands at which the job's vectors are the same in both rounds.** A STATEMENT, NOT A THEOREM IN THIS
FILE; its proof: shownOneLaw, Honest/K14/ExactSend.lean. No simulator occurs: sim is a free variable
that nothing reads. WHAT THE PART SHOWS IS NOT ALL THAT A RUN SHOWS OF ITS MESSAGES: the parts
behind it that are handed these messages' coins show more; nothing is said here of what they show.
NOT TO BE QUOTED WITHOUT THE OWNER's SENTENCE (the field fresh). The challenges and the positions
are fixed before the coins are sampled. THE COUNT ON A CARRIER's MAIN ROWS IS MEANT TO HAVE NO
SLACK: that the statement fails at one distinct position more of such a message's tree is in general
not proved. The count on mask rows serves the owner's sentence and this statement's proof; no datum
stands in a mask row, and this statement is not known to need it. It ranges over every data, right
or wrong. No property is claimed. -/
def ShownOneLaw : Prop :=
  ∀ (S Cl X Pb W : Type) (J : SendJob) (_hfit : sendShapeFits J = true) (wit : W → Ask)
    (φ : Face Empty W Pb) (σ : Side S Cl Empty W X Pb) (sim : Sim Pb)
    (_hr : σ.block.rounds = VerifiableInference.Desc.K1.rounds J.Q)
    (_hd : SendDeclared σ.block J) (m m' : Mid W X) (ds : List Fmt.Drawn)
    (asks : List (List (List Nat))),
    SameData J m.st.heard → SameData J m'.st.heard →
    drawsFit (VerifiableInference.Desc.K1.rounds J.Q) ds = true → budAt J.Q asks →
    (Prob.unif (Cs (sendingPart J).takes)).map
        (fun c => σ.shows φ (sendingMember σ J wit sim) (c, (), ()) m ds asks) =
      (Prob.unif (Cs (sendingPart J).takes)).map
        fun c => σ.shows φ (sendingMember σ J wit sim) (c, (), ()) m' ds asks

end ProofFile.Honest.K14
