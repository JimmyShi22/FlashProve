-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/MaskStated.lean: kind K14: THREE STATEMENTS, EACH AS THE
DEFINITION OF A PROPOSITION, WITH NO PROOF IN THIS FILE: the owner's sentence of the frame (the
field fresh of Good, Honest/Side.lean) at the part at "send o_u", which owns the coefficients that
the first fold of the proximity test on G_u spends. Their proofs: Honest/K14/MaskOfRows.lean,
MaskLaw.lean, MaskSend.lean. THIS FILE STATES NO GOAL OF THE RELEASE: the three count as none.

  MaskFresh       what the law concludes at a book, an order of places and an owner: at every side
                  that stands at the owner's place, whose row is the part at "send o_u" and whose
                  sub-protocol declares the shared sending's rounds, and at every bound that gives
                  budAt: the field fresh of Good at every member, in the field's own form
  MaskApart       THE SENTENCE IN WHICH NO BOOK OCCURS: the coefficients · what the part shows · all
                  of the message o_u's coins (the part's own, not the index committer's) have the
                  distribution in which the first is sampled afresh
  MaskOwnerLaw    THE LAW IN THE FRAME's FORM (OwnerLaw, Honest/BookGuard.lean) at the test
                  maskOwnerTest (Honest/K14/MaskOwner.lean), with the guard by name in the premise
  MaskBridge      where runIs and knownBelow (Honest/K14/FreshDefs.lean) accept, the frame's form
                  holds at every spender that spends

WITH EVERY ONE OF THEM. WHAT THE PART SHOWS IS NOT ALL THAT A RUN SHOWS OF THESE COEFFICIENTS: the
fold that spends them sends its scalars under them, and the part behind that fold is handed the
first mask whole, coefficients and tails; nothing is said here of what they show. The challenges and
the positions are fixed before the coins are sampled. THE OWNER's HALF ALONE: the spender's sentence
(the field exact at the fold, which takes the run as uniform) is not met; nor is the field exact, at
each fixed carried run, of the part behind the fold. THE BOUND IS SHARP AT THE FIRST MASK's ROWS, BY
A HAND RECKONING: at one distinct point more than a row's tail has entries the equation fails; in
general no Lean statement says so. (How many positions a description declares at that tree is
another matter, and is not said here.) They stand at stands that no run reaches, and at every data,
right or wrong: so they say nothing on whether the data are the protocol's. ONE REQUEST: the frame's
run is of one request. AT EVERY SHAPE OF THIS KIND's PLAN THAT IS WRITTEN OR PLANNED THE FIRST MASK
HAS ONE ROW (s.h = 0): that each row has a tail of its own has a member only at a made-up shape with
two rows. No property is claimed.

What is assumed, all on public data. The first three premises: the one test on the two sendings'
shapes accepts (sendingsFit, Honest/K14/SendingsShapes.lean); masks are sent ahead; the test on G_u
has a first stage s: so the sending has a second message, laid of 2 s.k + 1 coefficients in 2 ^ s.h
rows. The side's row is the part, beside any simulator. Its sub-protocol declares the shared
sending's two rounds at the job's own parameters, and SendDeclared (Honest/K14/SendingsPlay.lean):
the part's messages fit what it states. The bound on positions gives the count budAt
(Johnson/SendSim/At/Sim.lean). Of these, the sentence fails, by a hand reckoning, without: the
count's clause on the first mask's rows; the test on the book; and, of the shapes, where o_u has a
mask row AND a code's message length is off a power of two. The declared rounds, SendDeclared and
the count's clause on o_u's rows are taken because the field exact at the same row takes them: one
row has one bound; this sentence is not known to need them.
NO PREMISE READS THE INPUT. The index, the index committer's coins and the key are the three fields
of one variable, the input, which is fixed before either distribution is formed; the distributions
are over the part's own coins.
What is not claimed. In this file: that any of the three holds. That any book of a description
passes the test. That a run's positions are within the count. That the number of variables in the
shape is the number of rounds of the fold that spends: the test on the book accepts only where the
book's run has 2 s.k + 1 coins. Anything on what is or is not hidden.
-/
import Johnson.Desc.ProofFile.Honest.K14.MaskOwner
import Johnson.Desc.ProofFile.Honest.K14.SendingsPlay
import Johnson.Desc.ProofFile.Honest.K14.SendingsShapes
import Johnson.Desc.ProofFile.Honest.Small.Field
import Johnson.SendSim.At.Sim

set_option autoImplicit false
set_option relaxedAutoImplicit false

-- An instance of the library (Cb.instNonemptyPGD, Cb/Obj/LdObjectReqStd.lean) is offered to every
-- search for Nonempty and sends it after a field that nothing determines; it is struck here.
attribute [-instance] Cb.instNonemptyPGD

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Place)
open ProofFile.Honest.Small (FreshMember)
open OnBytes.SendSim.At (budAt)

/-- **The field fresh of Good at every side that stands at the owner's place, whose row is the part
at "send o_u" and whose sub-protocol declares the shared sending's rounds, at every bound that gives
budAt.** A definition: the form of a conclusion. -/
def MaskFresh (A : SendPub) (Bk : ProverCoinCounts) (ord : List Place) (o : Addr) : Prop :=
  ∀ (S Cl X Pb W₀ Rc Ky : Type) (wit : Common W₀ Rc Ky → Ask) (sim : Sim Pb)
    (φ : Face Empty (Common W₀ Rc Ky) Pb) (σ : Side S Cl Empty (Common W₀ Rc Ky) X Pb),
    σ.row = [(liftSend wit (sendingPart (jobU A)), sim)] →
    σ.block.rounds = VerifiableInference.Desc.K1.rounds (jobU A).Q →
    SendDeclared σ.block (jobU A) → ({ place := σ.block.place, part := 0 } : Addr) = o →
    ∀ bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop,
      (∀ ds asks, bud 0 ds asks → budAt (jobU A).Q asks) →
      ∀ u ∈ σ.members, FreshMember φ σ Bk ord bud u

/-- **At fixed challenges and fixed positions within the count, at shapes that the test accepts: the
first mask's coefficients are uniform, and independent of what the part shows together with all of
o_u's coins.** A STATEMENT, NOT A THEOREM IN THIS FILE; its proof: maskApart,
Honest/K14/MaskSend.lean. No book occurs. WHAT THE PART SHOWS IS NOT ALL THAT A RUN SHOWS OF THESE
COEFFICIENTS: the fold that spends them sends its scalars under them, and the part behind that fold
is handed the first mask whole, coefficients and tails; nothing is said here of what they show. The
challenges and the positions are fixed before the coins are sampled. THE OWNER's HALF ALONE: the
spender's sentence (the field exact at the fold) is not met; nor is the field exact, at each fixed
carried run, of the part behind the fold. THE BOUND IS SHARP AT THE FIRST MASK's ROWS, BY A HAND
RECKONING: at one distinct point more than a row's tail has entries the equation fails; in general
no Lean statement says so. No property is claimed. -/
def MaskApart : Prop :=
  ∀ (S Cl X Pb W₀ Rc Ky : Type) (A : SendPub) (s : OnBytes.Params.IoppStage)
    (_hfit : sendingsFit A.P = true) (_hm : A.P.S.masksAhead = true)
    (_hs : A.P.S.testU.head? = some s)
    (wit : Common W₀ Rc Ky → Ask) (sim : Sim Pb) (φ : Face Empty (Common W₀ Rc Ky) Pb)
    (σ : Side S Cl Empty (Common W₀ Rc Ky) X Pb)
    (_hrow : σ.row = [(liftSend wit (sendingPart (jobU A)), sim)])
    (_hr : σ.block.rounds = VerifiableInference.Desc.K1.rounds (jobU A).Q)
    (_hd : SendDeclared σ.block (jobU A)),
    ∀ u ∈ σ.members, ∀ sp ca m ds asks,
      drawsFit (u.rounds.map (·.1)) ds = true → budAt (jobU A).Q asks →
      (Prob.unif (Cs u.part.takes)).map (fun c =>
          (c.cut ⟨0, maskFirstCoin A⟩ ⟨0, 2 * s.k + 1⟩, σ.shows φ u (c, sp, ca) m ds asks,
            c.cut ⟨0, 0⟩ ⟨0, maskFirstCoin A⟩)) =
        (Prob.unif (Cs ⟨0, 2 * s.k + 1⟩ × Cs u.part.takes)).map fun a =>
          (some a.1, σ.shows φ u (a.2, sp, ca) m ds asks, a.2.cut ⟨0, 0⟩ ⟨0, maskFirstCoin A⟩)

/-- **The law at the test, in the frame's form**, under the three premises on the shapes: at the
owner that the test names, where fits accepts and GuardClear holds at the guard maskGuard at every
spender that spends: the field fresh, as MaskFresh words it. A STATEMENT, NOT A THEOREM IN THIS
FILE; its proof: maskOwnerLaw, Honest/K14/MaskSend.lean. WHAT THE PART SHOWS IS NOT ALL THAT A RUN
SHOWS OF THESE COEFFICIENTS: the fold that spends them sends its scalars under them, and the part
behind that fold is handed the first mask whole, coefficients and tails; nothing is said here of
what they show. The challenges and the positions are fixed before the coins are sampled. THE OWNER's
HALF ALONE: the spender's sentence (the field exact at the fold) is not met; nor is the field exact,
at each fixed carried run, of the part behind the fold. THE BOUND IS SHARP AT THE FIRST MASK's ROWS,
BY A HAND RECKONING: at one distinct point more than a row's tail has entries the equation fails; in
general no Lean statement says so. No property is claimed. -/
def MaskOwnerLaw : Prop :=
  ∀ (A : SendPub) (s : OnBytes.Params.IoppStage)
    (_hfit : sendingsFit A.P = true) (_hm : A.P.S.masksAhead = true)
    (_hs : A.P.S.testU.head? = some s),
    OwnerLaw (maskOwnerTest A s.k) (MaskFresh A)

/-- **Where runIs and knownBelow accept, the frame's form holds** at every spender that spends
something of the owner. A STATEMENT, NOT A THEOREM IN THIS FILE; its proof: maskBridge,
Honest/K14/MaskLaw.lean. On lists of entries alone: no distribution occurs. -/
def MaskBridge : Prop :=
  ∀ (A : SendPub) (k : Nat) (Bk : ProverCoinCounts) (ord : List Place) (o : Addr),
    runIs Bk o (maskFirstCoin A) (2 * k + 1) = true →
    knownBelow Bk ord o (maskFirstCoin A) = true →
    ∀ p, Bk.spentBy o p ≠ [] → GuardClear (maskGuard A) Bk ord o p

end ProofFile.Honest.K14
