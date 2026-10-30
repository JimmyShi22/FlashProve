-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LSeatsStatement.lean: ONE DEFINITION OF A SENTENCE. NOTHING
IS PROVED HERE: its proof is `fits_at_every_reached_record` (LSeatsLaw.lean).

  `FitsAtEveryReachedRecord`   under the library's head (`P5J.AtMgA` at `OnBytes.secondHashFunction`), at the
      blank ground and the finish of the code switch that is there, at EVERY state s that the first
      chain's sub-protocols' steps (each behind its test on the words shown, `below`) reach at
      border 354 and at the record T that the way into the
      closing proximity test (`enterFinish`) returns at s: at every job whose parameters are the
      planner's and whose state on entry is T, `FrontAsksD` at a plain data Dp gives `FitsAtL`
      (ClosingData.lean) at that Dp.

What it is for. `dataFront_L` (ClosingData.lean) asks `FitsAtL`, of whose 21 clauses thirteen read
the plain data, and its spender wants it at every stand of the thread. `FrontAsksD` comes of the
test `frontFiveB` on the shape of T (`frontAsksD_at_L`, ClosingFront.lean). So with this sentence
that one test is all that is asked of T's shape (`asks_at_head`, LShapeAtHead.lean): for the
thirteen no shape of a state is written, and no run on shapes is made.

The road. No walk over the 354 members. (1) The library's facts on every reached state
without a mark (`FoldFacts`, Johnson/Desc/First/FoldFacts.lean, at the head by `foldFacts_raw`,
Honest/Thread/ReachFacts.lean): the book's places and its trees' shapes are prefixes of the plan's
written lists, the messages' shapes are a prefix of the plan's written list, and the tree at place z
bears the number ft + z. (2) Of `FrontAsksD`: the guard's own clauses at Dp (`gpL`: the declared
openings name the trees of Dp by number, the fresh table has no main row and is no member, the
members' blocks have room and lie apart) and, of the door's clause on a member with a main row, that
there is a member. (3)
A closed line of Lean's kernel at the written lists: two messages, and no other, sit in the declared
tree; their shapes, parts and tree's shape are those of the finish's sending.

Limits. A sentence. `frontFiveB` stays a premise of the spender.
Terms: the head of LShapeTest.lean; Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingData
import Johnson.Desc.ProofFile.Honest.K12.ShapeAllDense
import Johnson.Desc.K12.SeatLaws
import Johnson.P5J.K09List

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open OnBytes (Codes)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.K12 (T12 enterFinish)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach)
open H2K.First (Plain)
open ProofFile.Honest.K12 (TestJob FrontAsksD)
open P5J (AtMgA)

/-- **The sentence**: at every reached record `FrontAsksD` gives `FitsAtL` at its own plain data. -/
def FitsAtEveryReachedRecord : Prop :=
  ∀ {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place},
    AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x →
    ∀ {G : ProofFile.Ground}, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G →
    ∀ {pl : K2.SwitchPlace}, finishAt Zp G = some pl →
    ∀ {pI : ProofFile.InstPub} {s : S}, Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 354 (pI, s) →
    ∀ {T : T12}, enterFinish s = .ok T →
    ∀ {W X : Type} (J : TestJob W X) (w : W) (fr : Front X), J.p = H2U.p12OfMade Zp.made →
      J.rec₀ w fr = T →
    ∀ {K : Codes} {Dp : Plain}, FrontAsksD J w fr K Dp → ∃ s₁ u Ly, FitsAtL J.p pl Dp s₁ u Ly

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.FitsAtEveryReachedRecord
