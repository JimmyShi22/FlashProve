-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/Accepted.lean: CONDITIONAL. Definitions of hypotheses, and
statements with their proofs.

What is here. A THREAD's DEBT `Accepted` (Honest/Thread/Pays.lean) AT THE MEMBER OF THE FEED-FORWARD
LAYERS' OWN ROUNDS (sub-protocol K4), BROUGHT DOWN TO ONE SENTENCE ON THE SUB-PROTOCOL's OWN
DECISION.

  `K4SitsBack T b p`   the way back through what the description wraps around the kind's
      sub-protocol: where that accepts from s to s', s' bears no mark and the reply is as it was,
      the member's own decision accepts from s to s'. (`K4Sits`, Law/Sits.lean, is the way there.)
      Law/SitsAt.lean has both at a member that is the lot's own sub-protocol, seated alone.
  `K4Hears T At fall b p`   at the stands in front that At names, at challenges that the member's
      rounds can sample, where nothing of the member stops and fall says nothing: the kind's
      sub-protocol at the first chain's state (`blockAtS p`) accepts THE ROUNDS AS PLAYED, without
      the sealed digest, at whatever groups of columns; behind it there is no mark, and the reply is
      as it was.
  `AcceptedAt T At fall b`   the sentence of `Accepted` with At in the stead of «Thr T b».
  `k4_accepted`   **AcceptedAt**, under K4SeatedA (Law/SeatedA.lean: four of K4Seated's nine
      fields), K4SitsBack and K4Hears: the step's own tests on the rounds, the columns and their
      number hold of what a half has played (`step_iff_decide`, Honest/Law/Cut.lean). Of the four it
      spends two: member and half.
  `k4_accepted_said`   so `AcceptedS T Said fall b`.

Not shown here. THAT THE KIND's DECISION ACCEPTS ANYTHING: `K4Hears` is a hypothesis here. That the
hypotheses can hold together: this file gives no example. WHAT AN ACCEPT OF THIS MEMBER IS WORTH: AN
ACCEPT HERE SAYS NOTHING OF THE VALUES SENT. By the sub-protocol's text (`hearAt`, `block`,
Johnson/Desc/First/K4/Block.lean) the decision calls neither of the kind's two runs of claims: it
asks that nothing is owed in front, two tests on the shape of the stretch of rounds, that what the
lookup has returned is there, and that the hearing returns and uses the stretch up. And other
writers' statement that the hearing returns (`hearAt_returns`,
Johnson/Desc/First/K4/Returns/Seat.lean) asks of the rounds, whichever they are, these two tests on
shape and that one sampled element is not 0: so, where its hypotheses on the plan and the state
hold, rounds of the right shape that hold other values than the honest ones are accepted too. By
reading, what the values are worth is tested where the kind's claims are added (the segment's
batching) and by its run "free-slot" behind that. Who proves K4Hears: Law/Hears.lean,
Law/TapeAccepts.lean and Law/HearsSeated.lean have it, over that statement that the hearing returns,
under: the seat; three tests on the plan alone; facts on the state in front (no mark; nothing owed;
what the lookup has heard is there and has the plan's sizes; room in the ledger; the tokens fit);
and a tie of fall to the test that one sampled element is 0. They ask nothing of what the prover has
sent but its shape, which they prove of the rounds as played. Following import lines, and stopping
unopened at every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/ and at
every module whose name begins Cb.Bridge, its imports reach 2 modules under Johnson/Bridge/ and none
of the others; what lies behind these is not counted. Nothing on completeness, on soundness or on
any other property.

Kin. `AcceptedAt` names no kind: it is `Accepted` (Honest/Thread/Pays.lean) at a free At;
`AcceptedS` (Honest/Thread/PaysS.lean) is its case At := «ThrS T Said b», which `k4_accepted_said`
shows by unfolding.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.RowKit
import Johnson.Desc.ProofFile.Honest.K4.Law.SeatedA
import Johnson.Desc.ProofFile.Honest.K4.Law.Sits
import Johnson.Desc.ProofFile.Honest.Thread.PaysS
import Johnson.Desc.ProofFile.Honest.Law.Cut
import Johnson.Desc.ProofFile.Frames1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes.Desc.First.K4 (Par blockAtS)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open VerifiableInference.Desc (Block OpenedColumn Claim First.S noDigest)

variable {Bk : ProverCoinCounts}

section
variable {V W X Pb : Type}

/-- **The way back through the wrappers.** This defines a hypothesis; the definition claims nothing.
-/
def K4SitsBack (T : Thread Bk First.S Claim V W X Pb) (b : Nat) (p : Par) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ s rs gs s', (blockAtS p).decide s rs gs = .ok s' →
    s'.failed = none → ProofFile.sameReply s s' = true → blk.decide s rs gs = .ok s'

/-- **The kind's own decision accepts the rounds as played.** This defines a hypothesis; the
definition claims nothing. -/
def K4Hears (T : Thread Bk First.S Claim V W X Pb)
    (At : Coins Bk → First.S → Mid W X → Env → Prop)
    (fall : Nat → First.S → List Fmt.Drawn → Option String) (b : Nat) (p : Par) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols, At k s m E →
    drawsFit blk.rounds ds = true →
    chainStopAt (T.φ.sees m.st.input) [blk] T.hs m.loc ds = none → fall b s ds = none →
    T.Moved blk k m E ds y cols →
    ∀ gs, ∃ s', (blockAtS p).decide s ((roundsOf y.1).map noDigest) gs = .ok s' ∧
      s'.failed = none ∧ ProofFile.sameReply s s' = true

variable {S Cl : Type}

/-- **The sentence of `Accepted`**, at the stands in front that At names. A definition: nothing is
claimed by it. -/
def AcceptedAt (T : Thread Bk S Cl V W X Pb) (At : Coins Bk → S → Mid W X → Env → Prop)
    (fall : Nat → S → List Fmt.Drawn → Option String) (b : Nat) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols, At k s m E →
    drawsFit blk.rounds ds = true →
    chainStopAt (T.φ.sees m.st.input) [blk] T.hs m.loc ds = none → fall b s ds = none →
    T.Moved blk k m E ds y cols → ∃ s', T.Stepped blk k s m E ds y cols s'

end

variable {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
  {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard} {Q : K4Pub} {p : Par}
  {blk₀ : Block First.S Claim} {fall : Nat → First.S → List Fmt.Drawn → Option String}

/-- **`Accepted` AT K4's MEMBER.** CONDITIONAL: on the seat, the way back, and the kind's own
decision on the played rounds. -/
theorem k4_accepted {At : Coins Bk → First.S → Mid (Local W₀ Rc Xi Tr) X → Env → Prop}
    (Se : K4SeatedA T b cells weights tokens look Q p blk₀) (hBk : K4SitsBack T b p)
    (hH : K4Hears T At fall b p) : AcceptedAt T At fall b := by
  intro blk hblk k s m E ds y cols hAt hd hst hf hM
  obtain rfl : blk₀ = blk := Option.some.inj (Se.member.symm.trans hblk)
  obtain ⟨s', h1, h2, h3⟩ := hH blk₀ hblk k s m E ds y cols hAt hd hst hf hM
    (VerifiableInference.Desc.regroup
      ((VerifiableInference.Desc.groupsOf T.ft blk₀.rounds ds).map (·.length)) cols)
  have hdec := hBk blk₀ hblk s _ _ s' h1 h2 h3
  have hM' := hM
  unfold Thread.Moved at hM'
  obtain ⟨⟨l, hl, hy⟩, hc⟩ := hM'
  obtain ⟨c, -, rfl, ho, hr⟩ := chainSteps_one hl Se.half
  exact ⟨s', hM, (step_iff_decide s s' hr ho hy hd hc).2 hdec⟩

/-- **`AcceptedS T Said fall b`.** CONDITIONAL, as `k4_accepted`; the decision is asked at the pair
alone. -/
theorem k4_accepted_said (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (Se : K4SeatedA T b cells weights tokens look Q p blk₀) (hBk : K4SitsBack T b p)
    (hH : K4Hears T (ThrS T Said b) fall b p) : AcceptedS T Said fall b :=
  k4_accepted Se hBk hH

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.K4SitsBack
#print axioms ProofFile.Honest.K4.K4Hears
#print axioms ProofFile.Honest.K4.AcceptedAt
#print axioms ProofFile.Honest.K4.k4_accepted
#print axioms ProofFile.Honest.K4.k4_accepted_said
