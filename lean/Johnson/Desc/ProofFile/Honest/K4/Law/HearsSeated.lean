-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/HearsSeated.lean: CONDITIONAL.

What is here. THE THREAD's DEBT `Accepted` (Honest/Thread/Pays.lean) AT THE MEMBER OF THE
FEED-FORWARD LAYERS' OWN ROUNDS (sub-protocol K4), at any thread, with both halves of `K4Hears`
(Law/Accepted.lean) laid together: the rounds as a tape (Law/TapeAccepts.lean) and the state and the
plan (Law/Hears.lean). Statements and proofs: calls.

  `k4TapeFits_seated`, `k4TapeCoin_seated`   the two hypotheses on the tape, under `K4SeatedA`.
  `k4Hears_seated`   **K4Hears.**
  `k4_accepted_ready`   **AcceptedAt T At fall b** (Law/Accepted.lean: `Accepted`'s sentence at a
      free At); `k4_accepted_ready_said`: so AcceptedS (Honest/Thread/PaysS.lean).

Not shown here. THAT THE HYPOTHESES CAN HOLD TOGETHER: this file gives no example. What stays:
`K4SeatedA` (Law/SeatedA.lean: the four of the nine fields of `K4Seated` that are read here) ·
`K4SitsBack` (Law/Accepted.lean) · the three tests on the plan (`k4PlanB`) · the state in front at
every stand that At names (`K4ReadyP`: who is meant to prove which field is said in Law/Hears.lean)
· that where the chain's fall says nothing, the honest side's test on one sampled element says
nothing. THE MEMBER's STEP TESTS NO SENT VALUE: it accepts every play of the right shape, a false
one too: that the honest play is accepted is all that is said. Following import lines, and stopping
unopened at every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/ and at
every module whose name begins Cb.Bridge, its imports reach 2 modules under Johnson/Bridge/, and
none of the others; what lies behind these is not counted; 8 of the modules that it reaches have
RecCompile in their names, none of them RecCompile's Honest*, Both or PassH*. An earlier walk, which
opened every module that it reached, met none under Johnson/Goal/, Johnson/D/ or ThirdParty/.

Kin. The same debt at a thread of the first chain, above this file: `k4_accepted_head`
(Law/ReadyHead.lean), `k4_accepted_all` (Law/ElevenHead.lean). Another kind's like law at its own
member: `k13_accepted_at_head_filler` (Honest/K13/AcceptedAtHeadFiller.lean).

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Hears
import Johnson.Desc.ProofFile.Honest.K4.Law.TapeAccepts

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open VerifiableInference.Desc (Block Claim First.S)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
  {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard} {Q : K4Pub} {p : Par}
  {blk₀ : Block First.S Claim} {fall : Nat → First.S → List Fmt.Drawn → Option String}
  {At : Coins Bk → First.S → Mid (Local W₀ Rc Xi Tr) X → Env → Prop}

theorem k4TapeFits_seated (Se : K4SeatedA T b cells weights tokens look Q p blk₀) :
    K4TapeFits T b p := by
  intro blk hblk k m E ds y cols hM hd
  obtain rfl : blk₀ = blk := Option.some.inj (Se.member.symm.trans hblk)
  exact k4_played_fits Se hM hd

theorem k4TapeCoin_seated (Se : K4SeatedA T b cells weights tokens look Q p blk₀) :
    K4TapeCoin T b Q p := by
  intro blk hblk k m E ds y cols hM hz
  obtain rfl : blk₀ = blk := Option.some.inj (Se.member.symm.trans hblk)
  exact k4_coin_tape Se hM hz

/-- **The sub-protocol's own decision accepts the rounds as played.** CONDITIONAL. -/
theorem k4Hears_seated (Se : K4SeatedA T b cells weights tokens look Q p blk₀)
    (hPl : k4PlanB p = true) (hRd : ∀ k s m E, At k s m E → K4ReadyP p s)
    (hf : ∀ s ds, fall b s ds = none → k4CoinZero Q ds = none) : K4Hears T At fall b p :=
  k4Hears_of_plan (k4TapeFits_seated Se) (k4TapeCoin_seated Se) hPl hRd hf

/-- **THE MEMBER's STEP ACCEPTS THE HONEST PLAY.** CONDITIONAL. -/
theorem k4_accepted_ready (Se : K4SeatedA T b cells weights tokens look Q p blk₀)
    (hBk : K4SitsBack T b p) (hPl : k4PlanB p = true)
    (hRd : ∀ k s m E, At k s m E → K4ReadyP p s)
    (hf : ∀ s ds, fall b s ds = none → k4CoinZero Q ds = none) : AcceptedAt T At fall b :=
  k4_accepted Se hBk (k4Hears_seated Se hPl hRd hf)

/-- **`AcceptedS T Said fall b`.** CONDITIONAL; the state in front is asked at the stands of the
thread with Said (`ThrS T Said b`) alone. -/
theorem k4_accepted_ready_said (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (Se : K4SeatedA T b cells weights tokens look Q p blk₀) (hBk : K4SitsBack T b p)
    (hPl : k4PlanB p = true) (hRd : ∀ k s m E, ThrS T Said b k s m E → K4ReadyP p s)
    (hf : ∀ s ds, fall b s ds = none → k4CoinZero Q ds = none) : AcceptedS T Said fall b :=
  k4_accepted_ready Se hBk hPl hRd hf

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4TapeFits_seated
#print axioms ProofFile.Honest.K4.k4TapeCoin_seated
#print axioms ProofFile.Honest.K4.k4Hears_seated
#print axioms ProofFile.Honest.K4.k4_accepted_ready
#print axioms ProofFile.Honest.K4.k4_accepted_ready_said
