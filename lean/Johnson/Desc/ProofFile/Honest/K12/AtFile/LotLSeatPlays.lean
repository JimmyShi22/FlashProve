-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLSeatPlays.lean

It states no goal. No property of the protocol is claimed.

`Plays` at the first chain's closing
proximity test (member 354) at the base prover's thread: H := A.H, Q := `firstScriptAt I Sz Op A cF`:
`closingTestPlays_at_firstScript` (LotLTableFirstScript.lean) with hT paid and hready brought to two
public tests.

  `closingTestPlays_at_base`   at the finish pl; left, each in the form in which its law concludes it:
                               hh, hok, hpub

By what. `closingTestTies_at_base`, `makersBook_at_base`, `blankGround_at_base`
(LotLSeatPlaysPremises.lean); `switch_lot_ready_at_every_closing_stand` (LotLOwedReady.lean).

Hypotheses. h: the head. hA: the maker returns A at the base prover's filling. hf: pl is the finish.
hh: the side that the search finds at the test's place is the pair of the lot's job: the sentence of
`L_found` (AtFullSide/K12/LettersFoundL.lean). hok: the closing's public test at the finish: the
sentence of `closing_test_passes_at_finish` (LotLOwedClosed.lean). hpub: the filling's public test at
every input that the thread calls valid: the sentence of `closing_public_at_valid`
(LotLPublicClosing.lean) at `Sz.ref`. The three are called in LotLSeatPlaysPaid.lean: the rows beneath
the first two are heavy.

Limits.
- The full size and the format's second hash function alone.
- hh, hok, hpub ARE PREMISES; where one of them fails this says nothing.
- `Plays` speaks of stands of the thread; that a stand is reached is not said.
- That the test accepts what is played is not said here.
- At the base prover's filling's return, at its own type of random values: NOT AT THE ONLINE PROVER,
  whose filling reads this one through the coins' map.
- The statements at the maker's return are typed at `OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit`: they cannot
  even be written at the online prover's return (`OnlineProverWithDescription FullSizeMatrix (protocolAtFiles files).EncodingRandomness Cells Unit Unit`,
  E2E/TheHonestProver.lean): no law through `OnlineProverParts.through` is made here.
- Nothing on completeness of the chain, soundness or hiding.

NOT IN FRONT OF A LAW OVER COINS: `closingTestPlays_at_base` bears this label; the rule is at its
home, the head of Johnson/Bind/ForProver/FiveFieldsAt.lean.
This file's own ground, in the rule's terms.
- h and hA speak of the public files, of the letters I and Op (how an index, an instance and the
  challenges are read, and one named member of the index's type) and of what the maker returns at
  the filling made of them. By their text they name no coin, no run's input (its index, its trace)
  and no Script: of neither kind.
- hf, hh and hok speak of the finish, of the prover's side that the search finds at the test's place
  and of the closing's public test: they name no coin. hpub is bound over every input that meets Vd
  and reads its instance: it names no coin.
- w, the run's input, is a letter under no premise in front. It holds the committer's coins (its
  field rc) and the hidden input (its fields w₀ and trace).
- A run's coins k are bound inside the end, `Plays`. Beside k it binds the letters s, m and E (the
  verifier's state, the state of the prover's side, the available tables) under `Thr … 354 k s m E`:
  a premise of the first kind: it names k; by its text, at fixed s, m and E it can hold at some
  values of the coins and fail at others.
- `Plays` | `PlaysS` binds besides l under `chainSteps … (k.look T.chain) … = .ok l`: of the first
  kind.
- ds, the challenges, stands under `drawsFit` (no coin) and under `chainStopAt (T.φ.sees m.st.input)
  …`: no run's coin is among its arguments (`Part.stopAt`, Honest/Side.lean), but in the first chain
  the face shows a part's second stop the whole input of m (`Face.sees`, Honest/Frame.lean), which
  holds rc and the hidden input: of the first kind as far as such a stop reads rc, of the second as
  far as it reads the index or the trace; what the parts at 354 read is not fixed here.
- One clause of the invariant says that the input of m is w and meets Vd, a letter for a predicate
  on the input: what it reads of the input is not fixed here.
- The thread's other letters (test, carryX, item, n₁, n₂, b₀, Vd, Rd, Kp) stand under no premise in
  front that names a coin; the invariant reads them. The Script is no letter: it is the term
  `firstScriptAt`.
- What lifts the bar: for s, m, E and l the made terms would be those of the honest run at the
  border, as terms of w, k and the challenges, and the lemma would show the premises at them at
  every value of the coins. For ds, which no term of the prover's makes, the lemma would show that
  at each ds `chainStopAt … = none` holds at every value of rc or at none. None is known to this
  file: the bar is flat.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLSeatPlaysPremises
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLTableFirstScript
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLOwedReady

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K12.LotL
open VerifiableInference.Desc (Block Chain Place Strs)
open OnBytes.Maker (WholeD)
open ProofFile.Honest.FirstThread (lettersHead WtF)
open ProofFile.Honest.K1 (LocB firstScriptAt readersB closingB)
open ProofFile.Honest.K12.AtProof (finishAt jobL doorAtL switch_lot_ready_at_every_closing_stand)
open P5J (AtMgA TS)

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {I : WiderIn W₀} {Sz : OnBytes.HonestTrace.Sz} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {pl : K2.SwitchPlace}

/-- hh, hok AND hpub ARE PREMISES. **`Plays` at the closing test, at the base prover's thread.** -/
theorem closingTestPlays_at_base (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction Sz Op) = .ok A)
    (hf : finishAt A.Z A.G = some pl) (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : LocB W₀ → Prop) (Rd : Nat → LocB W₀ → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : LocB W₀)
    (hh : (A.H.first.find? fun g => g.place == (H2U.p12OfMade A.Z.made).place) =
      some (proverSideOfProximityTest (jobL (H2U.p12OfMade A.Z.made) (doorAtL A.Z) (widerRows Sz A.Z A.G)
                         (readersB I A.Z) (closingB A.Z A.G) pl)))
    (hok : K2.closingOk K2.freshTable ((K2.segmentsOf A.Z A.G).take pl.link) pl = true)
    (hpub : ∀ v, Vd v → K2.publicOk (widerRows Sz A.Z A.G) A.G.first.layout pl
      ((K2.segmentsOf A.Z A.G).take pl.link) v.x = true) :
    Plays (lettersHead h A.H (firstScriptAt I Sz Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 354 :=
  closingTestPlays_at_firstScript h hA hf test carryX item n₁ n₂ b₀ Vd Rd Kp w hh
    (closingTestTies_at_base h hA hf)
    (switch_lot_ready_at_every_closing_stand h A.H (firstScriptAt I Sz Op A cF) test carryX item n₁ n₂
      b₀ Vd Rd Kp w (makersBook_at_base h hA) (blankGround_at_base h hA) hf (widerRows Sz A.Z A.G)
      (readersB I A.Z) A.G.first.layout (K2.segmentsOf A.Z A.G) hok hpub (roundsTo cF.blocksInOrder 353))

end ProofFile.Honest.K12.LotL

#print axioms ProofFile.Honest.K12.LotL.closingTestPlays_at_base
