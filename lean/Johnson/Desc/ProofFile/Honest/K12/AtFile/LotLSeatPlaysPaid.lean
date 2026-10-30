-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLSeatPlaysPaid.lean

It states no goal. No property of the protocol is claimed.

`Plays` at the first chain's closing
proximity test (member 354) with no premise left but the head and the maker's return: the three named
premises of `closingTestPlays_at_base` (LotLSeatPlays.lean) paid by calls; and the corollary at the
library's value of the first thread (`firstThread`, Honest/Thread/TheFirstThread.lean) at the first
chain's Script as a value (`firstScriptAt`, AtFullSide/K1/FirstScript.lean).

  `closingTestSide_at_base`        hh: the side that the search finds at the test's place
  `closingTestPlays_at_ref`        at `Sz.ref`, at any letters of `lettersHead` whose Vd implies `okStart`
  `closingTestPlays_at_firstThread_paid`   at `firstThread h ⟨firstScriptAt I Sz.ref Op A h.firstChain, numbers⟩ w`

By what. `L_found` (AtFullSide/K12/LettersFoundL.lean), `p12OfMade_place`
(Johnson/Loose/H2K12/SitsInPure.lean); `closing_test_passes_at_finish` (LotLOwedClosed.lean);
`closing_public_at_valid` (LotLPublicClosing.lean); `finish_at_base` (AtFullSide/K1/FirstScript.lean);
`ReadyInput`'s first clause (Honest/Thread/ReadyInput.lean).

Hypotheses. h: the head (in the last: the head at a return of the maker). hA: the maker returns A at
the base prover's filling at `Sz.ref`. hV (the second): an input that the thread calls valid has an
instance that passes `okStart`.

Limits.
- The full size, the format's second hash function and the sizes `Sz.ref` alone.
- `Plays` speaks of stands of the thread; that a stand is reached is not said.
- That the test accepts what is played is not said here.
- That the head can be met together with hA is not shown here.
- The rows beneath are heavy: AtFullSide/K12/StatedAtHeadW.lean (under `L_found`) and the files on
  the closing (under `closing_test_passes_at_finish`).
- K2/Law/ClosingAtHead.lean and the files beneath it lie beneath this file.
- At the base prover's filling's return, at its own type of random values: NOT AT THE ONLINE PROVER,
  whose filling reads this one through the coins' map.
- The statements at the maker's return are typed at `OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit`: they cannot
  even be written at the online prover's return (`OnlineProverWithDescription FullSizeMatrix (protocolAtFiles files).EncodingRandomness Cells Unit Unit`,
  E2E/TheHonestProver.lean): no law through `OnlineProverParts.through` is made here.
- Nothing on completeness of the chain, soundness or hiding.

NOT IN FRONT OF A LAW OVER COINS: `closingTestPlays_at_ref` and
`closingTestPlays_at_firstThread_paid` bear this label; the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean.
This file's own ground, in the rule's terms.
- h and hA speak of the public files, of the letters I and Op (how an index, an instance and the
  challenges are read, and one named member of the index's type) and of what the maker returns at
  the filling made of them. By their text they name no coin, no run's input (its index, its trace)
  and no Script: of neither kind.
- hV (of the first) is bound over every input that meets Vd and reads its instance: it names no
  coin.
- w, the run's input, is a letter under no premise in front. It holds the committer's coins (its
  field rc) and the hidden input (its fields w₀ and trace).
- numbers (the stated numbers of the falls), in the second, is a letter under no premise.
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
- One clause of the invariant says that the input of m is w and meets the thread's `valid`: in the
  first the letter Vd, a letter for a predicate on the input; in the second `ReadyInput`
  (Honest/Thread/ReadyInput.lean): the instance passes the description's test, the index is in
  range, the trace is the prover's own: of the second kind: it reads the hidden input and no coin.
- `closingTestSide_at_base` names no coin: it bears none.
- What lifts the bar: for s, m, E and l the made terms would be those of the honest run at the
  border, as terms of w, k and the challenges, and the lemma would show the premises at them at
  every value of the coins. For ds, which no term of the prover's makes, the lemma would show that
  at each ds `chainStopAt … = none` holds at every value of rc or at none. None is known to this
  file: the bar is flat.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLSeatPlays
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLOwedClosed
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLPublicClosing
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread
import AtFullSide.K12.LettersFoundL

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K12.LotL
open VerifiableInference.Desc (Block Chain Place Strs)
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz)
open ProofFile.Honest.FirstThread (lettersHead WtF HeadAtReturn FallNumbers firstThread)
open ProofFile.Honest.K1 (LocB firstScriptAt readersB closingB finish_at_base)
open ProofFile.Honest.K12.AtProof (finishAt jobL doorAtL placeL closing_test_passes_at_finish
  closing_public_at_valid)
open P5J (AtMgA TS F0T)

section
variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {I : WiderIn W₀} {Sz : OnBytes.HonestTrace.Sz} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {pl : K2.SwitchPlace}

/-- **hh: the side that the search finds at the test's place is the pair of the lot's job.** -/
theorem closingTestSide_at_base (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction Sz Op) = .ok A)
    (hf : finishAt A.Z A.G = some pl) :
    (A.H.first.find? fun g => g.place == (H2U.p12OfMade A.Z.made).place) =
      some (proverSideOfProximityTest (jobL (H2U.p12OfMade A.Z.made) (doorAtL A.Z) (widerRows Sz A.Z A.G)
                         (readersB I A.Z) (closingB A.Z A.G) pl)) := by
  obtain ⟨pl', hf', hs⟩ := AtFullSide.K12.L_found h I Sz Op hA
  obtain rfl : pl' = pl := Option.some.inj (hf'.symm.trans hf)
  have hp : (H2U.p12OfMade A.Z.made).place = placeL := H2K.JointK.p12OfMade_place A.Z
  rw [hp]
  exact hs

end

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {I : WiderIn W₀} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- hV IS A PREMISE ON THE LETTER Vd. **`Plays` at the closing test, at the base prover's thread at
`Sz.ref`.** -/
theorem closingTestPlays_at_ref (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref Op) = .ok A)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : LocB W₀ → Prop) (Rd : Nat → LocB W₀ → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : LocB W₀)
    (hV : ∀ v, Vd v → (F0T OnBytes.secondHashFunction A.Z Np cF).okStart v.x = true) :
    Plays (lettersHead h A.H (firstScriptAt I Sz.ref Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 354 := by
  obtain ⟨pl, hf⟩ := finish_at_base h hA
  exact closingTestPlays_at_base h hA hf test carryX item n₁ n₂ b₀ Vd Rd Kp w
    (closingTestSide_at_base h hA hf)
    (closing_test_passes_at_finish h.toAtMg (blankGround_at_base h hA) hf)
    (closing_public_at_valid h (blankGround_at_base h hA) hf Vd hV)

/-- **`Plays` at the closing test, at the library's first thread at the first chain's Script.** -/
theorem closingTestPlays_at_firstThread_paid {files : VerifierAndGoals.PublicFiles} (h : HeadAtReturn files A)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref Op) = .ok A)
    (numbers : FallNumbers) (w : LocB W₀) :
    Plays (firstThread h ⟨firstScriptAt I Sz.ref Op A h.firstChain, numbers⟩ w) 354 :=
  closingTestPlays_at_ref h.head hA _ _ _ _ _ _ _ _ _ w fun _ hv => hv.1

end ProofFile.Honest.K12.LotL

#print axioms ProofFile.Honest.K12.LotL.closingTestSide_at_base
#print axioms ProofFile.Honest.K12.LotL.closingTestPlays_at_ref
#print axioms ProofFile.Honest.K12.LotL.closingTestPlays_at_firstThread_paid
