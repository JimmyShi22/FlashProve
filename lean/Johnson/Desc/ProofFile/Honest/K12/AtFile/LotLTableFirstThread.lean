-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLTableFirstThread.lean

It states no goal. No property of the protocol is claimed.

LotLTableFirstScript.lean's FIVE TOPS
AT THE FIRST THREAD AT A RETURN OF THE MAKER (`firstThread`, Honest/Thread/TheFirstThread.lean)
WHOSE SCRIPT IS THE FIRST CHAIN's SCRIPT AT THE BASE PROVER (`firstScriptAt`,
AtFullSide/K1/FirstScript.lean). Five statements; each proof is one call:
`firstThread` is `lettersHead`'s thread at written letters by unfolding (`firstThread_is`).

  `closingTestTable_at_firstThread`   the thread's table at own 77 + τ is the test's, as a function
  `closingTestFixed_at_firstThread`   its fixed number
  `finishTable_at_firstThread`        the thread's table and fixed number at own 76
  `closingTestOldOpenings_at_firstThread`   at a stand every old tree that the test's rounds open is at
                                      hand with the declared width, from hready
  `closingTestPlays_at_firstThread`   `Plays` at member 354, from hh, hT, hready

Hypotheses. h: the head at the return. hA: the maker returns A at the filling
`onlineProverPartsInUse I secondHashFunction Sz Op`. hf: the code switch's finish. numbers, w: letters. hready, hh, hT: as in LotLTableFirstScript.lean.

Limits. Those of LotLTableFirstScript.lean. hready IS A PREMISE ON EVERY STAND. That a stand is reached
is not said. Nothing on completeness of the chain, soundness or hiding.

NOT IN FRONT OF A LAW OVER COINS: `closingTestOldOpenings_at_firstThread` and
`closingTestPlays_at_firstThread` bear this label; the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean.
This file's own ground, in the rule's terms.
- h (the head at a return of the maker) and hA speak of the public files, of the letters I and Op
  (how an index, an instance and the challenges are read, and one named member of the index's type)
  and of what the maker returns at the filling made of them. By their text they name no coin, no
  run's input (its index, its trace) and no Script: of neither kind.
- hf, hh and hT speak of the finish, of the prover's side that the search finds at the test's place
  and of the book's entries: they name no coin.
- hready is itself bound over all coins and every stand: by itself it picks among no coins.
- w, the run's input, is a letter under no premise in front. It holds the committer's coins (its
  field rc) and the hidden input (its fields w₀ and trace).
- numbers (the stated numbers of the falls) is a letter under no premise.
- A run's coins k are bound inside each end. Beside k the first binds the letters st, m and E (the
  verifier's state, the state of the prover's side, the available tables) under `Thr … 354 k st m
  E`, and the second, through `Plays`, s, m and E under the same: a premise of the first kind: it
  names k; by its text, at a fixed state, m and E it can hold at some values of the coins and fail
  at others.
- `Plays` | `PlaysS` binds besides l under `chainSteps … (k.look T.chain) … = .ok l`: of the first
  kind.
- ds, the challenges, stands under `drawsFit` (no coin) and under `chainStopAt (T.φ.sees m.st.input)
  …`: no run's coin is among its arguments (`Part.stopAt`, Honest/Side.lean), but in the first chain
  the face shows a part's second stop the whole input of m (`Face.sees`, Honest/Frame.lean), which
  holds rc and the hidden input: of the first kind as far as such a stop reads rc, of the second as
  far as it reads the index or the trace; what the parts at 354 read is not fixed here.
- One clause of the invariant is of the second kind: the thread's `valid` says that the input of m
  is w and meets `ReadyInput` (Honest/Thread/ReadyInput.lean): the instance passes the description's
  test, the index is in range, the trace is the prover's own: it reads the hidden input and no coin.
- The other theorems of this file tie no letter to a coin: where k stands in them it is bound inside
  an equation of functions. They bear none.
- What lifts the bar: for the state, m, E and l the made terms would be those of the honest run at
  the border, as terms of w, k and the challenges, and the lemma would show the premises at them at
  every value of the coins. For ds, which no term of the prover's makes, the lemma would show that
  at each ds `chainStopAt … = none` holds at every value of rc or at none. None is known to this
  file: the bar is flat.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLTableFirstScript
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open ProofFile.Honest.FirstThread (HeadAtReturn FallNumbers firstThread)
open ProofFile.Honest.K1 (LocB firstScriptAt readersB closingB)
open ProofFile.Honest.K12.AtProof (jobL doorAtL finishAt)
open ProofFile.Honest.K2.Law (SwitchCoins)
open P5J (TS)

variable {W₀ : Type} {files : VerifierAndGoals.PublicFiles} {I : WiderIn W₀} {Sz : OnBytes.HonestTrace.Sz} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {pl : K2.SwitchPlace}

/-- **The table of the test's tree number τ, at the first thread.** -/
theorem closingTestTable_at_firstThread (h : HeadAtReturn files A)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction Sz Op) = .ok A)
    (hf : finishAt A.Z A.G = some pl) (numbers : FallNumbers) (w : LocB W₀) :
    ∀ τ, τ + 1 < (H2U.p12OfMade A.Z.made).nums.stages.length →
      (firstThread h ⟨firstScriptAt I Sz Op A h.firstChain, numbers⟩ w).table
          (.own (treesTo h.firstChain.blocksInOrder 354 + τ)) =
        testTbl (firstThread h ⟨firstScriptAt I Sz Op A h.firstChain, numbers⟩ w).chain
          (jobL (H2U.p12OfMade A.Z.made) (doorAtL A.Z) (widerRows Sz A.Z A.G) (readersB I A.Z)
            (closingB A.Z A.G) pl) ()
          ((firstThread h ⟨firstScriptAt I Sz Op A h.firstChain, numbers⟩ w).front +
            roundsTo h.firstChain.blocksInOrder 354) (fun _ _ _ => true) τ :=
  closingTestTable_at_firstScript h.head hA hf _ _ _ _ _ _ _ _ _ w

/-- **Its fixed number, at the first thread.** -/
theorem closingTestFixed_at_firstThread (h : HeadAtReturn files A)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction Sz Op) = .ok A)
    (hf : finishAt A.Z A.G = some pl) (numbers : FallNumbers) (w : LocB W₀) :
    ∀ τ, τ + 1 < (H2U.p12OfMade A.Z.made).nums.stages.length →
      (firstThread h ⟨firstScriptAt I Sz Op A h.firstChain, numbers⟩ w).fixed
          (.own (treesTo h.firstChain.blocksInOrder 354 + τ)) =
        (firstThread h ⟨firstScriptAt I Sz Op A h.firstChain, numbers⟩ w).front +
            roundsTo h.firstChain.blocksInOrder 354 +
          seedRound (H2U.p12OfMade A.Z.made).nums.stages τ :=
  closingTestFixed_at_firstScript h.head hA hf _ _ _ _ _ _ _ _ _ w

/-- **The tree that the test opens, own 76, at the first thread.** -/
theorem finishTable_at_firstThread (h : HeadAtReturn files A)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction Sz Op) = .ok A)
    (hf : finishAt A.Z A.G = some pl) (numbers : FallNumbers) (w : LocB W₀) :
    (firstThread h ⟨firstScriptAt I Sz Op A h.firstChain, numbers⟩ w).table (.own 76) =
      (fun k v hd => (pl.place, K2.switchTableAt A.B 0 (K2.coreSender K2.freshTable)
        (widerRows Sz A.Z A.G) (readersB I A.Z) (closingB A.Z A.G) pl k v hd 0)) ∧
    (firstThread h ⟨firstScriptAt I Sz Op A h.firstChain, numbers⟩ w).fixed (.own 76) =
      roundsTo h.firstChain.blocksInOrder 353 ∧
    roundsTo h.firstChain.blocksInOrder 353 = 48235 :=
  finishTable_at_firstScript h.head hA hf _ _ _ _ _ _ _ _ _ w

/-- **The old openings at a stand of the first thread**, from hready. -/
theorem closingTestOldOpenings_at_firstThread (h : HeadAtReturn files A)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction Sz Op) = .ok A)
    (hf : finishAt A.Z A.G = some pl) (numbers : FallNumbers) (w : LocB W₀)
    (hready : ∀ k st m E, Thr (firstThread h ⟨firstScriptAt I Sz Op A h.firstChain, numbers⟩ w) 354 k st m E →
      ∃ c : SwitchCoins pl.sizes pl.others pl.foldVars pl.carries, K2.handed 0 pl k = some c ∧
        ∃ V : ℕ → Johnson.Prover.Send.Rows, K2.switchRowsLaid (widerRows Sz A.Z A.G) (readersB I A.Z)
          (closingB A.Z A.G) pl c m.st.input
          (m.st.heard.take (roundsTo h.firstChain.blocksInOrder 353)) = .ok V) :
    ∀ k st m E, Thr (firstThread h ⟨firstScriptAt I Sz Op A h.firstChain, numbers⟩ w) 354 k st m E →
      ∀ d ∈ (proximityTestKind guardedProximityTestParts (H2U.p12OfMade A.Z.made) : Block T12 Unit).rounds,
        ∀ o ∈ d.opens, oldSrc E.sent o.2 = true → ∃ pt, E.tree o.2 = some pt ∧ pt.2.words = o.1.W :=
  closingTestOldOpenings_at_firstScript h.head hA hf _ _ _ _ _ _ _ _ _ w hready

/-- **`Plays` at the closing test, at the first thread.** -/
theorem closingTestPlays_at_firstThread (h : HeadAtReturn files A)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction Sz Op) = .ok A)
    (hf : finishAt A.Z A.G = some pl) (numbers : FallNumbers) (w : LocB W₀)
    (hh : (A.H.first.find? fun g => g.place == (H2U.p12OfMade A.Z.made).place) =
      some (proverSideOfProximityTest (jobL (H2U.p12OfMade A.Z.made) (doorAtL A.Z) (widerRows Sz A.Z A.G) (readersB I A.Z)
                             (closingB A.Z A.G) pl)))
    (hT : tiesB A.B (H2U.p12OfMade A.Z.made).place (AtProof.membersL pl).length = true)
    (hready : ∀ k st m E, Thr (firstThread h ⟨firstScriptAt I Sz Op A h.firstChain, numbers⟩ w) 354 k st m E →
      ∃ c : SwitchCoins pl.sizes pl.others pl.foldVars pl.carries, K2.handed 0 pl k = some c ∧
        ∃ V : ℕ → Johnson.Prover.Send.Rows, K2.switchRowsLaid (widerRows Sz A.Z A.G) (readersB I A.Z)
          (closingB A.Z A.G) pl c m.st.input
          (m.st.heard.take (roundsTo h.firstChain.blocksInOrder 353)) = .ok V) :
    Plays (firstThread h ⟨firstScriptAt I Sz Op A h.firstChain, numbers⟩ w) 354 :=
  closingTestPlays_at_firstScript h.head hA hf _ _ _ _ _ _ _ _ _ w hh hT hready

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.closingTestTable_at_firstThread
#print axioms ProofFile.Honest.K12.closingTestFixed_at_firstThread
#print axioms ProofFile.Honest.K12.finishTable_at_firstThread
#print axioms ProofFile.Honest.K12.closingTestOldOpenings_at_firstThread
#print axioms ProofFile.Honest.K12.closingTestPlays_at_firstThread
