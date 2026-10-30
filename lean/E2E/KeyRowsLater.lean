--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyRowsLater.lean: FOUR WHOLE ROWS OF THE KEY FILE's LATER CHAINS: at the shared chain's front
and end (numbers 0 and 11) and at the last chain's test on the taken trees' sources and its end
(numbers 1 and 3): ALL FOUR DEBTS OF A SUB-PROTOCOL (`PlaysS`, `BehindS`, `ExchangeS`, `RidesPastS`:
Johnson/Desc/ProofFile/Honest/Thread/PaysS.lean), from the pair, at any shared or last thread that
brings what a row names, and at any letter for what is said of the prover's run: in scope. And the first chain's exchange at
three sub-protocols, from the pair. By calls.
NOTHING IS SHOWN OF ANY PROVER.

  **`row_front₂`**, **`row_seal₂`**: the shared chain's two; the second where no half stands at the
      end's place
  **`row_sources₃`**, **`row_end₃`**: the last chain's two
  **`exchangeS_of_anew₁`**: `ExchangeS` at the numbers 5, 11 and 14 of the first chain is owed for
      what the row makes anew alone, AND THAT MAY BE PAID FROM THE PAIR: whoever pays it may spend
      what is said of the prover's run (E2E/KeyOwedAgain.lean has the like from the thread alone)

What each clause is paid by: the play: these four have no round but the shared chain's end, whose
one round is the sealing round (E2E/KeyPlaysQuiet.lean). The other three are premises, so these
rows carry them: at `threadKey` E2E/KeySharedQuiet.lean, at `lettersLastKey` E2E/KeyLastQuiet.lean
state them under named premises; at `laid₃`, `behind₃` and `ridesPast₃` stand.

Limits.
- THE PLAY AND THE EXCHANGE ARE EMPTY AT THESE FOUR: nothing is sent and nothing is owed: the
  content is what holds behind the yes, and the riders.
- That such a sub-protocol ACCEPTS is another debt: at the shared chain's front:
  E2E/KeySharedStands.lean.
- Each is true also where the thread holds at nothing.

-/
import E2E.KeyBehind
import E2E.KeyBehind3
import E2E.KeyRidesSame
import E2E.KeyOwedAgain
import E2E.KeyPlaysQuiet
import E2E.KeyExchangeEmpty
import Johnson.Desc.ProofFile.Honest.Thread.PaysS

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyThread
open VerifiableInference.Desc.Key (Xi Source LaterPlaces rows₂ rows₃)
open Johnson.RunOne.KeyRows1 (ReadsL)
open ProofFile.Honest

variable {Bk : ProverCoinCounts} {W₀ Rc Cells M Smp Rec X' : Type} (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (L : KeyFill Bk W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
  {hs₁ : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X')}
  {tb₁ : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table}
  {hs₂ : List (Placed Empty (Common W₀ Rc OnBytes.TableKey) X')}
  {tb₂ : Fmt.TreeSource → Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table}
  {hs₃ : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X')}
  {tb₃ : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table}
  {Z : VerifierAndGoals.PublicFiles}

/-- **The row at the shared chain's front.** -/
theorem row_front₂ (hs : AtPublicFiles.AtFiles.KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true)
    (U : Thread Bk (D Xs N Pl).S₂ (D Xs N Pl).Cl Empty (Common W₀ Rc OnBytes.TableKey) X'
      OnBytes.TableKey)
    (hO : OverShared Xs N Pl U) (hQ : QuietEnds₂ U) (ho : (U.row 0).owes = [])
    (hr : RidesPast U 0)
    (S₂ : Nat → Coins Bk → Mid (Common W₀ Rc OnBytes.TableKey) X' → Prop) :
    PlaysS U S₂ 0 ∧ BehindS U S₂ 0 ∧ ExchangeS U S₂ 0 ∧ RidesPastS U S₂ 0 :=
  ⟨playsS_of _ _ (plays_quiet₂ scope hs.named U hO.bs 0 (by decide)),
    behindS_of _ _ (behind₂ Xs N Pl hs scope hO hQ 0 (by decide)),
    exchangeS_of _ _ (exchange_of_nil _ ho),
    ridesPastS_of _ _ hr⟩

/-- **The row at the shared chain's end.** -/
theorem row_seal₂ (hs : AtPublicFiles.AtFiles.KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true)
    (U : Thread Bk (D Xs N Pl).S₂ (D Xs N Pl).Cl Empty (Common W₀ Rc OnBytes.TableKey) X'
      OnBytes.TableKey)
    (hO : OverShared Xs N Pl U) (hQ : QuietEnds₂ U) (ho : (U.row 11).owes = [])
    (hr : RidesPast U 11)
    (hn : (U.hs.find? fun g => g.place == (D Xs N Pl).shared.last.place) = none)
    (S₂ : Nat → Coins Bk → Mid (Common W₀ Rc OnBytes.TableKey) X' → Prop) :
    PlaysS U S₂ 11 ∧ BehindS U S₂ 11 ∧ ExchangeS U S₂ 11 ∧ RidesPastS U S₂ 11 := by
  have hp := plays_seal₂ U hO.bs hn
  rw [(lengths scope hs.named).2.1] at hp
  exact ⟨playsS_of _ _ hp, behindS_of _ _ (behind₂ Xs N Pl hs scope hO hQ 11 (by decide)),
    exchangeS_of _ _ (exchange_of_nil _ ho), ridesPastS_of _ _ hr⟩

/-- **The row at the last chain's test on the taken trees' sources.** -/
theorem row_sources₃ (hs : AtPublicFiles.AtFiles.KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true)
    (U₃ : Thread Bk (D Xs N Pl).S₃ (D Xs N Pl).Cl (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X' Xi)
    (hbs : U₃.bs = (D Xs N Pl).second.blocksInOrder) (hB : Behind U₃ 1) (ho : (U₃.row 1).owes = [])
    (hr : RidesPast U₃ 1) (S₃ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Unit) X' → Prop) :
    PlaysS U₃ S₃ 1 ∧ BehindS U₃ S₃ 1 ∧ ExchangeS U₃ S₃ 1 ∧ RidesPastS U₃ S₃ 1 :=
  ⟨playsS_of _ _ (plays_quiet₃ scope hs.named U₃ hbs 1 (by decide)),
    behindS_of _ _ hB,
    exchangeS_of _ _ (exchange_of_nil _ ho),
    ridesPastS_of _ _ hr⟩

/-- **The row at the last chain's end.** -/
theorem row_end₃ (hs : AtPublicFiles.AtFiles.KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true)
    (U₃ : Thread Bk (D Xs N Pl).S₃ (D Xs N Pl).Cl (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X' Xi)
    (hbs : U₃.bs = (D Xs N Pl).second.blocksInOrder) (hB : Behind U₃ 3) (ho : (U₃.row 3).owes = [])
    (hr : RidesPast U₃ 3) (S₃ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Unit) X' → Prop) :
    PlaysS U₃ S₃ 3 ∧ BehindS U₃ S₃ 3 ∧ ExchangeS U₃ S₃ 3 ∧ RidesPastS U₃ S₃ 3 :=
  ⟨playsS_of _ _ (plays_quiet₃ scope hs.named U₃ hbs 3 (by decide)),
    behindS_of _ _ hB,
    exchangeS_of _ _ (exchange_of_nil _ ho),
    ridesPastS_of _ _ hr⟩

/-- **The first chain's exchange at three sub-protocols, from the pair.** -/
theorem exchangeS_of_anew₁ (hs : AtPublicFiles.AtFiles.KeySourced Z Xs N Pl)
    (scope : VerifierAndGoals.InScope Z = true) (hG : ReadsL L.base.h₁)
    (S₁ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Unit) X' → Prop) : ∀ b ∈ [5, 11, 14],
    (∀ blk, (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁).bs[b]? = some blk → ∀ k s m E ds y cols s',
      ThrS (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) S₁ b k s m E → drawsFit blk.rounds ds = true →
      (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁).Stepped blk k s m E ds y cols s' →
      (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁).Items (anew b) k s' y.2 (E.add y.1)) →
    ExchangeS (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) S₁ b := by
  intro b hb hnew blk hblk k s m E ds y cols s' hT hd hS ds' i hi
  rcases (owes_split b hb).1 i hi with h | h
  · exact hnew blk hblk k s m E ds y cols s' hT hd hS ds' i h
  · exact items_again₁ Xs N Pl L w₀ rc x hs scope hG b hb blk hblk k s m E ds y cols s' hT.1 hS
      ds' i h

end AtPublicFiles.KeyThread

#print axioms AtPublicFiles.KeyThread.row_front₂
#print axioms AtPublicFiles.KeyThread.row_seal₂
#print axioms AtPublicFiles.KeyThread.row_sources₃
#print axioms AtPublicFiles.KeyThread.row_end₃
#print axioms AtPublicFiles.KeyThread.exchangeS_of_anew₁
