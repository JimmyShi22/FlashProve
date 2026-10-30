-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotMemberFourteen.lean: the two statements `LotMemberFourteen` and `LotFitsAt`,
and a proof of each.

  `LotMemberFourteen`: at member 14 of the key file's first chain, "rng.0.rows", at the thread `Th` (E2E/FirstHSeat.lean): it
    plays, what lies behind stays, the exchange holds, what rides passes, the step is accepted: each asked from `ThrS`, at
    every letter Said and every fall.
  `LotFitsAt`: `FitsAt` at members 4, 10, 14, 18.
  `readsL_baseH`: the filling's reading reads no ledger of a message (`ReadsL`).
  `halved_first`: in scope, where K bears the first chain's places: the frame's test `halved` at the first chain. It is the
    first third of the library's `halvedAll_key` (E2E/KeyLaid.lean), whose text it repeats, from `AtPlaces` alone.
  `lotMemberFourteen`, `lotFitsAt`: the two proofs.

Limits.
- `ThrS (Th …) Said 14`, the premise inside all five, IS MET BY NOTHING YET: nothing shows that `Th` stands at border 14 at any
  run. It hangs on the chain's start and on the debts at members 0 to 13. Where it stands nowhere (so at Q.Rel false) the
  five are empty.
- `MembersS` asks `SaidNext` at 14 beside the five: it is not in the lot and not here.
- Four of the five are calls of the library; the new content is `grows_of_rows` and `grows_behind` (E2E/LotMemberFourteenGrows.lean).
- The letters K, f, Q, w₀, rc, x, K₀, Said and fall stay free. Q.kind₁ at 14 is not read: the thread's clause `keeps` has its own
  text there (`eq₁`, E2E/KeyKeepsEq.lean). Member 14 has no round: nothing is said of what any half of K sends.
- The premise fullPub = some K₀ is spent by neither proof; of `FirstPublic` the field `places` alone is spent, by `lotFitsAt`.
  No file that this one stands on shows a member of `FirstPublic`.
- `FitsAt` speaks of form alone, and from `Thread.Moved`: that `chainSteps`, `play` and the filling of the columns return is
  its premise. It says nothing on whether a decision returns. The proof gives it at every member, not at the four alone.
- The written sizes alone: in scope, at a sourced description.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.FirstHSeat
import E2E.FirstHSeats
import Johnson.Desc.ProofFile.Honest.Thread.PaysS
import E2E.LotMemberFourteenGrows
import E2E.KeyLaid
import Johnson.Desc.ProofFile.Honest.Thread.FitsAll

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.FirstH.Lots
open OnBytes OnBytes.Params
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces)
open AtPublicFiles.KeyFile (KeyParts In1)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest

section
variable {W₀ Rc X₀ X' Wk : Type} (K₀ : KeyPub) (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces)
  (K : KeyParts W₀ Rc X₀ X' Wk) (f : W₀ → Weights) (Q : LaterFill (keyBook K₀) W₀ Rc) (w₀ : W₀)
  (rc : Rc) (x : Xi)

/-- **The five at member 14.** -/
def LotMemberFourteen : Prop :=
  ∀ {Z : PublicFiles}, KeySourced Z Xs N Pl → InScope Z = true → fullPub = some K₀ →
    FirstPublic (Pl := Pl) Xs N K f →
    ∀ (Said : Nat → Coins (keyBook K₀) → Mid (In1 W₀ Rc) X' → Prop)
      (fall : Nat → FirstState → List Fmt.Drawn → Option String),
      PlaysS (Th Xs N Pl K f Q w₀ rc x) Said 14 ∧ BehindS (Th Xs N Pl K f Q w₀ rc x) Said 14 ∧
        ExchangeS (Th Xs N Pl K f Q w₀ rc x) Said 14 ∧ RidesPastS (Th Xs N Pl K f Q w₀ rc x) Said 14 ∧
        AcceptedS (Th Xs N Pl K f Q w₀ rc x) Said fall 14

/-- **The fits.** -/
def LotFitsAt : Prop :=
  ∀ {Z : PublicFiles}, KeySourced Z Xs N Pl → InScope Z = true → fullPub = some K₀ →
    FirstPublic (Pl := Pl) Xs N K f → ∀ b ∈ [4, 10, 14, 18], FitsAt (Th Xs N Pl K f Q w₀ rc x) b

end

/-- The filling's reading reads no ledger of a message. -/
theorem readsL_baseH (one : OneTime) : Johnson.RunOne.KeyRows1.ReadsL (baseH one).h₁ :=
  Johnson.RunOne.KeyRows1.readsL_h₁ (baseH one) fun _ _ _ _ => rfl

section
open AtPublicFiles.KeyLink (halved_sealed)
open AtPublicFiles.KeyBook
open AtPublicFiles.KeyFile (keyProver first_places)
open AtPublicFiles.AtFiles (KeyNamed keyFileDescription)

/-- **In scope a half of `keyProver K` stands at every sub-protocol of the first chain that sends**, where K bears that
chain's places. -/
theorem halved_first {W₀ Rc X₀ X' Wk : Type} {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums}
    {Pl : LaterPlaces} (scope : InScope Z = true) (h : KeyNamed Z Xs N Pl)
    (K : KeyParts W₀ Rc X₀ X' Wk) (hK : K.AtPlaces) :
    halved (keyFileDescription Xs N Pl).first.blocksInOrder (keyProver K).first = true := by
  have r1 := (places_named scope h).1
  have e1 : fullFirst = ([(idxPlace, 2), (msgPlace, 2)] ++ linkRows 0 9581 ++ linkRows 1 9220 ++
      [(rowsPlace, 0), (rngPlace, 23), (battPlace, 20), (wPlace, 2)]) ++ [(sealPlace, 1)] := by
    decide
  exact halved_sealed _ _ _ _ (r1.trans e1) rfl (by
    rw [first_places K hK]
    decide)

end

section
variable {W₀ Rc X₀ X' Wk : Type} (K₀ : KeyPub) (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces)
  (K : KeyParts W₀ Rc X₀ X' Wk) (f : W₀ → Weights) (Q : LaterFill (keyBook K₀) W₀ Rc) (w₀ : W₀)
  (rc : Rc) (x : Xi)

/-- **The five at member 14: proved.** -/
theorem lotMemberFourteen : LotMemberFourteen K₀ Xs N Pl K f Q w₀ rc x := by
  intro Z hs scope _ _ Said fall
  exact five14 Xs N Pl (fillH Xs N Pl K f Q x) w₀ rc x hs scope (readsL_baseH _) Said fall

/-- **The fits: proved.** -/
theorem lotFitsAt : LotFitsAt K₀ Xs N Pl K f Q w₀ rc x := by
  intro Z hs scope _ hp b _
  exact fitsAt_of_halved (Th Xs N Pl K f Q w₀ rc x) (halved_first scope hs.named K hp.places) b

end

end AtPublicFiles.FirstH.Lots

#print axioms AtPublicFiles.FirstH.Lots.readsL_baseH
#print axioms AtPublicFiles.FirstH.Lots.halved_first
#print axioms AtPublicFiles.FirstH.Lots.lotMemberFourteen
#print axioms AtPublicFiles.FirstH.Lots.lotFitsAt
