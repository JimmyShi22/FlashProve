-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyEightFive.lean: the five statements that make a sub-protocol count as accepted, at members 1 to 8 of the key
file's shared chain, from `K14Asks`, and from the five facts on the committed table and the key. At every letter
`Said` and every fall. By calls.

Why. A kind counts as accepted only with `PlaysS`, `BehindS`, `ExchangeS`, `RidesPastS` and `AcceptedS` at each of
its borders (Thread/PaysS.lean). At these eight members the library has them from one structure: `k14_asks`,
`k14_behind`. Here they are stated at the key's shared thread.

Main names.
  `eight_five`: the five at each member from `K14Asks`.
  `eight_five_sourced`: the five, from what `asks_key` (E2E/KeyAsksKey.lean) asks.

What stays open. Premises of `eight_five_sourced`: `F`: the five facts on the committed table and the key, at the
letter `Vd`. `Vd` is to say which instance: that the key is the committer's own at a seed, which a tied input gives;
the five are then proved by `five_made`, and are not laid into `Vd`. That a tied input gives `Vd` is not shown here.
`hlin`, `hsend`, `hap`: public. `hN`: the numbers' tenants are distinct. Nothing here says that the thread stands at
any run: each statement is «from the pair at this border». What the book lends at these places is another debt.

Idle letters. `Mg₀` and `Nm` may be idle at this thread, because no spender reads what stays of them: the tests at 9
and 10 take `SaysNine`, had at any `Mg₀`; the door takes `pin` at o_omega, which the thread's own words overwrite.

Nothing on soundness, completeness, hiding or binding.

-/
import E2E.KeyAsksKey
import Johnson.Desc.ProofFile.Honest.K14.Asks
import Johnson.Desc.ProofFile.Honest.Thread.PaysS

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.KeyEightFive
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (TableKey)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source LaterPlaces sharedTests keyAsProof)
open _root_.Desc.K14 (St)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeySharedThread (parKey sentKey randKey lettersKey threadKey)
open AtPublicFiles.KeyAsksKey (tableKey asks_key)

section
variable {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K₀ : KeyPub) (K : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (tt : Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop)
  (input : Common W₀ Rc TableKey)
  (Said : Nat → Coins (keyBook K₀) → Mid (Common W₀ Rc TableKey) X₀ → Prop)
  (fall : Nat → (VerifiableInference.Desc.Key.descriptionFromSource Xs Nr Pl).S₂ → List Fmt.Drawn → Option String)

/-- **The five at each of the eight, from `K14Asks`.** -/
theorem eight_five {layO : OnBytes.TreeLay}
    (h : K14Asks ℓ (lettersKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd input)
      (parKey Xs Pl) (sentKey Xs Pl) layO (keyAsProof Xs.chains) (sharedTests Pl)
      VerifiableInference.Desc.K12.Seat.last (planData (parKey Xs Pl)) K.weights (randKey K))
    (b : Nat) (h1 : 1 ≤ b) (h8 : b ≤ 8) :
    PlaysS (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd input) Said b ∧
      BehindS (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd input) Said b ∧
      ExchangeS (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd input) Said b ∧
      RidesPastS (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd input) Said
        b ∧
      AcceptedS (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd input) Said
        fall b := by
  obtain ⟨plays, -, exchange, ridesPast, accepted⟩ := k14_asks h fall b h1 h8
  have behind := k14_behind h (cs := [])
    (fun _ _ _ => ⟨fun _ _ hc => absurd hc List.not_mem_nil, fun _ => trivial⟩)
    b h1 h8 (fun _ hy => absurd hy List.not_mem_nil) (fun _ hy => absurd hy List.not_mem_nil)
  exact ⟨playsS_of _ _ plays, behindS_of _ _ behind, exchangeS_of _ _ exchange,
    ridesPastS_of _ _ ridesPast, acceptedS_of _ _ accepted⟩

/-- **The five at each of the eight, from what `asks_key` asks.** -/
theorem eight_five_sourced {Z : VerifierAndGoals.PublicFiles} (hs : KeySourced Z Xs Nr Pl)
    (scope : VerifierAndGoals.InScope Z = true) (hK₀ : fullPub = some K₀)
    (F : FiveFields (parKey Xs Pl)
      (lettersKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd input).valid
      (lettersKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd input).stored
      K.weights (randKey K))
    (hlin : K.lin = planData (parKey Xs Pl)) (hsend : K.send = ⟨parKey Xs Pl, 0⟩)
    (hap : [K14.place 1, K14.sendPlace 2, K14.place 4, K14.sendPlace 5, K14.place 7, K14.place 8,
      K.onU.place, K.onOmega.place].Nodup)
    (hN : Function.Injective Nm.tenant) (b : Nat) (h1 : 1 ≤ b) (h8 : b ≤ 8) :
    PlaysS (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd input) Said b ∧
      BehindS (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd input) Said b ∧
      ExchangeS (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd input) Said b ∧
      RidesPastS (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd input) Said
        b ∧
      AcceptedS (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd input) Said
        fall b := by
  obtain ⟨layO, h⟩ := asks_key Xs Nr Pl K₀ K ℓ Nm Mg₀ tk tt rest Kp Vd input hs scope hK₀ F hlin
    hsend hap hN
  exact eight_five Xs Nr Pl K₀ K ℓ Nm Mg₀ tk tt rest Kp Vd input Said fall h b h1 h8

end

end AtPublicFiles.KeyEightFive

#print axioms AtPublicFiles.KeyEightFive.eight_five
#print axioms AtPublicFiles.KeyEightFive.eight_five_sourced
