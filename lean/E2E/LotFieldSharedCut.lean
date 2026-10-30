-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotFieldSharedCut.lean: WHAT THE DOOR ASKS OF THE KEY FILE's SHARED CHAIN (E2E/LotFieldShared.lean), CUT TO WHAT IS LEFT AT THE MEMBERS: PlaysS at the two
proximity tests, members 9 and 10.

  noHalf_end           no half of the prover stands at the chain's end, in scope, where the two tests' halves stand at their places
  plays_of_two         PlaysS at every member of the shared chain from PlaysS at 9 and 10: member 0 by plays_quiet₂, 1 to 8 by
                       eight_at_letters (E2E/KeyStandWalked.lean), 11 by plays_seal₂ (E2E/KeyPlaysQuiet.lean)
  LotDoorAsksSharedTwo, lotDoorAsksSharedTwo   DoorAsks at 12 and the letter at the walk's start

THE PRICE: eight_at_letters' premises: fullPub = some K₀; the instance is the committer's out-of-domain sample at SOME seed sd (hx); Nm.tenant is
injective (hN); the two halves' places (pU, pO). Not needed: hKp, hE, hEnd, hC, hFits (they serve the other four debts), and hn, which is paid.
OpensShared and NoStop stay premises, as in E2E/LotFieldShared.lean. It imports nothing of IOP's.

What it does not say: as E2E/LotFieldShared.lean's head. PlaysS at 9 and 10 is paid by nobody that we know of. Nothing on soundness, completeness,
hiding or binding. No law over coins: the seed, the index and the committer's coins are letters.
-/
import E2E.LotFieldShared
import E2E.KeyPlaysQuiet
import E2E.KeyThreadFits

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.KeyStandWalked.Lots
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (TableKey)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source LaterPlaces Xi)
open _root_.Desc.K14 (St)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub foldedTestPlace omegaTestPlace)
open AtPublicFiles.KeyStandOne (startAt inK)
open AtPublicFiles.KeyStandMember (keyOf)
open AtPublicFiles.KeyFiveFields (pubKey)
open AtPublicFiles.KeyFile (KeyParts keyProver keyProver_shared)
open AtPublicFiles.KeyAsksKey (tableKey)
open AtPublicFiles.Stops (NoStop)
open AtPublicFiles.LotField (DoorAsks)
open Bind.ForProver (shapeOf oodSh Seed)

variable {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K₀ : KeyPub) (K' : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (tt : Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop)
  (f : W₀ → Weights) (g : Rc → ℕ → TableRand) (Z₀ : ProofFile.Pub)
  (w₀ : W₀) (rc : Rc) (x : Xi)

/-- **No half of the prover stands at the shared chain's end.** -/
theorem noHalf_end {Z : VerifierAndGoals.PublicFiles} (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (pU : K'.onU.place = foldedTestPlace) (pO : K'.onOmega.place = omegaTestPlace) :
    ((keyProver (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g)).shared.find? fun h =>
      h.place == (keyFileDescription Xs Nr Pl).shared.last.place) = none := by
  obtain ⟨layO, hQ⟩ := AtPublicFiles.KeySharedThread.plan_key hs scope
  have hsp : (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g).lin.S.sharedSplitNeeded = true := hQ.facts.two
  rw [List.find?_eq_none]
  intro q hq
  have hm : q.place ∈ (keyProver (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g)).shared.map (·.place) :=
    List.mem_map_of_mem hq
  rw [keyProver_shared _ hsp] at hm
  have hm' : q.place ∈ [K14.place 1, K14.sendPlace 2, K14.place 4, K14.sendPlace 5, K14.place 7,
      K14.place 8, K'.onU.place, K'.onOmega.place] := hm
  rw [pU, pO] at hm'
  have hl : (keyFileDescription Xs Nr Pl).shared.last.place = (⟨2, none, 11, .frame⟩ : Place) := rfl
  rw [hl]
  revert hm'
  generalize q.place = p
  intro hm'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm'
  rcases hm' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- **PlaysS at every member of the shared chain, from PlaysS at 9 and 10.** -/
theorem plays_of_two {Z : VerifierAndGoals.PublicFiles} (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (hK₀ : fullPub = some K₀) (sd : Seed (shapeOf (pubKey Z₀ Xs.chains)) × ℕ)
    (hx : x = ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨f w₀, g rc, sd⟩⟩)
    (hN : Function.Injective Nm.tenant)
    (pU : K'.onU.place = foldedTestPlace) (pO : K'.onOmega.place = omegaTestPlace)
    (Said : Nat → Coins (keyBook K₀) → Mid (Common W₀ Rc TableKey) X₀ → Prop)
    (h : ∀ b ∈ [9, 10],
      PlaysS (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x) Said b) :
    ∀ b, b < 12 → PlaysS (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x) Said b := by
  have hO := AtPublicFiles.KeySharedQuiet.over_key Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
    (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd (inK w₀ rc x)
  intro b hb
  by_cases h0 : b = 0
  · subst h0
    exact playsS_of _ Said (AtPublicFiles.KeyThread.plays_quiet₂ scope hs.named _ hO.bs 0 (by decide))
  by_cases h8 : b ≤ 8
  · exact (eight_at_letters Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x hs scope hK₀ sd hx
      hN pU pO Said (fun _ _ _ => none) b (by omega) h8).1
  by_cases h9 : b = 9
  · subst h9
    exact h 9 (by decide)
  by_cases h10 : b = 10
  · subst h10
    exact h 10 (by decide)
  have h11 : b = 11 := by omega
  subst h11
  have hp := AtPublicFiles.KeyThread.plays_seal₂ _ hO.bs
    (noHalf_end Xs Nr Pl K' f g Z₀ hs scope pU pO)
  rw [(AtPublicFiles.KeyThread.lengths scope hs.named).2.1] at hp
  exact playsS_of _ Said hp

/-- **What the door asks of the shared chain, with the two proximity tests left.** -/
def LotDoorAsksSharedTwo : Prop :=
  ∀ {Z : VerifierAndGoals.PublicFiles}, KeySourced Z Xs Nr Pl → VerifierAndGoals.InScope Z = true → fullPub = some K₀ →
    ∀ sd : Seed (shapeOf (pubKey Z₀ Xs.chains)) × ℕ,
    x = ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨f w₀, g rc, sd⟩⟩ →
    Function.Injective Nm.tenant →
    K'.onU.place = foldedTestPlace → K'.onOmega.place = omegaTestPlace →
    OpensShared Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x →
    NoStop (keyProver (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g)).shared →
    (∀ b ∈ [9, 10], PlaysS (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x)
      (walkedLetter Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x) b) →
    DoorAsks (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x)
        (walkedLetter Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x) 12 ∧
      ∀ k, walkedLetter Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x 0 k
        (startAt (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) (some []) (inK w₀ rc x))

theorem lotDoorAsksSharedTwo :
    LotDoorAsksSharedTwo Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x :=
  fun hs scope hK₀ sd hx hN pU pO hO hstop h =>
    lotDoorAsksShared Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x hs.named.plan hO hstop
      (plays_of_two Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x hs scope hK₀ sd hx hN pU pO
        _ h)

end AtPublicFiles.KeyStandWalked.Lots

#print axioms AtPublicFiles.KeyStandWalked.Lots.noHalf_end
#print axioms AtPublicFiles.KeyStandWalked.Lots.plays_of_two
#print axioms AtPublicFiles.KeyStandWalked.Lots.lotDoorAsksSharedTwo
