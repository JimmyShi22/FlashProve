-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotFieldShared.lean: THE FIELD AND ONE STATE AT THE LAST BORDER OF THE KEY FILE's SHARED CHAIN: what the last chain's door asks of the
shared chain (DoorAsks, E2E/LotFieldFirstLaw.lean), at the thread threadAt and letter walkedLetter (E2E/KeyStandWalked.lean), n = 12.
The twin of E2E/LotFieldFirst.lean: «the same is wanted of T₂ at 12». The statements are ours.

  OpensShared          A NAMED PREMISE: at every border 0 to 12 every source that a round declared so far opens is at hand, with the depth
                       that the round declares. IT DOES NOT HOLD AT EVERY tt: see below.
  LotOneShared, lotOneShared             OneStand and OneState at 12, from OpensShared ALONE: no premise on the files or on a member.
  LotDoorAsksShared, lotDoorAsksShared   DoorAsks at 12 and the letter at the walk's start, from: the description's tests on the plan,
                       OpensShared, no part of the shared chain stops, PlaysS at the members 0 to 11.
  doorAsksShared_of_owes                 the same from OwesS, the accept law's own debt at the thread, and «the thread has twelve members».

WHY OpensShared IS A PREMISE. The thread's tables are tableKey … tk tt, and tk, tt ARE FREE LETTERS of threadAt, of sharedThread
(E2E/OfflineFromChains.lean) too. DepthsAt reads the logLength of the table that the thread names at each source that a round opens;
tbKey (E2E/KeyTreesKey.lean) names «tt n» at every own tree behind the two sendings'. Some written round of the chain opens such a tree
at a depth that is not 0, so in scope, at a tt whose tables have the depth 0, OpensShared fails: opensShared_fails_somewhere
(E2E/LotFieldSharedControl.lean). WHOEVER FIXES tk, tt OWES THIS PREMISE AT THAT VALUE: at IOP's ttPlaced it is paid over IOP's trial, which is
on no row (E2E/LotOpensShared.lean); this file imports nothing of IOP's.

What it does not say. No stand of the thread at 12 is shown: where there is none, state and field are empty. PlaysS at 9 and 10 is paid by
nobody that we know of. Nothing on soundness, completeness, hiding or binding. No law over coins.
-/
import E2E.LotFieldFirstLaw
import E2E.KeyStandWalked
import E2E.KeySharedQuiet

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
open AtPublicFiles.AtFiles (keyFileDescription)
open AtPublicFiles.KeyBook (KeyPub keyBook)
open AtPublicFiles.KeyStandOne (startAt inK)
open AtPublicFiles.KeyStandMember (keyOf)
open AtPublicFiles.KeyFiveFields (pubKey)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeyAsksKey (tableKey)
open AtPublicFiles.Stops (NoStop)
open AtPublicFiles.LotField (DoorAsks doorAsks_walked enter_walked oneState_walked)

variable {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K₀ : KeyPub) (K' : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (tt : Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop)
  (f : W₀ → Weights) (g : Rc → ℕ → TableRand) (Z₀ : ProofFile.Pub)
  (w₀ : W₀) (rc : Rc) (x : Xi)

/-- **What the shared chain opens**, at every border 0 to 12: a named premise. -/
def OpensShared : Prop :=
  (∀ n, n ≤ 12 →
      (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x).opensAvailable n = true) ∧
    ∀ n, n ≤ 12 → ∀ k m,
      DepthsAt (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x) n k m

/-- **One run, one state, at the shared chain's last border.** -/
def LotOneShared : Prop :=
  OpensShared Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x →
    OneStand (walkedLetter Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x) 12 ∧
      OneState (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x)
        (walkedLetter Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x) 12

/-- **What the door asks of the shared chain.** -/
def LotDoorAsksShared : Prop :=
  (keyFileDescription Xs Nr Pl).planOk = true →
    OpensShared Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x →
    NoStop (keyProver (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g)).shared →
    (∀ b, b < 12 → PlaysS (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x)
      (walkedLetter Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x) b) →
    DoorAsks (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x)
        (walkedLetter Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x) 12 ∧
      ∀ k, walkedLetter Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x 0 k
        (startAt (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) (some []) (inK w₀ rc x))

/-- No tree is taken over by the shared chain. -/
theorem taken_shared : ∀ j, Fmt.TreeSource.own j ∉
    (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x).taken :=
  fun j hj => (List.not_mem_nil : ¬ Fmt.TreeSource.own j ∈ []) hj

/-- The chain begins at one state. -/
theorem begun_shared : ∀ k w hd s₀ s₁,
    (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x).begun k w hd s₀ →
    (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x).begun k w hd s₁ → s₀ = s₁ :=
  fun _ _ _ _ _ h h' => Eq.trans h (Eq.symm h')

theorem lotOneShared : LotOneShared Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x := by
  intro hO
  have hT := taken_shared Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x
  exact ⟨oneStand_walked (fun _ _ _ h h' _ _ => h.trans h'.symm)
      (oneColumns_of hT (fun b hb => hO.1 (b + 1) hb) fun b hb => hO.2 (b + 1) hb),
    oneState_walked hT hO.1 hO.2
      (begun_shared Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x)
      fun _ _ _ h h' _ _ => h.trans h'.symm⟩

theorem lotDoorAsksShared :
    LotDoorAsksShared Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x := by
  intro hp hO hstop hP
  exact ⟨doorAsks_walked
      (AtPublicFiles.KeySharedQuiet.fits_key Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
        (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd
        (inK w₀ rc x) hp)
      (taken_shared Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x) hO.1 hO.2
      (begun_shared Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x) hstop hP rfl,
    fun k => enter_walked _ _ k⟩

/-- **The same from OwesS**, the accept law's own debt at the thread. -/
theorem doorAsksShared_of_owes (hp : (keyFileDescription Xs Nr Pl).planOk = true)
    (hO : OpensShared Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x)
    (hstop : NoStop (keyProver (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g)).shared)
    (hlen : (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x).bs.length = 12)
    (owes : OwesS (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x)
      (walkedLetter Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x)) :
    DoorAsks (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x)
      (walkedLetter Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x) 12 :=
  (lotDoorAsksShared Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x hp hO hstop
    fun b hb => (owes b (hlen ▸ hb)).1).1

end AtPublicFiles.KeyStandWalked.Lots

#print axioms AtPublicFiles.KeyStandWalked.Lots.taken_shared
#print axioms AtPublicFiles.KeyStandWalked.Lots.begun_shared
#print axioms AtPublicFiles.KeyStandWalked.Lots.lotOneShared
#print axioms AtPublicFiles.KeyStandWalked.Lots.lotDoorAsksShared
#print axioms AtPublicFiles.KeyStandWalked.Lots.doorAsksShared_of_owes
