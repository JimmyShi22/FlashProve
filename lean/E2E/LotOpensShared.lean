-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotOpensShared.lean: THE NAMED PREMISE OpensShared (E2E/LotFieldShared.lean) PAID AT tt := IOP's ttPlaced, in the goals' scope: at every border
0 to 12 of the key file's shared thread every source that a round declared so far opens is at hand, with the depth that the round declares.

  ttShared             (its text: E2E/LotLetters.lean) the value of the letter tt: IOP's ttPlaced K₀ (JKU AQ bs st wts rnd) (JKO AQ bs wts rnd) own₀ (t7K K₀ bs wts rnd own₀)
                       (E2E/KeyDepthsAt.lean, KeyDepthsClosed.lean); bs, st, wts, rnd, own₀ stay letters, tk too
  LotOpensShared, lotOpensShared   OpensShared at it, under KeySourced, InScope, fullPub = some K₀
  LotOneSharedPlaced, lotOneSharedPlaced   so OneStand and OneState at 12 there, with no other premise

IT STANDS ON E2E/KeyOpensAll.lean (opens_key_all, depths_key_all) and nineteen files beneath it, laid
as copies.
By what: the places are the written ones (later_sourced) and the linear claim's parameters are QK (par_sourced), so the thread's table
tbKey (parKey Xs Pl) … is IOP's tbPlaced = tbKey QK ….

Limits. logLength alone: nothing on what a table holds; that ttShared's tables are what the two tests' halves send is PlaysS's matter at 9 and 10.
bs, st, wts, rnd, own₀ are free: nothing ties them to the prover's own halves here. Nothing on soundness, completeness, hiding or binding.
-/
import E2E.LotLetters
import E2E.LotFieldShared
import E2E.KeyOpensAll
import E2E.KeyShapeSharedTies

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace AtPublicFiles.KeyStandWalked.Lots
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (TableKey)
open VerifiableInference.Desc (Place Block)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source LaterPlaces Xi)
open _root_.Desc.K14 (St)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.AtFiles.Full (PF QK par_sourced later_sourced)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeySharedThread (threadKey parKey)
open AtPublicFiles.KeyStandOne (inK)
open AtPublicFiles.KeyStandMember (keyOf)
open AtPublicFiles.KeyFiveFields (pubKey)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeyAsksKey (tableKey)
open AtPublicFiles.KeyTreesKey (tbKey)
open AtPublicFiles.KeyDepthsAt (ttPlaced)
open AtPublicFiles.KeyDepthsClosed (AQ t7K tbPlaced)
open AtPublicFiles.KeyOpensAll (opens_key_all depths_key_all)
open AtPublicFiles.KeyLay (JKU JKO)

variable {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K₀ : KeyPub) (K' : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop)
  (f : W₀ → Weights) (g : Rc → ℕ → TableRand) (Z₀ : ProofFile.Pub)
  (w₀ : W₀) (rc : Rc) (x : Xi)
  (bs : List (Block St Unit)) (st : W₀ → Rc → ℕ → ℕ → Option (List UInt64))
  (wts : Common W₀ Rc TableKey → Weights) (rnd : Common W₀ Rc TableKey → TableRand) (own₀ : X₀)

/-- **What the shared chain opens, at that value.** -/
def LotOpensShared : Prop :=
  ∀ {Z : VerifierAndGoals.PublicFiles}, KeySourced Z Xs Nr Pl → VerifierAndGoals.InScope Z = true → fullPub = some K₀ →
    OpensShared Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk (ttShared K₀ bs st wts rnd own₀) rest Kp Vd f g Z₀ w₀ rc x

theorem lotOpensShared :
    LotOpensShared Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk rest Kp Vd f g Z₀ w₀ rc x bs st wts rnd own₀ := by
  intro Z hs scope hK₀
  obtain rfl : Pl = PF := later_sourced hs scope
  have e : parKey Xs PF = QK := par_sourced hs scope
  have ht : tableKey Xs PF K₀ (keyOf (pubKey Z₀ Xs.chains) Xs PF K' f g) tk
      (ttShared K₀ bs st wts rnd own₀) =
      tbPlaced K₀ bs st wts rnd own₀ (keyOf (pubKey Z₀ Xs.chains) Xs PF K' f g).weights
        (AtPublicFiles.KeySharedThread.randKey (keyOf (pubKey Z₀ Xs.chains) Xs PF K' f g)) tk := by
    show tbKey (parKey Xs PF) _ _ tk _ = tbKey QK _ _ tk _
    rw [e]
  refine ⟨fun n hn => ?_, fun n hn k m => ?_⟩
  · exact opens_key_all Xs Nr (keyOf (pubKey Z₀ Xs.chains) Xs PF K' f g) ℓ Nm Mg₀ _ rest Kp Vd
      (inK w₀ rc x) e (Nat.lt_succ_of_le hn)
  · show DepthsAt (threadKey Xs Nr PF (keyOf (pubKey Z₀ Xs.chains) Xs PF K' f g) ℓ Nm Mg₀
      (tableKey Xs PF K₀ (keyOf (pubKey Z₀ Xs.chains) Xs PF K' f g) tk
        (ttShared K₀ bs st wts rnd own₀)) rest Kp Vd (inK w₀ rc x)) n k m
    rw [ht]
    exact depths_key_all K₀ hK₀ bs st wts rnd own₀ _ _ tk Xs Nr
      (keyOf (pubKey Z₀ Xs.chains) Xs PF K' f g) ℓ Nm Mg₀ rest Kp Vd (inK w₀ rc x) e hn k m

/-- **One run, one state, at the shared chain's last border, at that value.** -/
def LotOneSharedPlaced : Prop :=
  ∀ {Z : VerifierAndGoals.PublicFiles}, KeySourced Z Xs Nr Pl → VerifierAndGoals.InScope Z = true → fullPub = some K₀ →
    OneStand (walkedLetter Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk (ttShared K₀ bs st wts rnd own₀) rest Kp Vd f g
        Z₀ w₀ rc x) 12 ∧
      OneState (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk (ttShared K₀ bs st wts rnd own₀) rest Kp Vd f g Z₀
          w₀ rc x)
        (walkedLetter Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk (ttShared K₀ bs st wts rnd own₀) rest Kp Vd f g Z₀ w₀
          rc x) 12

theorem lotOneSharedPlaced :
    LotOneSharedPlaced Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk rest Kp Vd f g Z₀ w₀ rc x bs st wts rnd own₀ :=
  fun hs scope hK₀ => lotOneShared Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk _ rest Kp Vd f g Z₀ w₀ rc x
    (lotOpensShared Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk rest Kp Vd f g Z₀ w₀ rc x bs st wts rnd own₀ hs scope
      hK₀)

end AtPublicFiles.KeyStandWalked.Lots

#print axioms AtPublicFiles.KeyStandWalked.Lots.lotOpensShared
#print axioms AtPublicFiles.KeyStandWalked.Lots.lotOneSharedPlaced
