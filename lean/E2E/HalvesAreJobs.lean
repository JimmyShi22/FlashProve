-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/HalvesAreJobs.lean

THE HALVES IN THE KEY's SHARED LIST ARE THE TWO JOBS' HALVES, at one term of the key's parts: the
pairs (E2E/KeyPartsHalves.lean) laid over parts whose sendings stand at the chain's own parameters.


  `bs_of`            at such parts the eight are `Eight`'s
  `pU`, `pO`         the two places, from the written numbers; `pO_full`, `place_omega`
  `JO`               the job at the test on G_omega, at these parts
  `onU_is_job`, `onOmega_is_job`   the pairs are `proverSideOfProximityTest (jobNine …)` and `(proverSideOfProximityTest JO).needsField`
  `withHalves_keyOf` the pairs over `keyOf` are `keyOf` over the pairs: `not_plays_at`'s form
  `find_U`, `find_O`  at the places of members 9 and 10, the prover's list finds these halves
  `trees_nine_at`    `trees_nine` at this term: its hU and hOp paid

PREMISES. hs : K₁.send = ⟨parKey Xs PF, 0⟩: true of `keyOf` by text (`send_keyOf`). B : Eight …; hsp on
`K₁.lin`: true of `keyOf` in scope (`hQ.facts.two`). What stays of `trees_nine`: e, own₀, htt.

ORDER MATTERS. The pairs read the parts' stored columns, weights and rand: so the pairs go on top of
`keyOf`, not under it.

Limits. No Thr, no Moved, no Plays: what a run reaches is not said. That K₁'s readers are the key's
real ones is `keyOf`'s. Nothing on completeness, on soundness or on what is hidden.
-/
import E2E.TreesAtNine
import E2E.KeyPartsHalves
import E2E.KeyStandMember

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace AtPublicFiles.HalvesAreJobs
open ProofFile.Honest ProofFile.Honest.K14 ProofFile.Honest.K12
open OnBytes (TableKey)
open VerifiableInference.Desc (Place Block)
open VerifiableInference.Desc.K12 (P12)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source)
open AtPublicFiles.KeyFile (KeyParts keyProver keyProver_shared)
open AtPublicFiles.KeySharedThread (threadKey parKey)
open _root_.Desc.K14 (St blocks)
open _root_.Desc.K14.Honest (Eight)
open AtPublicFiles.AtFiles.Full (QK PF)
open AtPublicFiles.KeyBook (foldedTestPlace omegaTestPlace)
open AtPublicFiles.KeyDoorNine (jobNine)
open AtPublicFiles.KeyTreesKey (tbKey)
open AtPublicFiles.KeyLay (jobKO proverSideOfTestOnU proverSideOfTestOnOmega onUOf onOmegaOf withTestsOnUAndOmega bsOf wtOf rdOf)
open AtPublicFiles.KeyStandMember (keyOf)
open AtPublicFiles.TreesAtNine (JN TN trees_nine)
open H2K.Member (piKOFull)

/-- The place of the test on G_u. -/
abbrev pU : P12 := H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ PF.U

/-- The place of the test on G_omega. -/
abbrev pO : P12 := H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ (PF.O.getD PF.U)

theorem pO_full : pO = piKOFull := by
  first
    | decide +kernel
    | rfl

theorem place_omega : pO.place = omegaTestPlace := by
  rw [pO_full]
  decide +kernel

section
variable {W₀ Rc X₀ X Wk : Type}

theorem send_keyOf (Zp : ProofFile.Pub) (Xs : Source) (K' : KeyParts W₀ Rc X₀ X Wk) (f : W₀ → Weights)
    (g : Rc → ℕ → TableRand) :
    (keyOf Zp Xs PF K' f g).send = ⟨parKey Xs PF, 0⟩ := rfl

/-- The pairs over `keyOf` are `keyOf` over the pairs. -/
theorem withHalves_keyOf (Zp : ProofFile.Pub) (Xs : Source) (K' : KeyParts W₀ Rc X₀ X Wk)
    (f : W₀ → Weights) (g : Rc → ℕ → TableRand) (p q : P12) :
    withTestsOnUAndOmega (keyOf Zp Xs PF K' f g) p q =
      keyOf Zp Xs PF
        { K' with onU := onUOf (keyOf Zp Xs PF K' f g) p
                  onOmega := onOmegaOf (keyOf Zp Xs PF K' f g) p q } f g := rfl

variable (Xs : Source) (K₁ : KeyParts W₀ Rc X₀ X Wk) (B : Eight (parKey Xs PF))

theorem bs_of (hs : K₁.send = ⟨parKey Xs PF, 0⟩) :
    bsOf K₁ = [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8] := by
  unfold bsOf
  rw [hs]
  show (blocks (parKey Xs PF)).getD [] = _
  rw [B.made]
  rfl

/-- The job at the test on G_omega, at these parts. -/
abbrev JO : TestJob (Common W₀ Rc TableKey) X₀ :=
  (jobKO (X := X₀) ⟨parKey Xs PF, 0⟩ pU pO [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8]
    (wtOf K₁) (rdOf K₁)).toRun.toTest

/-- **The pair at the test on G_u is the half of the job.** -/
theorem onU_is_job (hs : K₁.send = ⟨parKey Xs PF, 0⟩) :
    onUOf K₁ pU = proverSideOfProximityTest (JN Xs K₁ B) := by
  unfold onUOf proverSideOfTestOnU
  rw [bs_of Xs K₁ B hs, hs]
  rfl

/-- **The pair at the test on G_omega is the half of JO behind the guard.** -/
theorem onOmega_is_job (hs : K₁.send = ⟨parKey Xs PF, 0⟩) :
    onOmegaOf K₁ pU pO = (proverSideOfProximityTest (JO Xs K₁ B) : Placed Empty (Common W₀ Rc TableKey) X₀).needsField := by
  unfold onOmegaOf proverSideOfTestOnOmega
  rw [bs_of Xs K₁ B hs, hs]

include Xs K₁ B in
theorem place_gu : (H2K.JointK.keyGu PF).place = pU.place :=
  (seatOf_inside (Cl := Unit) (JN Xs K₁ B)
    (VerifiableInference.Desc.K12.Seat.enter (·.gU) (·.firstMask))
    VerifiableInference.Desc.K12.Seat.leave).place

include Xs K₁ B in
theorem place_go : (H2K.JointK.keyOmega (PF.O.getD PF.U)).place = pO.place :=
  (seatOf_inside (Cl := Unit) (JO Xs K₁ B)
    (VerifiableInference.Desc.K12.Seat.enter (·.gOmega) fun _ => none)
    VerifiableInference.Desc.K12.Seat.leave).place

theorem nodup_halves (hsp : K₁.lin.S.sharedSplitNeeded = true) :
    ((keyProver (withTestsOnUAndOmega K₁ pU pO)).shared.map (·.place)).Nodup := by
  have pa : (withTestsOnUAndOmega K₁ pU pO).onU.place = foldedTestPlace := AtPublicFiles.KeyPlaysAt.place_on
  have pb : (withTestsOnUAndOmega K₁ pU pO).onOmega.place = omegaTestPlace := place_omega
  rw [keyProver_shared (withTestsOnUAndOmega K₁ pU pO) hsp, pa, pb]
  decide

/-- **At member 9's place the prover's list finds the half of the job.** -/
theorem find_U (hs : K₁.send = ⟨parKey Xs PF, 0⟩) (hsp : K₁.lin.S.sharedSplitNeeded = true) :
    ((keyProver (withTestsOnUAndOmega K₁ pU pO)).shared.find? fun g =>
      g.place == (H2K.JointK.keyGu PF).place) = some (proverSideOfProximityTest (JN Xs K₁ B)) := by
  have hf : ((keyProver (withTestsOnUAndOmega K₁ pU pO)).shared.find? fun g =>
      g.place == (onUOf K₁ pU).place) = some (onUOf K₁ pU) :=
    AtPublicFiles.KeyPlaysAt.find_of_nodup (fun g : Placed Empty (Common W₀ Rc TableKey) X₀ => g.place)
      (g := onUOf K₁ pU) (keyProver (withTestsOnUAndOmega K₁ pU pO)).shared
      (List.mem_append_right _ List.mem_cons_self) (nodup_halves K₁ hsp)
  have hp : (H2K.JointK.keyGu PF).place = (onUOf K₁ pU).place := place_gu Xs K₁ B
  rw [hp, hf, onU_is_job Xs K₁ B hs]

/-- **At member 10's place it finds the half of JO behind the guard.** -/
theorem find_O (hs : K₁.send = ⟨parKey Xs PF, 0⟩) (hsp : K₁.lin.S.sharedSplitNeeded = true) :
    ((keyProver (withTestsOnUAndOmega K₁ pU pO)).shared.find? fun g =>
      g.place == (H2K.JointK.keyOmega (PF.O.getD PF.U)).place) =
      some (proverSideOfProximityTest (JO Xs K₁ B) : Placed Empty (Common W₀ Rc TableKey) X₀).needsField := by
  have hf : ((keyProver (withTestsOnUAndOmega K₁ pU pO)).shared.find? fun g =>
      g.place == (onOmegaOf K₁ pU pO).place) = some (onOmegaOf K₁ pU pO) :=
    AtPublicFiles.KeyPlaysAt.find_of_nodup (fun g : Placed Empty (Common W₀ Rc TableKey) X₀ => g.place)
      (g := onOmegaOf K₁ pU pO) (keyProver (withTestsOnUAndOmega K₁ pU pO)).shared
      (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)) (nodup_halves K₁ hsp)
  have hp : (H2K.JointK.keyOmega (PF.O.getD PF.U)).place = (onOmegaOf K₁ pU pO).place :=
    place_go Xs K₁ B
  rw [hp, hf, onOmega_is_job Xs K₁ B hs]

end

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (K₁ : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (wts : W₀ → Weights) (rnd : Rc → TableRand)
  (tk : Nat → Nat → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (tt : Nat → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w : Common W₀ Rc TableKey)

/-- **`trees_nine` at this term**: what stays is e, B, hs, hsp, own₀ and tt's equation. -/
theorem trees_nine_at (e : parKey Xs PF = QK) (B : Eight (parKey Xs PF))
    (hs : K₁.send = ⟨parKey Xs PF, 0⟩) (hsp : K₁.lin.S.sharedSplitNeeded = true) (own₀ : X₀)
    (htt : ∀ τ, τ < 4 → tt (3 + τ) = testTbl 1 (JN Xs K₁ B) own₀ 8 (fun _ _ _ => true) τ) :
    ∀ k s m E ds y cols,
      Thr (TN Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w) 9 k s m E →
      drawsFit (H2K.JointK.keyGu PF).rounds ds = true →
      (TN Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w).Moved
        (H2K.JointK.keyGu PF) k m E ds y cols →
      (TN Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w).Trees
        ((TN Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w).fresh 9) k y.2
        (E.add y.1) :=
  trees_nine Xs Nr (withTestsOnUAndOmega K₁ pU pO) K₁ ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w e B hsp
    (onU_is_job Xs K₁ B hs) place_omega own₀ htt

end

end AtPublicFiles.HalvesAreJobs

#print axioms AtPublicFiles.HalvesAreJobs.pU
#print axioms AtPublicFiles.HalvesAreJobs.pO
#print axioms AtPublicFiles.HalvesAreJobs.pO_full
#print axioms AtPublicFiles.HalvesAreJobs.place_omega
#print axioms AtPublicFiles.HalvesAreJobs.send_keyOf
#print axioms AtPublicFiles.HalvesAreJobs.withHalves_keyOf
#print axioms AtPublicFiles.HalvesAreJobs.bs_of
#print axioms AtPublicFiles.HalvesAreJobs.JO
#print axioms AtPublicFiles.HalvesAreJobs.onU_is_job
#print axioms AtPublicFiles.HalvesAreJobs.onOmega_is_job
#print axioms AtPublicFiles.HalvesAreJobs.place_gu
#print axioms AtPublicFiles.HalvesAreJobs.place_go
#print axioms AtPublicFiles.HalvesAreJobs.nodup_halves
#print axioms AtPublicFiles.HalvesAreJobs.find_U
#print axioms AtPublicFiles.HalvesAreJobs.find_O
#print axioms AtPublicFiles.HalvesAreJobs.trees_nine_at
