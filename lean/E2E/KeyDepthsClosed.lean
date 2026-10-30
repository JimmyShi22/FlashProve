-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyDepthsClosed.lean: Trial (e) with its holes closed: the
premises of E2E/KeyDepthsAt.lean taken at jobKU's and jobKO's own J, and own 7's premise paid at a term,
ownTbl (K12/OwnTbl.lean). So at 10, 11, 12 DepthsAt holds at the key with no premise but e and hK₀.

  t7K              own 7's text at jobKO's J
  seven_depth      its depth
  depths_key_ten, depths_key_eleven, depths_key_twelve   DepthsAt at threadKey, table as placed

Limits. The jobs at the thread's own ⟨QK, 0⟩, not at KeyLayFits' AK: atKey and QK are two terms, and
the members are held at QK here by the kernel (mems_U, mems_O; members_closed is the like at U).
As in KeyDepthsAt.lean's
head: logLength alone; ok the constant yes; nothing on L2's other prices; no thread is shown to stand.
ownTbl is a text at part 0's coins, which […] has not read. Nothing on completeness,
soundness or hiding.
-/
import E2E.KeyDepthsAt
import E2E.CongruenceAtKey
import Johnson.Desc.ProofFile.Honest.K12.OwnTbl

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace AtPublicFiles.KeyDepthsClosed
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (TableKey)
open VerifiableInference.Desc (Place Block)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source)
open _root_.Desc.K14 (St)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeySharedThread (threadKey parKey)
open AtPublicFiles.AtFiles.Full (PF QK)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyTreesKey (tbKey)
open AtPublicFiles.KeyDepthsAt (ttPlaced lays_O_at depthsAt_ten depthsAt_eleven depthsAt_twelve)
open AtPublicFiles.KeyLay (JKU JKO own_O)
open ProofFile.Honest.K12 (ownTbl ownTbl_depth)

/-- The sendings' public data at the thread's own value. -/
abbrev AQ : SendPub := ⟨QK, 0⟩

/-- The members of the test on G_u at that value. -/
def memsU : List (Addr × Nat × Due) :=
  [(⟨sendPlace 2, 0⟩, 0, ⟨0, ProofFile.Honest.K14.dueOf (jobU AQ).Q.codes ((jobU AQ).Q.sent.getD 0 default).shape
      ((jobU AQ).sort 0)⟩),
   (⟨sendPlace 5, 0⟩, 1, ⟨0, ProofFile.Honest.K14.dueOf (jobOmega AQ).Q.codes
      ((jobOmega AQ).Q.sent.getD 1 default).shape ((jobOmega AQ).sort 1)⟩)]

/-- The members of the test on G_omega at that value. -/
def memsO : List (Addr × Nat × Due) :=
  [(⟨sendPlace 5, 0⟩, 0, ⟨0, ProofFile.Honest.K14.dueOf (jobOmega AQ).Q.codes
      ((jobOmega AQ).Q.sent.getD 0 default).shape ((jobOmega AQ).sort 0)⟩),
   (⟨sendPlace 5, 0⟩, 1, ⟨0, ProofFile.Honest.K14.dueOf (jobOmega AQ).Q.codes
      ((jobOmega AQ).Q.sent.getD 1 default).shape ((jobOmega AQ).sort 1)⟩)]

/-- At QK they are jobFolded's. By the kernel. -/
theorem mems_U : memsU = AtPublicFiles.KeyTest.jobFolded.members := by decide +kernel

/-- At QK they are jobOmega's. By the kernel. -/
theorem mems_O : memsO = AtPublicFiles.KeyTest.jobOmega.members := by decide +kernel

/-- Control: the two lists are not one. -/
theorem mems_differ : memsU ≠ memsO := by decide +kernel

theorem fresh_words : AtPublicFiles.KeyTest.jobFolded.fresh = some (⟨sendPlace 2, 0⟩, 1) ∧
    AtPublicFiles.KeyTest.jobOmega.fresh = none := by decide +kernel

section
variable {W₀ Rc X₀ X Wk P₁ Wt : Type} (K₀ : KeyPub) (hK₀ : fullPub = some K₀)
  (bs : List (Block St Unit)) (st : W₀ → Rc → ℕ → ℕ → Option (List UInt64))
  (wts : Common W₀ Rc TableKey → Weights) (rnd : Common W₀ Rc TableKey → TableRand)
  (own₀ : X₀)

variable {bs st wts rnd} in
theorem members_U : (JKU (X := X₀) AQ bs st wts rnd).members = AtPublicFiles.KeyTest.jobFolded.members := mems_U

variable {bs st wts rnd} in
theorem fresh_U : (JKU (X := X₀) AQ bs st wts rnd).fresh = AtPublicFiles.KeyTest.jobFolded.fresh :=
  fresh_words.1.symm

variable {bs wts rnd} in
theorem members_O : (JKO (X := X₀) AQ bs wts rnd).members = AtPublicFiles.KeyTest.jobOmega.members := mems_O

variable {bs wts rnd} in
theorem fresh_O : (JKO (X := X₀) AQ bs wts rnd).fresh = AtPublicFiles.KeyTest.jobOmega.fresh :=
  fresh_words.2.symm

/-- Own 7's text at jobKO's J. -/
abbrev t7K : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table :=
  ownTbl 1 (JKO (X := X₀) AQ bs wts rnd) own₀ 43 (fun _ _ _ => true)

include hK₀ in
theorem seven_depth (k : Coins (keyBook K₀)) (w : Common W₀ Rc TableKey) (h : List Fmt.Drawn) :
    (t7K K₀ bs wts rnd own₀ k w h).2.logLength = 13 :=
  ownTbl_depth (JKO (X := X₀) AQ bs wts rnd) rfl 1 (Or.inr rfl)
    (lays_O_at K₀ hK₀ (JKO (X := X₀) AQ bs wts rnd) rfl members_O
      fresh_O)
    own₀ 43 (own_O (JKO (X := X₀) AQ bs wts rnd) rfl rfl) k w h

variable (weights : W₀ → Weights) (rand : Rc → TableRand)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (Xs : Source) (Nr : H2U.PlaceNums) (K : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w₁ : Common W₀ Rc TableKey)

/-- The table as placed, at the two jobs. -/
abbrev tbPlaced : Fmt.TreeSource → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn →
    Place × Table :=
  tbKey QK weights rand tk (ttPlaced K₀ (JKU (X := X₀) AQ bs st wts rnd)
    (JKO (X := X₀) AQ bs wts rnd) own₀ (t7K K₀ bs wts rnd own₀))

include hK₀ in
/-- **DepthsAt at 10 at the key, at every k and m.** -/
theorem depths_key_ten (e : parKey Xs PF = QK) (k : Coins (keyBook K₀))
    (m : Mid (Common W₀ Rc TableKey) X₀) :
    DepthsAt (threadKey Xs Nr PF K ℓ Nm Mg₀ (tbPlaced K₀ bs st wts rnd own₀ weights rand tk) rest Kp Vd
      w₁) 10 k m :=
  depthsAt_ten K₀ hK₀ weights rand tk Xs Nr K ℓ Nm Mg₀ rest Kp Vd w₁ e _ _ own₀ _ rfl
    members_U fresh_U k m

include hK₀ in
/-- **DepthsAt at 11 at the key, at every k and m.** -/
theorem depths_key_eleven (e : parKey Xs PF = QK) (k : Coins (keyBook K₀))
    (m : Mid (Common W₀ Rc TableKey) X₀) :
    DepthsAt (threadKey Xs Nr PF K ℓ Nm Mg₀ (tbPlaced K₀ bs st wts rnd own₀ weights rand tk) rest Kp Vd
      w₁) 11 k m :=
  depthsAt_eleven K₀ hK₀ weights rand tk Xs Nr K ℓ Nm Mg₀ rest Kp Vd w₁ e _ _ own₀ _ rfl
    members_U fresh_U rfl members_O
    fresh_O (seven_depth K₀ hK₀ bs wts rnd own₀) k m

include hK₀ in
/-- **DepthsAt at 12 at the key, at every k and m.** -/
theorem depths_key_twelve (e : parKey Xs PF = QK) (k : Coins (keyBook K₀))
    (m : Mid (Common W₀ Rc TableKey) X₀) :
    DepthsAt (threadKey Xs Nr PF K ℓ Nm Mg₀ (tbPlaced K₀ bs st wts rnd own₀ weights rand tk) rest Kp Vd
      w₁) 12 k m :=
  depthsAt_twelve K₀ hK₀ weights rand tk Xs Nr K ℓ Nm Mg₀ rest Kp Vd w₁ e _ _ own₀ _ rfl
    members_U fresh_U rfl members_O
    fresh_O (seven_depth K₀ hK₀ bs wts rnd own₀) k m

end

end AtPublicFiles.KeyDepthsClosed

end

#print axioms AtPublicFiles.KeyDepthsClosed.AQ
#print axioms AtPublicFiles.KeyDepthsClosed.memsU
#print axioms AtPublicFiles.KeyDepthsClosed.memsO
#print axioms AtPublicFiles.KeyDepthsClosed.mems_U
#print axioms AtPublicFiles.KeyDepthsClosed.mems_O
#print axioms AtPublicFiles.KeyDepthsClosed.mems_differ
#print axioms AtPublicFiles.KeyDepthsClosed.fresh_words
#print axioms AtPublicFiles.KeyDepthsClosed.members_U
#print axioms AtPublicFiles.KeyDepthsClosed.fresh_U
#print axioms AtPublicFiles.KeyDepthsClosed.members_O
#print axioms AtPublicFiles.KeyDepthsClosed.fresh_O
#print axioms AtPublicFiles.KeyDepthsClosed.t7K
#print axioms AtPublicFiles.KeyDepthsClosed.seven_depth
#print axioms AtPublicFiles.KeyDepthsClosed.tbPlaced
#print axioms AtPublicFiles.KeyDepthsClosed.depths_key_ten
#print axioms AtPublicFiles.KeyDepthsClosed.depths_key_eleven
#print axioms AtPublicFiles.KeyDepthsClosed.depths_key_twelve
