-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/InstanceTerm.lean: the shared thread at the base prover with no rider, and the input's
validity there.

  five_term_nine, five_term_ten, five_term_eight   the five at 9, 10 and 1 to 8 at it.
  five_term_laid   the five at 1 to 8 at every input whose key is the committer's; key_at_base pays
                   that at an instance written of the object's record.
  instance_is_xiAt   an instance written of the object's record is the builder's.
  valid_at_base      the validity that FiveFields reads, at the chain's input of the base return, at
                     an instance written of the object's record.

Limits. At the base return alone; «term» in laterTerm means the value with no rider, not T1's prover.
hfield at 10 comes from outside this file.
NOT IN FRONT OF A LAW OVER COINS (the rule: Johnson/Bind/ForProver/FiveFieldsAt.lean's head). The
ground: each of the five starts from ThrS, a premise on the letters left (rest, Kp₁, Said, w), which
may read the coins; no lemma here shows it at every value of the coins: there the bar is flat.
hw, in five_term_laid, ties a letter w's key to its coins (the first kind); key_at_base lifts it at an
instance written of the object's record, with the seed a letter beside the coins. Nothing on
completeness, on soundness or on what is hidden.
-/
import AtFullSide.K12.InstanceEight
import AtFullSide.Honest.ValidOfInstance
import AtFullSide.K14.AtLaidLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace ProofFile.Honest.Term
open AtPublicFiles.AtFiles
open OnBytes (TableKey)
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K12 (P12)
open Desc.K14 (St blocks)
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest.FirstThread
open LPFD.Full (XF)

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

variable (h : HeadAtReturn files A) (w : Common FullSizeMatrix IndexCommitterCoins TableKey)
  {b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit} {nO : H2U.PlaceNums}

/-- **The five at member 9.** -/
theorem five_term_nine
    (base : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL matrixFilling = .ok A)
    (hb : blocks (K1.qAt A.Z h.places) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hO : h.places.O = some nO) (pO : P12)
    (rest : Coins A.B → Common FullSizeMatrix IndexCommitterCoins TableKey → List Fmt.Drawn → WtShared)
    (Kp₁ : Place → St → St → Prop)
    (Said : ℕ → Coins A.B → Mid (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit → Prop)
    (fall : ℕ → St → List Fmt.Drawn → Option String) :
    FiveAtBorder (sharedThread h (readsBase h)
      (sharedParts h (laterTerm h [b1, b2, b3, b4, b5, b6, b7, b8] pO rest Kp₁)) w) Said fall 9 :=
  five_border_nine h w base hb hO pO rest [] Kp₁ (fun _ _ _ hc => absurd hc List.not_mem_nil) Said
    fall

/-- **The five at member 10.** -/
theorem five_term_ten
    (base : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL matrixFilling = .ok A)
    (hb : blocks (K1.qAt A.Z h.places) = some [b1, b2, b3, b4, b5, b6, b7, b8]) (pO : P12)
    (hO : (fourOf h.places).O = some pO)
    (rest : Coins A.B → Common FullSizeMatrix IndexCommitterCoins TableKey → List Fmt.Drawn → WtShared)
    (Kp₁ : Place → St → St → Prop)
    (Said : ℕ → Coins A.B → Mid (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit → Prop)
    (hfield : ∀ k s m E, ThrS (sharedThread h (readsBase h)
        (sharedParts h (laterTerm h [b1, b2, b3, b4, b5, b6, b7, b8] pO rest Kp₁)) w)
        Said 10 k s m E → ∀ cols,
      (sharedThread h (readsBase h)
        (sharedParts h (laterTerm h [b1, b2, b3, b4, b5, b6, b7, b8] pO rest Kp₁)) w).colsTo
        10 m E = .ok cols → m.opened = some cols)
    (fall : ℕ → St → List Fmt.Drawn → Option String) :
    FiveAtBorder (sharedThread h (readsBase h)
      (sharedParts h (laterTerm h [b1, b2, b3, b4, b5, b6, b7, b8] pO rest Kp₁)) w) Said fall 10 :=
  five_border_ten h w base hb pO hO rest [] Kp₁ Said
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ hc => absurd hc List.not_mem_nil) hfield fall

include h in
/-- **The validity at the chain's input of the base return**, at an instance written of the object's
record at M, ρ and s. -/
theorem valid_at_base (scope : VerifierAndGoals.InScope files = true) (base : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol
      files.lay files.KL matrixFilling = .ok A) (M : FullSizeMatrix) (ρ : (protocolAtFiles files).EncodingRandomness) (s : (protocolAtFiles files).OutOfDomainSeed)
    (x' : XF) :
    Bind.ForProver.validAt (Bind.ForProver.shapeOf A.Z) A.Z
      ⟨matrixInput.weights A.Z M, ProofFile.Honest.randOf (S := OnBytes.Slice.frS) (cut := 402653181) ρ,
        A.H.key (LPFD.Full.instanceAsPlainRecord (x', (protocolAtFiles files).recOf M ρ s))⟩ := by
  rw [key_at_return h]
  exact valid_of_instance files scope (ProofFile.Honest.K5.parts_of_atPure base).1.pub M ρ s x'

include h in
/-- **The key of such an input is the committer's**: the premise of k14_five_shared_laid. -/
theorem key_at_base (scope : VerifierAndGoals.InScope files = true) (base : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol
      files.lay files.KL matrixFilling = .ok A) (M : FullSizeMatrix) (ρ : (protocolAtFiles files).EncodingRandomness) (s : (protocolAtFiles files).OutOfDomainSeed)
    (x' : XF) :
    AtFullSide.K14.KeyIsTheCommitters A
      ⟨M, ProofFile.Honest.randOf (S := OnBytes.Slice.frS) (cut := 402653181) ρ,
        A.H.key (LPFD.Full.instanceAsPlainRecord (x', (protocolAtFiles files).recOf M ρ s))⟩ :=
  fun _ => valid_at_base h scope base M ρ s x'

/-- **The five at a member 1 to 8, at every input whose key is the committer's.** -/
theorem five_term_laid
    (base : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL matrixFilling = .ok A)
    (bs : List (Block St Unit)) (pO : P12)
    (rest : Coins A.B → Common FullSizeMatrix IndexCommitterCoins TableKey → List Fmt.Drawn → WtShared)
    (Kp₁ : Place → St → St → Prop) (hw : AtFullSide.K14.KeyIsTheCommitters A w)
    (Said : ℕ → Coins A.B → Mid (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit → Prop)
    (fall : ℕ → St → List Fmt.Drawn → Option String) (b : ℕ) (hb1 : 1 ≤ b) (hb8 : b ≤ 8) :
    FiveAtBorder (sharedThread h (readsBase h) (sharedParts h (laterTerm h bs pO rest Kp₁)) w)
      Said fall b :=
  AtFullSide.K14.k14_five_shared_laid base h (laterTerm h bs pO rest Kp₁) rfl rfl
    (fun _ hc => absurd hc List.not_mem_nil) w hw Said fall b hb1 hb8

/-- An instance written of the object's record is the builder's at the public part's own shape. -/
theorem instance_is_xiAt (scope : VerifierAndGoals.InScope files = true)
    (base : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL matrixFilling = .ok A) (M : FullSizeMatrix)
    (ρ : (protocolAtFiles files).EncodingRandomness) (s : (protocolAtFiles files).OutOfDomainSeed) (x' : XF) :
    ∃ (sd : Bind.ForProver.Seed (Bind.ForProver.shapeOf A.Z) × ℕ) (bytes : ByteArray × ByteArray),
      LPFD.Full.instanceAsPlainRecord (x', (protocolAtFiles files).recOf M ρ s) =
        Bind.ForProver.xiAt (Bind.ForProver.shapeOf A.Z) A.Z
          ⟨matrixInput.weights A.Z M, ProofFile.Honest.randOf (S := OnBytes.Slice.frS) (cut := 402653181) ρ,
            sd⟩ bytes := by
  have hp := (ProofFile.Honest.K5.parts_of_atPure base).1.pub
  have hS : Bind.ForProver.shapeOf A.Z = Bind.Column.shFull :=
    (Bind.ForProver.shapeAtFull_inScope scope hp).1
  rw [hS]
  exact instance_is_committers files scope hp M ρ s x'

/-- **The five at a member 1 to 8, at the chain's input at an instance written of the object's
record.** -/
theorem five_term_eight (scope : VerifierAndGoals.InScope files = true)
    (base : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL matrixFilling = .ok A)
    (bs : List (Block St Unit)) (pO : P12)
    (rest : Coins A.B → Common FullSizeMatrix IndexCommitterCoins TableKey → List Fmt.Drawn → WtShared)
    (Kp₁ : Place → St → St → Prop) (M : FullSizeMatrix) (ρ : (protocolAtFiles files).EncodingRandomness) (s : (protocolAtFiles files).OutOfDomainSeed) (x' : XF)
    (Said : ℕ → Coins A.B → Mid (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit → Prop)
    (fall : ℕ → St → List Fmt.Drawn → Option String) (b : ℕ) (hb1 : 1 ≤ b) (hb8 : b ≤ 8) :
    FiveAtBorder (sharedThread h (readsBase h) (sharedParts h (laterTerm h bs pO rest Kp₁))
      ⟨M, ProofFile.Honest.randOf (S := OnBytes.Slice.frS) (cut := 402653181) ρ,
        A.H.key (LPFD.Full.instanceAsPlainRecord (x', (protocolAtFiles files).recOf M ρ s))⟩) Said fall b := by
  obtain ⟨sd, bytes, e⟩ := instance_is_xiAt scope base M ρ s x'
  rw [e]
  exact five_border_eight h base bs pO rest [] Kp₁ (fun _ hc => absurd hc List.not_mem_nil) M _ sd
    bytes Said fall b hb1 hb8

end ProofFile.Honest.Term

#print axioms ProofFile.Honest.Term.key_at_base
#print axioms ProofFile.Honest.Term.five_term_laid
#print axioms ProofFile.Honest.Term.instance_is_xiAt
#print axioms ProofFile.Honest.Term.five_term_eight
#print axioms ProofFile.Honest.Term.five_term_nine
#print axioms ProofFile.Honest.Term.five_term_ten
#print axioms ProofFile.Honest.Term.valid_at_base
