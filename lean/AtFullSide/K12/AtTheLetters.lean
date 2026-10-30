-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/AtTheLetters.lean: the five at the shared chain's members 1 to 10 at the names of
TheLetters.lean: later, shared, reads, keepsOff.

  letters_head       under the head: the plan's eight blocks and the test on G_omega's place are
                     there, so that sharedBlocks and the default in later read them.
  later_at_head      later is laterTerm at these values.
  five_letters_nine, five_letters_ten, five_letters_eight   the five at 9, at 10, and at 1 to 8.

Limits. At the base return alone. NOT IN FRONT OF A LAW OVER COINS (the rule:
Johnson/Bind/ForProver/FiveFieldsAt.lean's head). The ground: each of the five starts from ThrS, a
premise on the letters left (O.rest, Said, w), which may read the coins: the bar is flat. hw ties w's
key to its coins (the first kind); key_at_base lifts it at an instance written of the object's
record. hfield at 10 is a premise. Nothing on completeness, on soundness or on what is hidden.
-/
import AtFullSide.Honest.TheLettersShared
import Johnson.Desc.ProofFile.Honest.K12.Sim.FirstPubOwnAtHead
import AtFullSide.K12.InstanceKeyFits

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.Honest.TheLetters
open AtPublicFiles.AtFiles
open ProofFile.Honest ProofFile.Honest.FirstThread
open OnBytes (TableKey)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K12 (P12)
open Desc.K14 (St blocks)
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest.Term (laterTerm matrixFilling)

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]
variable {Z : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (h : HeadAtReturn Z A)

/-- **Under the head the plan's eight blocks and the test on G_omega's place are there.** -/
theorem letters_head :
    ∃ (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit) (nO : H2U.PlaceNums) (pO : P12),
      blocks (K1.qAt A.Z h.places) = some [b1, b2, b3, b4, b5, b6, b7, b8] ∧
        h.places.O = some nO ∧ (fourOf h.places).O = some pO := by
  obtain ⟨_, _, hQ⟩ := ProofFile.Honest.K14.plan2_at_head h.head
  obtain ⟨B⟩ := hQ.eight
  obtain ⟨pO, hO⟩ := ProofFile.Honest.K12.Light.omega_head h.head.toAtMg
  obtain ⟨nO, h1, -⟩ := ProofFile.Honest.K12.Light.omega_of_four hO
  exact ⟨B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8, nO, pO, B.made, h1, hO⟩

/-- **later is laterTerm at the head's values.** -/
theorem later_at_head {b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit} {pO : P12}
    (hb : blocks (K1.qAt A.Z h.places) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hO : (fourOf h.places).O = some pO) (O : OpenShared A) :
    later (h := h) O = laterTerm h [b1, b2, b3, b4, b5, b6, b7, b8] pO O.rest keepsOff := by
  have e₁ : sharedBlocks h = [b1, b2, b3, b4, b5, b6, b7, b8] := by
    unfold sharedBlocks
    rw [hb]
    rfl
  have e₂ : (fourOf h.places).O.getD (fourOf h.places).U = pO := by
    rw [hO]
    rfl
  have e₀ : later (h := h) O = ProofFile.Honest.Term.laterBase h (sharedBlocks h)
      ((fourOf h.places).O.getD (fourOf h.places).U) O.rest [] keepsOff := rfl
  rw [e₀, e₁, e₂]

variable (w : Common FullSizeMatrix IndexCommitterCoins TableKey)

/-- **The five at member 9, at TheLetters' names.** -/
theorem five_letters_nine
    (base : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A) (O : OpenShared A)
    (Said : ℕ → Coins A.B → Mid (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit → Prop)
    (fall : ℕ → St → List Fmt.Drawn → Option String) :
    FiveAtBorder (sharedThread h (reads h) (shared h O) w) Said fall 9 := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, nO, pO, hb, hN, hO⟩ := letters_head h
  show FiveAtBorder (sharedThread h (reads h) (sharedParts h (later (h := h) O)) w) Said fall 9
  rw [later_at_head h hb hO O]
  exact ProofFile.Honest.Term.five_term_nine h w base hb hN pO O.rest keepsOff Said fall

/-- **The five at member 10, at TheLetters' names.** -/
theorem five_letters_ten
    (base : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A) (O : OpenShared A)
    (Said : ℕ → Coins A.B → Mid (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit → Prop)
    (hfield : ∀ k s m E, ThrS (sharedThread h (reads h) (shared h O) w) Said 10 k s m E → ∀ cols,
      (sharedThread h (reads h) (shared h O) w).colsTo 10 m E = .ok cols → m.opened = some cols)
    (fall : ℕ → St → List Fmt.Drawn → Option String) :
    FiveAtBorder (sharedThread h (reads h) (shared h O) w) Said fall 10 := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, nO, pO, hb, -, hO⟩ := letters_head h
  revert hfield
  show (∀ k s m E, ThrS (sharedThread h (reads h) (sharedParts h (later (h := h) O)) w) Said 10
      k s m E → ∀ cols, (sharedThread h (reads h) (sharedParts h (later (h := h) O)) w).colsTo 10 m E =
        .ok cols → m.opened = some cols) →
    FiveAtBorder (sharedThread h (reads h) (sharedParts h (later (h := h) O)) w) Said fall 10
  rw [later_at_head h hb hO O]
  exact fun hf => ProofFile.Honest.Term.five_term_ten h w base hb pO hO O.rest keepsOff Said hf fall

/-- **The five at a member 1 to 8, at TheLetters' names**, at every input whose key is the
committer's. -/
theorem five_letters_eight
    (base : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A) (O : OpenShared A)
    (hw : AtFullSide.K14.KeyIsTheCommitters A w)
    (Said : ℕ → Coins A.B → Mid (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit → Prop)
    (fall : ℕ → St → List Fmt.Drawn → Option String) (b : ℕ) (hb1 : 1 ≤ b) (hb8 : b ≤ 8) :
    FiveAtBorder (sharedThread h (reads h) (shared h O) w) Said fall b := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, nO, pO, hb, -, hO⟩ := letters_head h
  show FiveAtBorder (sharedThread h (reads h) (sharedParts h (later (h := h) O)) w) Said fall b
  rw [later_at_head h hb hO O]
  exact ProofFile.Honest.Term.five_term_laid h w base _ pO O.rest keepsOff hw Said fall b hb1 hb8

end AtFullSide.Honest.TheLetters

#print axioms AtFullSide.Honest.TheLetters.letters_head
#print axioms AtFullSide.Honest.TheLetters.later_at_head
#print axioms AtFullSide.Honest.TheLetters.five_letters_nine
#print axioms AtFullSide.Honest.TheLetters.five_letters_ten
#print axioms AtFullSide.Honest.TheLetters.five_letters_eight
