-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/SharedStandAtBase.lean: NOT IN FRONT OF A LAW OVER COINS. The
proof file's shared thread at the base prover, walked through K14's eight members and the two
proximity tests at the letter that keeps the field: stands at 9, 10 and 11 behind real yeses.

  stand_eleven_at_base the statement, at laterBase with no rider, at any input

Premises left, each named. H18: the five at K14's eight. F: WalkFacts at the term. P₀: member 0. R: each member's rounds at the
run's coins and lists. start: the stand at 0.

By what. stand_eleven (SharedStand.lean), five_border_nine, five_border_ten
(AtFullSide/K12/InstanceLater.lean), field_of_saidNil (OField.lean).

Limits. A walk of the thread's steps, not a run of the frame. At the base return alone. Nothing on
completeness, soundness or hiding.
-/
import AtFullSide.K12.InstanceLater
import Johnson.Desc.ProofFile.Honest.K12.AtFile.SharedStand
import Johnson.Desc.ProofFile.Honest.K12.AtFile.OField

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

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (h : HeadAtReturn files A)
  {b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit} {nO : H2U.PlaceNums} (w : Common FullSizeMatrix IndexCommitterCoins TableKey)

local notation "𝐓" pO:max rest:max Kp₁:max =>
  sharedThread h (readsBase h) (sharedParts h (laterBase h [b1, b2, b3, b4, b5, b6, b7, b8] pO rest [] Kp₁))
    w

/-- **The walk at the base prover.** -/
theorem stand_eleven_at_base
    (base : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL matrixFilling = .ok A)
    (hb : blocks (K1.qAt A.Z h.places) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hO : h.places.O = some nO) (pO : P12) (hO' : (fourOf h.places).O = some pO)
    (rest : Coins A.B → Common FullSizeMatrix IndexCommitterCoins TableKey → List Fmt.Drawn → WtShared)
    (Kp₁ : Place → St → St → Prop)
    (H18 : ∀ b, 1 ≤ b → b ≤ 8 → FiveAtBorder (𝐓 pO rest Kp₁)
      (SaidField (𝐓 pO rest Kp₁) BaseNil) (fun _ _ _ => none) b)
    (F : WalkFacts (𝐓 pO rest Kp₁) 12)
    (P₀ : MemberPaid (𝐓 pO rest Kp₁) (SaidField (𝐓 pO rest Kp₁) BaseNil) 0)
    {k : Coins A.B} {s₀ : St} {m₀ : Mid (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit} {E₀ : Env}
    (start : ThrS (𝐓 pO rest Kp₁) (SaidField (𝐓 pO rest Kp₁) BaseNil) 0 k s₀ m₀ E₀)
    (ds : ℕ → List Fmt.Drawn) (R : ∀ j, j < 11 → MemberRuns (𝐓 pO rest Kp₁) k j (ds j)) :
    ∃ (s s' s'' : St) (m m' m'' : Mid (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit) (E E' E'' : Env),
      ThrS (𝐓 pO rest Kp₁) (SaidField (𝐓 pO rest Kp₁) BaseNil) 9 k s m E ∧
      ThrS (𝐓 pO rest Kp₁) (SaidField (𝐓 pO rest Kp₁) BaseNil) 10 k s' m' E' ∧
      ThrS (𝐓 pO rest Kp₁) (SaidField (𝐓 pO rest Kp₁) BaseNil) 11 k s'' m'' E'' ∧
      (𝐓 pO rest Kp₁).keeps 9 s s' ∧ (𝐓 pO rest Kp₁).keeps 10 s' s'' ∧
      m''.st.heard =
        m₀.st.heard ++ ((List.range 9).flatMap fun j => ds (0 + j)) ++ ds 9 ++ ds 10 := by
  refine stand_eleven F P₀ (fun b h1 h10 => ?_) start ds R
  by_cases h8 : b ≤ 8
  · exact H18 b h1 h8
  by_cases h9 : b = 9
  · subst h9
    exact five_border_nine h _ base hb hO pO rest [] Kp₁ (fun _ _ _ hc => absurd hc List.not_mem_nil) _ _
  have e : b = 10 := by omega
  subst e
  exact five_border_ten h _ base hb pO hO' rest [] Kp₁ _
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ hc => absurd hc List.not_mem_nil)
    (fun _ _ _ _ u cols hc => ProofFile.Honest.K12.AtFile.field_of_saidNil _ u cols hc) _

end ProofFile.Honest.Term

#print axioms ProofFile.Honest.Term.stand_eleven_at_base
