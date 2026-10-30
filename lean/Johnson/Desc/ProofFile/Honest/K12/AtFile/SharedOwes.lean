-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/SharedOwes.lean: NOT IN FRONT OF A LAW OVER COINS. At the proof
file's shared thread at the base return, at the letter that keeps the field: the five at every member:
so OwesS, YesS and SaidNext, the second chain's fields of FromThreads.

  five_front           the five at member 0
  five_every           the five at all twelve members
  owes_at_term, yes_at_term, next_at_term   the fields

Premises left. hw: the input's key is the committer's.

By what. five_zero (MemberZero.lean), five_term_laid, five_border_nine, five_border_ten, five_at_end,
owesS_of_five, yesS_of_five.

Limits. At the base return alone. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.SharedAtTerm

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
open Desc.K14 (St blocks frontBlock)
open ProofFile.Honest.K12.AtFile
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest.FirstThread
open P2Law.ProofPlan (WP)

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (h : HeadAtReturn files A)
  {b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit} {nO : H2U.PlaceNums} (w : Common FullSizeMatrix IndexCommitterCoins TableKey)
  (pO : P12) (rest : Coins A.B → Common FullSizeMatrix IndexCommitterCoins TableKey → List Fmt.Drawn → WtShared)

local notation "𝐓" =>
  sharedThread h (readsBase h)
    (sharedParts h (laterTerm h [b1, b2, b3, b4, b5, b6, b7, b8] pO rest keepsEq)) w

/-- **The five at member 0.** -/
theorem five_front (hb : blocks (K1.qAt A.Z h.places) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (Said : ℕ → Coins A.B → Mid (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit → Prop)
    (fall : ℕ → St → List Fmt.Drawn → Option String) : FiveAtBorder (𝐓) Said fall 0 := by
  have hf := front_at (cF := h.firstChain) hb
  obtain ⟨x0, tl, he, hl₀⟩ : ∃ x0 tl, (𝐓).bs.take 9 = x0 :: tl ∧
      Desc.K14.Honest.Like x0 (frontBlock A.Z.p.chains) := by
    cases hf with
    | cons a _ => exact ⟨_, _, rfl, a⟩
  have hb₀ : (𝐓).bs[0]? = some x0 := by
    have e := congrArg (·[0]?) he
    simpa using e
  obtain ⟨p, a, b, e, r⟩ := five_zero (lettersBase h
      (sharedParts h (laterTerm h [b1, b2, b3, b4, b5, b6, b7, b8] pO rest keepsEq)) (readsBase h) w)
    Said rfl A.Z.p.chains hb₀ hl₀ (fun _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ c hc => absurd hc List.not_mem_nil)
    (fun _ s _ _ _ p hp => by
      obtain rfl : p = ⟨2, none, 0, .frame⟩ := (Option.some.inj hp).symm
      rfl)
    (fun _ s _ _ s' _ hk => hk _ rfl)
    (fun _ _ _ _ _ _ => trivial) fall
  exact ⟨p, b, e, r, a⟩

/-- **The five at every member.** -/
theorem five_every (scope : VerifierAndGoals.InScope files = true)
    (base : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL matrixFilling = .ok A)
    (hb : blocks (K1.qAt A.Z h.places) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hO : h.places.O = some nO) (hO' : (fourOf h.places).O = some pO)
    (hw : AtFullSide.K14.KeyIsTheCommitters A w)
    (fall : ℕ → St → List Fmt.Drawn → Option String) (b : ℕ) (hlt : b < (𝐓).bs.length) :
    FiveAtBorder (𝐓) (SaidField (𝐓) BaseNil) fall b := by
  have e12 : (𝐓).bs.length = 12 := twelve_members h.head hO
  rw [e12] at hlt
  by_cases h0 : b = 0
  · subst h0
    exact five_front h w pO rest hb _ fall
  by_cases h8 : b ≤ 8
  · exact five_term_laid h w base _ pO rest keepsEq hw _ fall b (by omega) h8
  by_cases h9 : b = 9
  · subst h9
    exact five_border_nine h w base hb hO pO rest [] keepsEq
      (fun _ _ _ hc => absurd hc List.not_mem_nil) _ fall
  by_cases h10 : b = 10
  · subst h10
    exact five_border_ten h w base hb pO hO' rest [] keepsEq _
      (fun _ _ _ _ _ _ _ _ _ _ _ _ _ hc => absurd hc List.not_mem_nil)
      (fun _ _ _ _ u cols hc => field_of_saidNil _ u cols hc) fall
  have e : b = 11 := by omega
  subst e
  exact five_at_end h w pO rest hO hb (key_fits_term h scope base _ _ w hw)
    (none_at_end h base hb hO') _ fall

/-- **OwesS.** -/
theorem owes_at_term (scope : VerifierAndGoals.InScope files = true)
    (base : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL matrixFilling = .ok A)
    (hb : blocks (K1.qAt A.Z h.places) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hO : h.places.O = some nO) (hO' : (fourOf h.places).O = some pO)
    (hw : AtFullSide.K14.KeyIsTheCommitters A w) : OwesS (𝐓) (SaidField (𝐓) BaseNil) :=
  owesS_of_five (fall := fun _ _ _ => none) (five_every h w pO rest scope base hb hO hO' hw _)

/-- **YesS.** -/
theorem yes_at_term (scope : VerifierAndGoals.InScope files = true)
    (base : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL matrixFilling = .ok A)
    (hb : blocks (K1.qAt A.Z h.places) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hO : h.places.O = some nO) (hO' : (fourOf h.places).O = some pO)
    (hw : AtFullSide.K14.KeyIsTheCommitters A w)
    (fall : ℕ → St → List Fmt.Drawn → Option String) : YesS (𝐓) (SaidField (𝐓) BaseNil) fall :=
  yesS_of_five (five_every h w pO rest scope base hb hO hO' hw fall)

/-- **SaidNext at every member.** -/
theorem next_at_term (scope : VerifierAndGoals.InScope files = true)
    (base : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL matrixFilling = .ok A)
    (hb : blocks (K1.qAt A.Z h.places) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hO : h.places.O = some nO) (hO' : (fourOf h.places).O = some pO)
    (hw : AtFullSide.K14.KeyIsTheCommitters A w) (b : ℕ) :
    SaidNext (𝐓) (SaidField (𝐓) BaseNil) b := by
  intro blk hblk
  have hj := lt_of_member _ hblk
  have e12 : (𝐓).bs.length = 12 := twelve_members h.head hO
  have F : WalkFacts (𝐓) 12 := walk_at_term h base pO hO' rest keepsEq w
  exact (paid_of_border F (by omega)
    (five_every h w pO rest scope base hb hO hO' hw _ b hj)).next blk hblk

end ProofFile.Honest.Term

#print axioms ProofFile.Honest.Term.five_front
#print axioms ProofFile.Honest.Term.five_every
#print axioms ProofFile.Honest.Term.owes_at_term
#print axioms ProofFile.Honest.Term.yes_at_term
#print axioms ProofFile.Honest.Term.next_at_term
