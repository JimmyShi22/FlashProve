-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/TermFacts.lean: what the walk of the shared chain takes at the thread of
the base return: `sharedThread` at `laterTerm` (AtFullSide/K12/InstanceTerm.lean).

  `walk_at_term`   `WalkFacts` at twelve
  `zero_at_term`   `MemberPaid` at member 0, where what a place keeps off the two tests is the state itself
  `none_at_end`    no half of the base prover stands at the chain's end

The premises. base: the base return. hb: the eight. hO': the second test's place.

Limits. At the base return alone. NOT IN FRONT OF A LAW OVER COINS. Nothing on completeness, on soundness or on
what is hidden.
-/
import AtFullSide.K12.InstanceTerm
import Johnson.Desc.ProofFile.Honest.K12.Part4.TwoTestsOfTheSharedChain
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WalkAtShared
import Johnson.Desc.ProofFile.Honest.K12.AtFile.MemberZeroPaid
import Johnson.Desc.ProofFile.Honest.K12.AtFile.StopsShared
import Johnson.Desc.ProofFile.Honest.K12.AtFile.HalfAtBase

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
open ProofFile.Honest.K12 (TestJob laysB)
open ProofFile.Honest.K12.Light (doorUF colsLoc sentOf)
open ProofFile.Honest.K12.AtFile
open ProofFile.Honest.K12.AtProof (fourOf placeU placeO sharedWithUO halfU halfO halfU_at_head halfO_at_head
  p12At_place)
open ProofFile.Honest.K14 (nowSharedBy_at_head halves_eq sendHalves_eq treesU)
open ProofFile.Honest.FirstThread
open P2Law.ProofPlan (WP)

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (h : HeadAtReturn files A)
  {b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit}

local notation "𝐓" pO:max rest:max Kp₁:max w:max =>
  sharedThread h (readsBase h) (sharedParts h (laterTerm h [b1, b2, b3, b4, b5, b6, b7, b8] pO rest Kp₁)) w

local notation "𝐋" pO:max rest:max Kp₁:max w:max =>
  lettersBase h (sharedParts h (laterTerm h [b1, b2, b3, b4, b5, b6, b7, b8] pO rest Kp₁)) (readsBase h) w

/-- **`WalkFacts` at twelve.** -/
theorem walk_at_term (base : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL matrixFilling = .ok A)
    (pO : P12) (hO' : (fourOf h.places).O = some pO)
    (rest : Coins A.B → Common FullSizeMatrix IndexCommitterCoins TableKey → List Fmt.Drawn → WtShared)
    (Kp₁ : Place → St → St → Prop) (w : Common FullSizeMatrix IndexCommitterCoins TableKey) :
    WalkFacts (𝐓 pO rest Kp₁ w) 12 := by
  have hm := h.head.toAtMg
  have hLU := ProofFile.Honest.K12.Part4.bookLendsTheJobOnU _ _ _ _ _ _ _ hm A.B (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit
    (doorUF (K1.qAt A.Z h.places) (sentOf (K1.qAt A.Z h.places).S) [b1, b2, b3, b4, b5, b6, b7, b8]
      (fun w => w.key)
      (fun w fr => colsLoc (K1.qAt A.Z h.places) (A.H.storedWords w.w₀ w.rc) fr.seen.rounds))
    (fun c => (readsBase h).weights c.w₀) (fun c => (readsBase h).rand c.rc) none (book_written h)
  have hLO : laysB A.B 1 (jobDoorO (X₀ := Unit) A.Z h.places pO [b1, b2, b3, b4, b5, b6, b7, b8]
      (readsBase h).weights (readsBase h).rand).toRun.toTest = true :=
    ProofFile.Honest.K12.Part4.bookLendsTheJobOnOmega _ _ _ _ _ _ _ hm A.B
      (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit pO _ (fun c => (readsBase h).weights c.w₀)
      (fun c => (readsBase h).rand c.rc) none (book_written h) hO'
  obtain ⟨c2, c5, -, -⟩ := covers_head hm (book_written h)
  have hl : List.Forall₂ VerifiableInference.Desc.Alike₂ WP.shared.blocksInOrder (𝐓 pO rest Kp₁ w).bs :=
    ProofFile.Honest.K14.alike_shared_at_laid h.head.scope h.head.laid
  have Q := (VerifiableInference.Desc.FileDescription.planOk_ok _).1 h.head.laid.planOk
  have e₁ : A.H.shared = sharedWithUO matrixInput A.Z :=
    congrArg (fun A₀ : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit => A₀.H.shared) (eq_ofFill base)
  exact walk_shared hm hO' (𝐋 pO rest Kp₁ w) rfl hl Q.blocks₂
    (by
      show AtPublicFiles.Stops.NoStop A.H.shared
      rw [e₁]
      exact noStop_withUO h.head matrixInput)
    (fun _ => rfl) (readsBase h).weights (readsBase h).rand _ _ () rfl rfl rfl rfl hLU hLO
    (treesU_head hm) c2 c5

/-- **`MemberPaid` at member 0.** -/
theorem zero_at_term (pO : P12)
    (rest : Coins A.B → Common FullSizeMatrix IndexCommitterCoins TableKey → List Fmt.Drawn → WtShared)
    (w : Common FullSizeMatrix IndexCommitterCoins TableKey)
    (hb : blocks (K1.qAt A.Z h.places) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (F : WalkFacts (𝐓 pO rest (fun _ s s' => s' = s) w) 12) :
    MemberPaid (𝐓 pO rest (fun _ s s' => s' = s) w)
      (SaidField (𝐓 pO rest (fun _ s s' => s' = s) w) BaseNil) 0 := by
  have hl : List.Forall₂ VerifiableInference.Desc.Alike₂ WP.shared.blocksInOrder
      (𝐓 pO rest (fun _ s s' => s' = s) w).bs :=
    ProofFile.Honest.K14.alike_shared_at_laid h.head.scope h.head.laid
  have hf := front_at (cF := h.firstChain) hb
  obtain ⟨x0, tl, he, hl₀⟩ : ∃ x0 tl, (𝐓 pO rest (fun _ s s' => s' = s) w).bs.take 9 = x0 :: tl ∧
      Desc.K14.Honest.Like x0 (frontBlock A.Z.p.chains) := by
    cases hf with
    | cons a _ => exact ⟨_, _, rfl, a⟩
  have hb₀ : (𝐓 pO rest (fun _ s s' => s' = s) w).bs[0]? = some x0 := by
    have e := congrArg (·[0]?) he
    simpa using e
  exact paid_zero (𝐋 pO rest (fun _ s s' => s' = s) w) F (by omega) rfl A.Z.p.chains hb₀ hl₀ hl
    (fun _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ c hc => absurd hc List.not_mem_nil)
    (fun _ s _ _ _ p hp => by
      obtain rfl : p = ⟨2, none, 0, .frame⟩ := (Option.some.inj hp).symm
      rfl)
    (fun _ s _ _ s' _ hk => hk _ rfl)
    (fun _ _ _ _ _ _ => trivial)

/-- **No half of the base prover stands at the chain's end.** -/
theorem none_at_end (base : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL matrixFilling = .ok A)
    (hb : blocks (K1.qAt A.Z h.places) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    {pO : P12} (hO' : (fourOf h.places).O = some pO) :
    (A.H.shared.find? fun g =>
      g.place == (H2K.JointK.sharedEnd ProofFile.Cl (K1.qAt A.Z h.places) h.places).place) = none := by
  have e₁ : A.H.shared = sharedWithUO matrixInput A.Z :=
    congrArg (fun A₀ : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit => A₀.H.shared) (eq_ofFill base)
  have hm := h.head.toAtMg
  have hpiece : (H2K.JointK.sharedEnd ProofFile.Cl (K1.qAt A.Z h.places) h.places).place.piece = 11 := rfl
  rw [e₁]
  unfold sharedWithUO
  rw [nowSharedBy_at_head h.head (matrixInput.weights A.Z)]
  refine List.find?_eq_none.2 fun g hg => ?_
  have hne : g.place.piece ≠ 11 := by
    rcases List.mem_append.1 hg with hg | hg
    · rcases List.mem_append.1 hg with hg | hg
      · rw [List.mem_append, halves_eq, sendHalves_eq, List.mem_append] at hg
        rcases hg with (hg | hg) | hg
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
          rcases hg with rfl | rfl | rfl
          · exact (by decide : ¬ (1 : ℕ) = 11)
          · exact (by decide : ¬ (4 : ℕ) = 11)
          · exact (by decide : ¬ (7 : ℕ) = 11)
        · split at hg
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
            subst hg
            exact (by decide : ¬ (8 : ℕ) = 11)
          · cases hg
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
          rcases hg with rfl | rfl
          · exact (by decide : ¬ (2 : ℕ) = 11)
          · exact (by decide : ¬ (5 : ℕ) = 11)
      · rw [halfU_at_head hm b1 b2 b3 b4 b5 b6 b7 b8 hb] at hg
        obtain rfl := List.mem_singleton.1 hg
        have hp : (fourOf h.places).U.place = placeU := p12At_place _ _
        show (fourOf h.places).U.place.piece ≠ 11
        rw [hp]
        decide
    · rw [halfO_at_head hm b1 b2 b3 b4 b5 b6 b7 b8 hb _ hO'] at hg
      obtain rfl := List.mem_singleton.1 hg
      have hp : pO.place = placeO := by
        obtain ⟨nO, -, rfl⟩ := Option.map_eq_some_iff.1 hO'
        exact p12At_place _ _
      show pO.place.piece ≠ 11
      rw [hp]
      decide
  simp only [beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true]
  intro e
  exact hne (e ▸ hpiece)

end ProofFile.Honest.Term

end

#print axioms ProofFile.Honest.Term.walk_at_term
#print axioms ProofFile.Honest.Term.zero_at_term
#print axioms ProofFile.Honest.Term.none_at_end
