-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/OwesRest.lean: FirstOwed's FIELDS THAT ARE NO KIND, AT THE BASE PROVER: noHalf, hno, hhalf, htst and hstl paid
here, and hatt by k5_lays_lookR_att; hσ, hnx, hs and k12 stay named.

  lots_no_frame, no_frame_at_base   no side at a place of kind frame, at every letter of the filling
  quiet_places                      a kernel fact: the places at + 2, + 4, + 6 behind a link's rounds are K9's or frames
  hno_at_base, hstl_at, hatt_at     three of the fields, each on its own
  first_owed_rest                   **FirstOwed** from the kinds' fields and these four

Limits. An implication. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.OwesByKind
import Johnson.AtFull.Shape.Scope.FirstChainFilled
import Johnson.Desc.ProofFile.Honest.K9.StepSilent
import Johnson.Desc.ProofFile.Honest.K9.NoSideAtBase
import Johnson.Desc.ProofFile.Honest.K5.Law.LaysLookRAtt
import Johnson.AtFull.Shape.ValsTSAtStand

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape.Scope
open VerifiableInference.Desc (Place KindName)
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile (Pub Ground SecondHashFunctionArgument)

variable {W₀ : Type} (I : WiderIn W₀) (o : SecondHashFunctionArgument) (Sz : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)

theorem lots_no_frame (Zq : Pub) (G : Ground) :
    ∀ M ∈ (onlineProverPartsInUse I o Sz O).lots, ∀ g ∈ M.halves Zq G, g.place.kind ≠ KindName.frame := by
  intro M hM g hg h9
  rw [widerFillAtCPUOWM_lots] at hM
  simp only [List.mem_append, List.mem_singleton] at hM
  rcases hM with ((h | rfl) | rfl) | rfl
  · rw [widerFillAt_lots] at h
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 h
    have hk : q.2 = KindName.frame := ((FirstFill.widerKinds I o Sz O Zq G).all q hq g hg).symm.trans h9
    have hin : KindName.frame ∈ (widerPairs I o Sz O).map (·.2) := hk ▸ List.mem_map.2 ⟨q, hq, rfl⟩
    have hno : KindName.frame ∉
        ([KindName.K1, .K2, .K7, .K11, .K13, .K3, .K4, .K5, .K6, .K8] : List KindName) := by decide
    exact hno hin
  · have hk := closeLotAt_kinds I Sz Zq G g hg
    rw [h9] at hk
    cases hk
  · have hk := proxLotAt_kinds I Sz Zq G g hg
    rw [h9] at hk
    cases hk
  · rw [wLotAt_halves] at hg
    obtain ⟨msg, _, rfl⟩ := Option.mem_toList.1 hg |> Option.mem_map.1
    cases h9

theorem no_frame_at_base {o' : SecondHashFunctionArgument} {pol lay KL : ByteArray} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles o' pol lay KL (onlineProverPartsInUse I o Sz O) = .ok A) :
    ∀ g ∈ A.H.first, g.place.kind ≠ KindName.frame := by
  obtain ⟨-, -, -, -, -, -, -, hf, -⟩ := atPure_ok hA
  intro g hg
  rw [hf] at hg
  obtain ⟨M, hM, hx⟩ := List.mem_flatMap.1 hg
  exact lots_no_frame I o Sz O A.Z A.G M hM g hx

set_option maxRecDepth 1000000 in
theorem quiet_places : ((List.range 25).all fun l => [2, 4, 6].all fun j =>
    (P5J.At.ps[14 * l + IM.nAt l + j]?).all fun p => p.kind == KindName.K9 || p.kind == KindName.frame) = true := by
  decide +kernel

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

theorem hno_at_base (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction Sz O) = .ok A) :
    ∀ l, l < 25 → ∀ j, j = 2 ∨ j = 4 ∨ j = 6 → ∀ p,
      P5J.At.ps[14 * l + IM.nAt l + j]? = some p → ∀ g ∈ A.H.first, g.place ≠ p := by
  intro l hl j hj p hp g hg e
  have c := List.all_eq_true.1 (List.all_eq_true.1 quiet_places l (List.mem_range.2 hl)) j
    (by rcases hj with rfl | rfl | rfl <;> simp)
  rw [hp] at c
  have c' : (p.kind == KindName.K9 || p.kind == KindName.frame) = true := c
  rcases Bool.or_eq_true_iff.1 c' with k | k
  · exact K9.no_side_at_base I OnBytes.secondHashFunction Sz O hA g hg (by rw [e]; exact beq_iff_eq.1 k)
  · exact no_frame_at_base I OnBytes.secondHashFunction Sz O hA g hg (by rw [e]; exact beq_iff_eq.1 k)

/-- digitsStand speaks at the head's link alone. -/
theorem hstl_at (h : HeadAtReturn files A) (parts : FirstThreadParts A)
    (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
    (Said : Nat → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop) :
    ∀ l, l < 24 → LaysAtS (firstLetters h parts w).thread Said (14 * l + 8)
      ⟨14 * l + 9, 14 * l + 9, fun _ _ s => digitsStand A.Z l s⟩ :=
  fun l hl _ _ _ _ _ _ _ _ _ _ _ _ _ e => absurd e (by omega)

/-- The lookup on the calls lays its hearing at the attention's sentence. -/
theorem hatt_at {Bs : ProofFile.PureBase} (h : HeadAtReturn files A) (parts : FirstThreadParts A)
    (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
    (Said : Nat → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (hB : ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok Bs) :
    ∀ g, g < 12 → LaysAtS (firstLetters h parts w).thread Said (14 * (2 * g + 1) + 3)
      (riderAtt (14 * (2 * g + 1) + 4) (14 * (2 * g + 1) + 9) fun a => heardByAttention A.Z g a.g) := by
  intro g hg blk hblk k s m E ds y cols s' hT hd hS
  obtain ⟨Bs', Lk, p, u, a, q, e1, -, -, -, e4, -⟩ := Johnson.AtFull.Shape.att_batch h.head g hg
  obtain rfl : Bs = Bs' := Except.ok.inj (hB.symm.trans e1)
  obtain ⟨Bs'', base, O'⟩ := h.head.laid.opened
  obtain rfl : Bs = Bs'' := Except.ok.inj (hB.symm.trans O'.made)
  have ha : (P5J.At.X A.Z).A[g]? = some a := by
    have e : Bs.G₀.W = (P5J.At.X A.Z) := O'.W
    rw [← e]
    exact e4
  obtain ⟨o, ho, hl⟩ := laysAtS_of _ Said (K5.k5_lays_lookR_att h.head A.H parts.script _ _ _ _ _ _ _ _ _ w hg
    ha) blk hblk k s m E ds y cols s' hT hd hS
  refine ⟨o, ho, fun a' ha' => ?_⟩
  obtain rfl := Option.some.inj (ha'.symm.trans ha)
  exact hl

/-- **FirstOwed**: what stays is the kinds' fields, k12, hσ, hnx and hs. -/
theorem first_owed_rest {Bs : ProofFile.PureBase}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction Sz O) = .ok A)
    (h : HeadAtReturn files A) (parts : FirstThreadParts A) (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
    (Said : Nat → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (hB : ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok Bs)
    (k1 : KindPaid (firstLetters h parts w) Said KindName.K1)
    (k2 : KindPaid (firstLetters h parts w) Said KindName.K2)
    (k3 : KindPaid (firstLetters h parts w) Said KindName.K3)
    (k4 : KindPaid (firstLetters h parts w) Said KindName.K4)
    (k5 : KindPaid (firstLetters h parts w) Said KindName.K5)
    (k6 : KindPaid (firstLetters h parts w) Said KindName.K6)
    (k7 : KindPaid (firstLetters h parts w) Said KindName.K7)
    (k8 : KindPaid (firstLetters h parts w) Said KindName.K8)
    (k9 : KindPaid (firstLetters h parts w) Said KindName.K9)
    (k10 : KindPaid (firstLetters h parts w) Said KindName.K10)
    (k11 : KindPaid (firstLetters h parts w) Said KindName.K11)
    (k12 : PlaysS (firstLetters h parts w).thread Said 354)
    (k13 : KindPaid (firstLetters h parts w) Said KindName.K13)
    (hσ : ∀ s s', Johnson.Desc.First.ForkMerge.Returns.K11Keeps (K11.parOf A.Z Bs.G₀) s s' →
      digitsStand A.Z 24 s → digitsStand A.Z 24 s')
    (hnx : LaysAtS (firstLetters h parts w).thread Said 345
      (riderHead 346 346 fun a => a.F.next = nextSlotBehindTheHead))
    (hs : LaysAtS (firstLetters h parts w).thread Said 345
      ⟨346, 347, fun _ _ s => digitsStand A.Z 24 s⟩) :
    FirstOwed h parts w Said Bs where
  k1 := k1
  k2 := k2
  k3 := k3
  k4 := k4
  k5 := k5
  k6 := k6
  k7 := k7
  k8 := k8
  k9 := k9
  k10 := k10
  k11 := k11
  k12 := k12
  k13 := k13
  hσ := hσ
  noHalf := no_frame_at_base I OnBytes.secondHashFunction Sz O hA
  hno := hno_at_base I Sz O hA
  hhalf := ⟨_, Johnson.AtFull.Shape.k7_find I Sz O h hA hB⟩
  htst := K9.step_silent_first h parts.numbers
  hnx := hnx
  hs := hs
  hstl := hstl_at h parts w Said
  hatt := hatt_at h parts w Said hB

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.quiet_places
#print axioms Johnson.AtFull.Shape.Scope.no_frame_at_base
#print axioms Johnson.AtFull.Shape.Scope.first_owed_rest
