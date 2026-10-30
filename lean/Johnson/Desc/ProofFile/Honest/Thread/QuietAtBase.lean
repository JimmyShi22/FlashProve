-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/QuietAtBase.lean: at the base filling `onlineProverPartsInUse`, every half of
the kinds K1, K2 and K12 has no stop, so no member of the first chain with a new tree stops there.

  `quiet_placeHalf`, `quiet_lotHalves`, `quiet_wHalves`   the sender's halves
  `quiet_switchHalves`   the code switch's
  `quiet_testHalf`   the proximity test's
  `quiet_shared`, `quiet_shared_at_return`   every half of the shared chain
  `quiet_base`, `quiet_at_return`   every half of the three kinds among what the filling lays, and at a
                   return of `onlineProverFromPublicFiles` there

This file proves nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.NoStopOfSenders
import Johnson.Desc.ProofFile.Honest.Thread.FirstFillAll
import Johnson.Desc.ProofFile.Honest.K1.Law.WSideAtFill
import Johnson.Desc.ProofFile.Honest.K7.AtFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Place KindName)

section
variable {V W X Xi : Type}

theorem quiet_placeHalf (wit : W → K1.PlaceIn Xi) (J : K1.SendJob (K1.PlaceIn Xi) X) :
    RowQuiet (K1.placeHalf (V := V) wit J).parts := by
  intro p hp
  obtain rfl := List.mem_singleton.1 hp
  exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem quiet_lotHalves (wit : W → K1.PlaceIn Xi) (no : Place → Nat)
    (D : Pub → Ground → RowDataOf Xi) (Z : Pub) (G : Ground) :
    ∀ x ∈ (K1.lotHalves (V := V) (X := X) wit no D Z G), RowQuiet x.parts := by
  intro x hx
  unfold K1.lotHalves at hx
  rcases List.mem_cons.1 hx with rfl | hx
  · exact quiet_placeHalf wit _
  · obtain ⟨⟨Y, l⟩, -, hy⟩ := List.mem_flatMap.1 hx
    dsimp only at hy
    split at hy
    · cases hy
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact quiet_placeHalf wit _
      · obtain rfl := List.mem_singleton.1 hy
        exact quiet_placeHalf wit _

theorem quiet_wHalves (wit : W → K1.PlaceIn Xi) (no : Place → Nat)
    (D : Pub → Ground → RowDataOf Xi) (Z : Pub) (G : Ground) :
    ∀ x ∈ (K1.wHalves (V := V) (X := X) wit no D Z G), RowQuiet x.parts := by
  intro x hx
  unfold K1.wHalves at hx
  cases hm : OnBytes.linMessageW Z.first.lin with
  | none =>
    rw [hm] at hx
    cases hx
  | some msg =>
    rw [hm] at hx
    obtain rfl := List.mem_singleton.1 hx
    exact quiet_placeHalf wit _

theorem quiet_testHalf (J : K12.TestJob W X) : RowQuiet (K12.proverSideOfProximityTest (V := V) J).parts := by
  intro p hp
  unfold K12.proverSideOfProximityTest at hp
  rcases List.mem_cons.1 hp with rfl | hp
  · unfold K12.firstPart
    split <;> exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
  · obtain rfl := List.mem_singleton.1 hp
    exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

end

section
variable {W₀ Rc Xi Tr X : Type}

theorem quiet_switchHalves (Sd : K2.Sender) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → _) (closing : K2.Closing) (Z : Pub) (G : Ground) :
    ∀ x ∈ (K2.switchHalves (X := X) Sd D readers closing Z G), RowQuiet x.parts := by
  intro x hx
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
  intro q hq
  obtain rfl := List.mem_singleton.1 hq
  exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

end

variable {W₀ : Type}

/-- **Every half of the three kinds at the base filling has no stop.** -/
theorem quiet_base (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (Zq : Pub) (G : Ground) :
    ∀ y ∈ firstOf Zq G (onlineProverPartsInUse I o S O).lots,
      [KindName.K1, .K2, .K12].contains y.place.kind = true → RowQuiet y.parts := by
  intro y hy hk
  obtain ⟨M, hM, hyM⟩ := List.mem_flatMap.1 hy
  rw [widerFillAtCPUOWM_lots] at hM
  simp only [List.mem_append, List.mem_singleton] at hM
  rcases hM with ((h | rfl) | rfl) | rfl
  · rw [widerFillAt_lots] at h
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 h
    have hkq := (FirstFill.widerKinds I o S O Zq G).all q hq y hyM
    simp only [widerPairs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quiet_lotHalves _ _ _ Zq G y hyM
    · exact quiet_switchHalves _ _ _ _ Zq G y hyM
    all_goals (rw [hkq] at hk; cases hk)
  · have h := closeLotAt_kinds I S Zq G y hyM
    rw [h] at hk
    cases hk
  · unfold proxLotAt at hyM
    dsimp only at hyM
    split at hyM
    · split at hyM
      · obtain ⟨J, -, rfl⟩ := List.mem_map.1 hyM
        exact quiet_testHalf J
      · cases hyM
    · cases hyM
  · exact quiet_wHalves _ _ _ Zq G y hyM

/-- **Every half of the shared chain at the base filling has no stop.** -/
theorem quiet_shared (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (Zq : Pub) (G : Ground) :
    ∀ y ∈ (onlineProverPartsInUse I o S O).shared Zq G, RowQuiet y.parts := by
  intro y hy
  have hy' : y ∈ K12.AtProof.sharedWithUO I Zq := hy
  unfold K12.AtProof.sharedWithUO at hy'
  split at hy'
  · rename_i six h6
    rcases List.mem_append.1 hy' with hy1 | hy3
    · rcases List.mem_append.1 hy1 with hy0 | hy2
      · unfold nowSharedBy at h6
        obtain ⟨P, -, h6⟩ := bind_ok h6
        obtain ⟨s, -, h6⟩ := bind_ok h6
        unfold K14.sixOf at h6
        split at h6
        · cases h6
        · split at h6
          · cases h6
          · cases h6
            rcases List.mem_append.1 hy0 with hh | hh
            · unfold K14.proverSidesOfSharedRounds at hh
              rcases List.mem_append.1 hh with hh | hh
              · simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
                rcases hh with rfl | rfl | rfl <;> intro q hq <;>
                  (obtain rfl := List.mem_singleton.1 hq) <;>
                  exact ⟨fun _ _ => rfl, fun v => v.elim⟩
              · split at hh
                · obtain rfl := List.mem_singleton.1 hh
                  intro q hq
                  obtain rfl := List.mem_singleton.1 hq
                  exact ⟨fun _ _ => rfl, fun v => v.elim⟩
                · cases hh
            · unfold K14.proverSidesOfSharedSendings at hh
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
              rcases hh with rfl | rfl <;> intro q hq <;>
                (obtain rfl := List.mem_singleton.1 hq) <;>
                exact ⟨fun _ _ => rfl, fun v => v.elim⟩
      · obtain ⟨J, -, rfl⟩ := List.mem_map.1 hy2
        exact quiet_testHalf J
    · obtain ⟨J, -, rfl⟩ := List.mem_map.1 hy3
      intro q hq
      obtain ⟨q₀, hq₀, rfl⟩ := List.mem_map.1 hq
      obtain ⟨h1, h2⟩ := quiet_testHalf (V := Empty) J q₀ hq₀
      exact ⟨h1, h2⟩
  · cases hy'

/-- **At a return of `onlineProverFromPublicFiles` at the base filling.** -/
theorem quiet_at_return {I : WiderIn W₀} {o o' : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
    {pol lay KL : ByteArray} {R : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (h : onlineProverFromPublicFiles o' pol lay KL (onlineProverPartsInUse I o S O) = .ok R) :
    ∀ y ∈ R.H.first, [KindName.K1, .K2, .K12].contains y.place.kind = true → RowQuiet y.parts := by
  obtain ⟨-, -, -, -, -, -, -, hf, -⟩ := atPure_ok h
  rw [hf]
  exact quiet_base I o S O R.Z R.G

/-- **The same of the shared chain.** -/
theorem quiet_shared_at_return {I : WiderIn W₀} {o o' : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz}
    {O : OnlineProverArguments} {pol lay KL : ByteArray} {R : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (h : onlineProverFromPublicFiles o' pol lay KL (onlineProverPartsInUse I o S O) = .ok R) :
    ∀ y ∈ R.H.shared, RowQuiet y.parts := by
  obtain ⟨-, -, -, -, -, -, -, -, hs, -⟩ := atPure_ok h
  rw [hs]
  exact quiet_shared I o S O R.Z R.G

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.quiet_shared
#print axioms ProofFile.Honest.FirstThread.quiet_shared_at_return
#print axioms ProofFile.Honest.FirstThread.quiet_at_return
#print axioms ProofFile.Honest.FirstThread.quiet_lotHalves
#print axioms ProofFile.Honest.FirstThread.quiet_wHalves
#print axioms ProofFile.Honest.FirstThread.quiet_testHalf
#print axioms ProofFile.Honest.FirstThread.quiet_switchHalves
#print axioms ProofFile.Honest.FirstThread.quiet_base
