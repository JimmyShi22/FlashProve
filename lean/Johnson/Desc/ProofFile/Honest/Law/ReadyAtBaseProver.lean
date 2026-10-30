-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/ReadyAtBaseProver.lean: from `ReadyDebts` at the online return to
`ReadyDebts` at the base filling's return, and so `ready` at the base prover, at every index in range
and request with a trace. No definition; two theorems.

  `readyDebts_base_of_online`   what the online return owes, paid, the base return's is paid:
                                the base filling's sides read through are the online return's, and
                                a side pays just where it pays read through (`sidePays_of_thru`)
  `ready_at_base_of_online`     so `ready` returns at the base prover

Limits.
  * Both returns are premises.
  * What `ReadyDebts` pays is that `ready` returns: nothing here says that a part plays, or that a
    verifier accepts.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.ReadyAtOnline
import Johnson.Desc.ProofFile.Honest.AtPureBook
import E2E.BaseMaker

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace ProofFile.Honest.Term
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge

variable {Z : VerifierAndGoals.PublicFiles} {returned : OnlineReturn Z} {A₀ : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- **What the online return owes, paid, the base return's is paid.** -/
theorem readyDebts_base_of_online (hA : onlineMaker Z = .ok returned) (hM : baseMaker Z = .ok A₀)
    (Dt : ReadyDebts returned.F returned.B returned.H) : ReadyDebts A₀.F A₀.B A₀.H := by
  obtain ⟨eZ, eG, eF, eB⟩ := atPure_book_same hM hA
  obtain ⟨hw, s1, s2, s3, hd⟩ := atPure_tests hM
  obtain ⟨-, -, -, -, -, -, -, e1, e2, e3, -⟩ := atPure_ok hA
  obtain ⟨-, -, -, -, -, -, -, f1, f2, f3, -⟩ := atPure_ok hM
  have once₁ := Dt.once₁
  have once₂ := Dt.once₂
  have once₃ := Dt.once₃
  rw [e1] at once₁
  rw [e2] at once₂
  rw [e3] at once₃
  refine ⟨by rw [eF]; exact Dt.plan, by rw [eF]; exact Dt.places, hw, List.isEmpty_iff.1 s1,
    List.isEmpty_iff.1 s2, List.isEmpty_iff.1 s3, ?_, ?_, ?_, hd, ?_, ?_, ?_⟩
  · rw [f1, eZ, eG]
    have q : twice (firstOf returned.Z returned.G (onlineBase.lots.map
        (HLot.thru (Local.thru id (tableCoins Z)) (Local.thru id (tableCoins Z))))) = [] := once₁
    rw [firstOf_through, twice_thru] at q
    exact q
  · rw [f2, eZ, eG]
    have q : twice ((onlineBase.shared returned.Z returned.G).map
        (Placed.thru id (Common.thru id (tableCoins Z)))) = [] := once₂
    rw [twice_thru] at q
    exact q
  · rw [f3, eZ, eG]
    have q : twice ((onlineBase.second returned.Z returned.G).map
        (Placed.thru (Local.thru id (tableCoins Z)) (Local.thru id (tableCoins Z)))) = [] := once₃
    rw [twice_thru] at q
    exact q
  · intro κ q hq hk
    rw [f1, eZ, eG] at hq
    obtain ⟨L, hL, hx⟩ := List.mem_flatMap.1
      (hq : q ∈ onlineBase.lots.flatMap fun L => L.halves returned.Z returned.G)
    have hp := Dt.pays₁ κ _ (through_side_mem id (tableCoins Z) matrixInput.dummy hA hL hx) hk
    rw [eB, eF]
    exact sidePays_of_thru _ _ hp
  · intro κ q hq hk
    rw [f2, eZ, eG] at hq
    have hm : q.thru id (Common.thru id (tableCoins Z)) ∈ returned.H.shared := by
      rw [e2]
      exact List.mem_map_of_mem hq
    have hp := Dt.pays₂ κ _ hm hk
    rw [eB, eF]
    exact sidePays_of_thru _ _ hp
  · intro κ q hq hk
    rw [f3, eZ, eG] at hq
    have hm : q.thru (Local.thru id (tableCoins Z)) (Local.thru id (tableCoins Z)) ∈
        returned.H.second := by
      rw [e3]
      exact List.mem_map_of_mem hq
    have hp := Dt.pays₃ κ _ hm hk
    rw [eB, eF]
    exact sidePays_of_thru _ _ hp

/-- **`ready` returns at the base prover, at every index in range, every request with a trace, every
table's randomness and every run's coins.** Conditional on the two returns and on what the online
return owes. -/
theorem ready_at_base_of_online (hA : onlineMaker Z = .ok returned) (hM : baseMaker Z = .ok A₀)
    (Dt : ReadyDebts returned.F returned.B returned.H) {w₀ : FullSizeMatrix} {x : ProofFile.Inst}
    (hi : A₀.H.inRange w₀ = true) (ht : (A₀.H.trace w₀ x).isSome = true) (rc : IndexCommitterCoins)
    (k : Coins A₀.B) : ∃ R, ready A₀.F A₀.B A₀.H w₀ rc x k = .ok R :=
  ready_of_sides (readyDebts_base_of_online hA hM Dt) hi ht rc k

end ProofFile.Honest.Term

#print axioms ProofFile.Honest.Term.readyDebts_base_of_online
#print axioms ProofFile.Honest.Term.ready_at_base_of_online
