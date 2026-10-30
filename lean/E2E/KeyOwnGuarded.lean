-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyOwnGuarded.lean: a seated proximity test behind the guard, whose rows taken in may have a written-out factor, is
accepted from the pair of a thread and what is said, at every letter for a fall.

  `K12SeatedGuarded`: a seat, the half behind the guard, and `OwnFrontDense` (E2E/KeyOwnDense.lean) at the stands of the pair.
  `acceptedS_guarded`: the conclusion.

It stands on `saysYes_guarded` (K12/FieldGuardLift.lean, IOP's). No member of the structure is given here.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyOwnDense
import Johnson.Desc.ProofFile.Honest.K12.FieldGuardLift

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)

variable {W X S Cl V Pb : Type} {Bk : ProverCoinCounts}

/-- **A seat, the half behind the guard, and `OwnFrontDense` at the stands of the pair.** -/
structure K12SeatedGuarded (T : Thread Bk S Cl V W X Pb) (Said : ℕ → Coins Bk → Mid W X → Prop) (b : ℕ)
    (J : TestJob W X) (enter : S → Except String T12) (leave : S → T12 → Except String S) :
    Prop where
  member : ∃ blk, T.bs[b]? = some blk ∧ SeatOf blk J enter leave
  half : (T.hs.find? fun g => g.place == J.p.place) = some (proverSideOfProximityTest J : Placed V W X).needsField
  stages : ∃ s t rest, J.p.nums.stages = s :: t :: rest ∧ s.k = (sgOf s).h + (sgOf s).g
  opened : ∀ k st m E, ThrS T Said b k st m E → m.opened.isSome = true
  stands : ∀ k st m E (c : RowCoins [(firstPart J : Part V W X), restPart J]),
    ThrS T Said b k st m E →
    lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) J.p.place
      [(firstPart J : Part V W X), restPart J] 0 = .ok c →
    OwnFrontDense J enter leave st m E c

/-- **It is accepted, from the pair, whatever the letter for a fall says.** -/
theorem acceptedS_guarded (T : Thread Bk S Cl V W X Pb) (Said : ℕ → Coins Bk → Mid W X → Prop)
    (b : ℕ) (J : TestJob W X) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (h : K12SeatedGuarded T Said b J enter leave)
    (fall : ℕ → S → List Fmt.Drawn → Option String) : AcceptedS T Said fall b := by
  obtain ⟨s, t, rest, hst, hk⟩ := h.stages
  obtain ⟨blk, hblk, hseat⟩ := h.member
  have hpl := hseat.place
  have hp : ((proverSideOfProximityTest J : Placed V W X).place == J.p.place) = true := by
    show (J.p.place == J.p.place) = true
    exact beq_self_eq_true _
  have f1 : ([(proverSideOfProximityTest J : Placed V W X)].find? fun g => g.place == J.p.place) =
      some (proverSideOfProximityTest J : Placed V W X) := by
    simp [List.find?, hp]
  have f2 : ([(proverSideOfProximityTest J : Placed V W X)].find? fun g => g.place == blk.place) =
      some (proverSideOfProximityTest J : Placed V W X) := by
    rw [hpl]
    exact f1
  have hf : (T.hs.find? fun g => g.place == blk.place) =
      some (proverSideOfProximityTest J : Placed V W X).needsField := by
    rw [hpl]
    exact h.half
  exact acceptedS_of_saysYes T Said hblk
    (saysYes_guarded (proverSideOfProximityTest J) hf f2 h.opened
      (saysYes_seat T.φ Bk T.chain T.ft [proverSideOfProximityTest J] blk J enter leave hseat (fall b) (ThrS T Said b) s t
        rest hst hk f1 fun k st m E ds c hT hd _ hc =>
          k12At_of_dense J enter leave st m E c (h.stands k st m E c hT hc) ds hd))
    (fun _ _ _ _ x => x) fun _ _ x => x

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.acceptedS_guarded
