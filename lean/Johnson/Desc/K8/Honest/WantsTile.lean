-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/WantsTile.lean: THE SMALLNESS TEST: THE LIST OF EXPECTED PIECES THAT THE
VERIFIER's SECOND COMPUTATION MAKES (`wants`, OnBytes/Model/Tail.lean: a function of tau and mz
alone) TILES A RECTANGLE OF tau ROWS AND 2 mz COLUMNS: ARITHMETIC, WHERE tau IS NOT 0. It pays what
`Added8.tile` (Johnson/Desc/K8/Honest/LeftRest.lean) asks of the list, and three of the ten fields
of `WantPub`. None of the library's goals.

  **`wants_tile`**   tl.wants = some (nbW, W) · 0 < tl.tau ⊢ no two pieces of W meet · their areas
                   add up to tau * (2 mz) · each piece's rows lie below tau, its columns below 2 mz,
                   and its virtual row below 2 nbW
  `wantPub_of_front`   what the pieces' half of the tests on weights asks of an expected piece
                   (`PieceFront`, Johnson/Desc/K8/Honest/PieceWhole.lean) · the plan's piece lies in
                   the digits' array · the three bounds ⊢ WantPub: six sentences stand in both; they
                   need not be asked twice
The unfolding of `wants` follows the proof of the library's `wants_rows`
(Johnson/Desc/First/Link/Law/CoefsFit.lean), which says that the list names every virtual row below
2 nbW. Kin, not called: `wants_rp` (Johnson/Desc/K8/Honest/SecondNz.lean: every expected piece has a
row).
Limits. ON PUBLIC NUMBERS ALONE: no ledger, no run, no prover. 0 < tl.tau IS A PREMISE, PAID BY
NOBODY HERE: at tau = 0 the first expected piece has one row, so the sentences fail, and the
verifier's own test says no. Nothing on whether the plan's pieces are the expected ones: that stays
in `WantPub`.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.LeftRest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims

/-- **THE EXPECTED PIECES TILE THE RECTANGLE.** -/
theorem wants_tile (tl : HTailF2) (nbW : Nat) (W : List Want) (hw : tl.wants = some (nbW, W))
    (h0 : 0 < tl.tau) :
    (W.Pairwise fun w x => ¬ TailClaims.Meets w x) ∧
      W.foldl (fun s w => s + w.Rp * w.Cp) 0 = tl.tau * (2 * tl.mz) ∧
      ∀ w ∈ W, w.r0 + w.Rp ≤ tl.tau ∧ w.c0 + w.Cp ≤ 2 * tl.mz ∧ w.row < 2 * nbW := by
  have hle : 2 ^ Nat.log2 tl.tau ≤ tl.tau := Nat.log2_self_le (Nat.pos_iff_ne_zero.1 h0)
  unfold HTailF2.wants at hw
  simp only at hw
  split at hw
  · exact nomatch hw
  · obtain ⟨e1, e2⟩ := Prod.mk.inj (Option.some.inj hw)
    subst e1
    subst e2
    generalize 2 ^ Nat.log2 tl.tau = a at hle ⊢
    by_cases hr : (tl.tau - a != 0) = true
    · simp only [hr, if_true]
      refine ⟨?_, ?_, ?_⟩
      · simp [TailClaims.Meets]
      · simp
        have e : tl.tau = a + (tl.tau - a) := by omega
        generalize tl.tau - a = b at e
        rw [e]
        ring
      · intro w hm
        simp at hm
        rcases hm with rfl | rfl | rfl | rfl <;> simp <;> omega
    · have hz : tl.tau - a = 0 := by simpa using hr
      simp only [hr, Bool.false_eq_true, if_false]
      refine ⟨?_, ?_, ?_⟩
      · simp [TailClaims.Meets]
      · simp
        have e : tl.tau = a := by omega
        rw [e]
        ring
      · intro w hm
        simp at hm
        rcases hm with rfl | rfl <;> simp <;> omega

/-- Six sentences stand in both structures. -/
theorem wantPub_of_front {tl : HTailF2} {g : Forest.Heard} {w : Want} (P : PieceFront tl g w)
    (ht : ((tl.zOf w.call).pieces.getD w.i {}).tree = tl.ix.ZZ) (hR : w.r0 + w.Rp ≤ tl.tau)
    (hK : w.c0 + w.Cp ≤ 2 * tl.mz) (hh : w.row < 2 * tl.zzBlocks + 2) : WantPub tl w :=
  ⟨P.mem, ht, P.row.symm, P.r0.symm, P.Rp.symm, P.c0.symm, P.Cp.symm, hR, hK, hh⟩

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.wants_tile
#print axioms VerifiableInference.Desc.First.K8.Honest.wantPub_of_front
