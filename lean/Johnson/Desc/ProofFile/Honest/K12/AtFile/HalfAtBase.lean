-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/HalfAtBase.lean: at the base prover's shared list, at the place of
the test on G_u, the search finds the test's half, plain, at the job that `halfU` makes. The premise `half` of
`LaidU` (FiveNine.lean) at that list.

  `six_elsewhere`   none of the six other sides stands at the test's place
  `half_found`   the statement, at `sharedWithUO` (K12/AtProof/HalfOAtPure.lean)

Limits. At the base list, with the index's reader I.weights Zp and the encoded columns of `encW`: the list read
through is another list. Nothing on what the half plays. Nothing on completeness, on soundness or on what is
hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.StandNine
import Johnson.Desc.ProofFile.Honest.K12.AtProof.HalfOAtPure
import Johnson.Desc.ProofFile.Honest.K14.AtWiderShared

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open OnBytes (TableKey)
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc (K1.qAt)
open Desc.K14 (St blocks)
open ProofFile.Honest.K14 (proverSidesOfSharedRounds proverSidesOfSharedSendings halves_eq sendHalves_eq nowSharedBy_at_head randNow)
open ProofFile.Honest.K12.AtProof (fourOf placeU p12At_place halfU halfU_at_head randAt sharedWithUO)
open ProofFile.Honest.K12.Light (jobHeadU)

variable {W₀ : Type}

/-- None of the six other sides stands at the test's place. -/
theorem six_elsewhere {Q : Desc.K14.P14} (wt : W₀ → Weights) :
    ∀ x ∈ (proverSidesOfSharedRounds { S := Q.S, atPoint := 0, atZeta := 6 } wt ++
      proverSidesOfSharedSendings { P := Q, atPoint := 0 } wt (randNow Q) :
        List (Placed Empty (Common W₀ IndexCommitterCoins TableKey) Unit)), x.place ≠ placeU := by
  intro x hx
  rw [List.mem_append, halves_eq, sendHalves_eq, List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact (by decide : ProofFile.Honest.K14.place 1 ≠ placeU)
    · exact (by decide : ProofFile.Honest.K14.place 4 ≠ placeU)
    · exact (by decide : ProofFile.Honest.K14.place 7 ≠ placeU)
  · split at hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      subst hx
      exact (by decide : ProofFile.Honest.K14.place 8 ≠ placeU)
    · cases hx
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact (by decide : ProofFile.Honest.K14.sendPlace 2 ≠ placeU)
    · exact (by decide : ProofFile.Honest.K14.sendPlace 5 ≠ placeU)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **The base list finds the test's half.** -/
theorem half_found (h : P5J.AtMg o Z D r₀ Zp Np cF) (hA : P5J.AtMgA o Z D r₀ Zp Np cF x₀)
    (I : WiderIn W₀) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    ((sharedWithUO I Zp).find? fun g => g.place == (fourOf Np).U.place) =
      some (proverSideOfProximityTest (jobHeadU Zp Np [b1, b2, b3, b4, b5, b6, b7, b8]
                         (fun w rc i x => (Bind.ForProver.encW Zp (I.weights Zp w) rc i x).map (·.map OnBytes.Slice.ofF))
                         (fun w => I.weights Zp w.w₀) (fun w => randAt (K1.qAt Zp Np) w.rc) none).toRun.toTest) := by
  have e := nowSharedBy_at_head hA (I.weights Zp)
  unfold sharedWithUO
  rw [e]
  show (((_ ++ halfU (I.weights Zp) (fun w => Bind.ForProver.encW Zp (I.weights Zp w)) Zp) ++ _).find? _) = _
  rw [halfU_at_head h b1 b2 b3 b4 b5 b6 b7 b8 hb, List.append_assoc, List.singleton_append]
  refine find_half _ _ _ _ rfl fun x hx => ?_
  have hp : (fourOf Np).U.place = placeU := p12At_place _ _
  rw [hp]
  exact six_elsewhere _ x hx

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.six_elsewhere
#print axioms ProofFile.Honest.K12.AtFile.half_found
