-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Row/K5RowSix.lean: CONDITIONAL: KIND K5's ROW OF "THE FOURTEEN", AND ITS
LOT's
SKELETON, FROM SIX BINDERS. Two calls; nothing is evaluated.
  **`k5_row_six`**, **`k5_lot_skel_six`** (hS) (hR) (hZ) (hG) (h₄) (hm): the ends of `k5_row_own`
  and
    `k5_lot_skel_own` (K5RowOwn.lean; copied here), their binders h₁ (162 rounds) and h₂ (the test
    on the plan's own numbers) paid by `h1_in_scope`, `h2_in_scope` (K5OwnScope.lean) from hS, hR
    and hZ.
WHAT IT BUYS: two of the eight binders fall, at all public files in the goals' scope, free of any
twin
of a plan and of any tie to one.
WHAT IT DOES NOT: h₄ (`claimsOkAtQ a = true` at each plan: still a walk at each plan) · hm (the
planner's three lists for the proof file are the written ones) · hZ, hG (the front and the blank
ground
return): NONE OF THE FOUR IS SHOWN AT ANY PUBLIC FILES BY LEAN's KERNEL. hS, hR are the goals' own
premises. Implications.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Row.K5RowOwn
import Johnson.Desc.First.Att.Row.K5OwnScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Row
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att.P (claimsOkAtQ)
open VerifiableInference.PlanWritten (toldRounds)
open VerifiableInference.Number.ByRuns (proofThree)

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground}

/-- **THE ROW, FROM SIX BINDERS.** -/
theorem k5_row_six (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction Pb.pol lay Pb.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀)
    (h₄ : ∀ g, g < 12 → ∀ a, Z.p.X.A[g]? = some a → claimsOkAtQ a = true)
    (hm : Z.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan]) :
    ∃ P : ℕ → Attention.Plan, (∀ g, g < 12 → Z.p.X.A[g]? = some (P g)) ∧
      H2K5.k5OwnN Z G₀ = (List.range 12).map (the_block Z G₀ P) ∧
      (∀ g, g < 12 →
        (the_block Z G₀ P g).place = ⟨1, some (2 * g + 1), 3, .K5⟩ ∧
          (the_block Z G₀ P g).rounds.length = 162 ∧
          (the_block Z G₀ P g).oracles.length = 162 ∧ toldRounds (the_block Z G₀ P g) = [] ∧
          (the_block Z G₀ P g).before = [(1, 4 + 6 * g)]) ∧
      ∀ g, g < 12 → (the_block Z G₀ P g).planOk = true :=
  k5_row_own hS hR hZ hG (h1_in_scope hS hR hZ) (h2_in_scope hS hR hZ) h₄ hm

/-- **THE LOT's SKELETON IS THE WRITTEN ONE, FROM SIX BINDERS.** -/
theorem k5_lot_skel_six (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction Pb.pol lay Pb.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀)
    (h₄ : ∀ g, g < 12 → ∀ a, Z.p.X.A[g]? = some a → claimsOkAtQ a = true)
    (hm : Z.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan]) :
    ProofFile.Sk.lotSk G₀ (H2K5.lotN Z) =
      { name := "K5: the attention segments' own rounds", letters := false, still := [],
        blocks := (List.range 12).map k5SkelW
        batch := fun _ => none, each := fun _ => false, tests := fun _ => false } :=
  k5_lot_skel_own hS hR hZ hG (h1_in_scope hS hR hZ) (h2_in_scope hS hR hZ) h₄ hm

end H2K5.Row

#print axioms H2K5.Row.k5_row_six
#print axioms H2K5.Row.k5_lot_skel_six
