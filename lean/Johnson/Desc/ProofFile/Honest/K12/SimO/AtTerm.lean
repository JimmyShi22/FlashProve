-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator at the proximity test on G_omega: the row is the base filling's.
/-
Johnson/Desc/ProofFile/Honest/K12/SimO/AtTerm.lean: UNDER THE HEAD: the pair of parts that the base filling lays at ⟨2, none, 10, K12⟩ (not read through to `onlineFilling`), `halfO` (K12/AtProof/HalfO.lean, in `sharedWithUO`, K12/AtProof/HalfOAtPure.lean), is the parts of `omegaRow` (SimO/Top.lean) at the real
job: one equation. And that row as a row without letters, as the frame's `SLot` takes it.

  `jobOmegaReal`       the real job, as `halfO_at_head` names it
  `halfO_is_omegaRow`  **the one equation**
  `omegaUnlettered`, `omegaUnlettered_half`   the row without letters, at `OnOmega` and `budBoth`; its half

Limits. A join. The door is `doorOmegaF` at `colsOpened`; nothing here pays `OnOmega`. The equation is at the unread input: `fillT` reads it through `OnlineProverParts.through`, which this file does not cross. No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.SimO.Top
import Johnson.Desc.ProofFile.Honest.K12.AtProof.HalfOAtPure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc (Block K1.qAt)
open VerifiableInference.Desc.K12 (P12 T12)
open Desc.K14 (St blocks)
open OnBytes (TableKey)
open ProofFile.Honest.K12.Light (jobAtOmega doorOmegaF colsOpened sentOf omegaRow OnOmega budBoth)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {W₀ V X Pb : Type}

/-- The real job at the test, at the head's letters. -/
def jobOmegaReal (Zp : ProofFile.Pub) (Np : H2U.Places4) (bs : List (Block St Unit)) (wt : W₀ → Weights) (pO : P12) :
    TestJob (Common W₀ IndexCommitterCoins TableKey) Unit :=
  (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO
    (doorOmegaF (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) bs (fourOf Np).U
      (fun w : Common W₀ IndexCommitterCoins TableKey => w.key) colsOpened)
    (fun w => wt w.w₀) (fun w => randAt (K1.qAt Zp Np) w.rc) none).toRun.toTest

/-- **The pair that the base filling lays is the parts of the row.** -/
theorem halfO_is_omegaRow (h : P5J.AtMg o Z D₀ r₀ Zp Np cF) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) (wt : W₀ → Weights) {pO : P12}
    (hO : (fourOf Np).O = some pO) (Js : SimJob Pb) :
    halfO wt Zp = [⟨pO.place, (omegaRow (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) Js).map (·.1)⟩] := by
  rw [halfO_at_head h b1 b2 b3 b4 b5 b6 b7 b8 hb wt hO]
  rfl

/-- The row without letters. -/
def omegaUnlettered (φ : Face V (Common W₀ IndexCommitterCoins TableKey) Pb) (J : TestJob (Common W₀ IndexCommitterCoins TableKey) Unit)
    (Js : SimJob Pb) (chain : ℕ) (os : List (Fmt.Shape × Fmt.TreeSource)) :
    Unlettered V (Common W₀ IndexCommitterCoins TableKey) Unit Pb :=
  { place := J.p.place, row := omegaRow J Js, On := OnOmega φ J Js chain os, bud := budBoth Js }

theorem omegaUnlettered_half (φ : Face V (Common W₀ IndexCommitterCoins TableKey) Pb)
    (J : TestJob (Common W₀ IndexCommitterCoins TableKey) Unit) (Js : SimJob Pb) (chain : ℕ)
    (os : List (Fmt.Shape × Fmt.TreeSource)) :
    (omegaUnlettered φ J Js chain os).half = (proverSideOfProximityTest J : Placed V _ Unit).needsField := rfl

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.jobOmegaReal
#print axioms ProofFile.Honest.K12.AtProof.halfO_is_omegaRow
#print axioms ProofFile.Honest.K12.AtProof.omegaUnlettered
#print axioms ProofFile.Honest.K12.AtProof.omegaUnlettered_half
