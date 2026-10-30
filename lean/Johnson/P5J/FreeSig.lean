-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/P5J/FreeSig.lean: THE FIRST PREMISE OF THE LAST TABLE's LAW (`LLT25.own3_at_rc_letter`,
Johnson/LLT25R/LastAtRc.lean) AT THE MEANING AT WHICH THE TOWER STANDS: laying the six letters of
`meaningSig` (Johnson/Desc/Sound/BordersFill.lean) over `h.mq 𝔇₀` again, at the later tables' codes,
turns nothing, where the first chain's codes and the later tables' are one. Statements and proofs:
unfolding.

  `free_dec`: THE SIXTH LETTER BY ITSELF: the promise "the committed table decodes" as `meaningQ`
    lays it over the six (through what is read off a witness: `hidAtSeat`'s field dec) IS
    `decodesOf` at the tower's decoder: by unfolding.
  **`AtMg.free_hSig`**: hcs : At.cs Zp = (p14At Zp).codes ⟹ meaningSig (p14At Zp).codes (F0T o Zp Np
  cF) (At.arr Zp) (smpNamed (p14At Zp).codes (At.seats Zp)) (At.ms Zp Z.lay) (dtK …) (h.mq 𝔇₀) =
  h.mq 𝔇₀.

Limits. hcs is a premise. 𝔇₀ is a letter. A member of the head is proved at `storedPublicFiles` and `zGap` alone
(at secondHashFunction; side library AtFullSide/Top/). Nothing on soundness.

-/
import Johnson.P5J.RowsAtMg
import Johnson.LLT25R.LastAtRc

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Slice
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound
open ToldDesc (p14At)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **The sixth letter**: the tower's meaning's promise "the committed table decodes" is the six
letters' own, at the tower's decoder. -/
theorem free_dec (h : AtMg o Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp)) :
    (h.mq 𝔇₀).decodes = decodesOf (dtK (At.EAt Z) o Zp Np cF h.plan.shape 0) := rfl

/-- **The six letters laid again turn nothing.** -/
theorem AtMg.free_hSig (h : AtMg o Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp))
    (hcs : At.cs Zp = (p14At Zp).codes) :
    meaningSig (p14At Zp).codes (F0T o Zp Np cF) (At.arr Zp)
      (smpNamed (p14At Zp).codes (At.seats Zp)) (At.ms Zp Z.lay)
      (dtK (At.EAt Z) o Zp Np cF h.plan.shape 0) (h.mq 𝔇₀) = h.mq 𝔇₀ := by
  have key : ∀ c, At.cs Zp = c →
      meaningSig c (F0T o Zp Np cF) (At.arr Zp) (smpNamed c (At.seats Zp)) (At.ms Zp Z.lay)
        (dtK (At.EAt Z) o Zp Np cF h.plan.shape 0) (h.mq 𝔇₀) = h.mq 𝔇₀ := by
    intro c e
    subst e
    rfl
  exact key _ hcs

end P5J

#print axioms P5J.free_dec
#print axioms P5J.AtMg.free_hSig
