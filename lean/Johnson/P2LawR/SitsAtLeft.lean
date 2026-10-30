-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/SitsAtLeft.lean: the five tests on the plan that the last table's premise hRc spends
(`ToldDesc.planSitsB`, Johnson/ToldDescR/OwnSitsBools.lean: 4 < 197; the laying's places number 4
and 197 are the two elder seats; the chain's messages number 4 and 197 have their shapes) ACCEPT at
the closed term `P5J.L0.ldAt Zp`, from the head and one named test on the plan. One theorem. A
joining.

  `sits_at_head`: (h : `P5J.AtMg o Z D r' Zp Np cF`) (hy) ⊢ `planSitsB (L0.ldAt Zp)
    (msgsOfChain Zp.made.proof.1) (vAt Zp (At.N Zp cF)) 4 197 = true`.
    ONE CALL of `Second.Seam.planSits_at_N` (Johnson/Second/Seam/PlanSitsInScope.lean), turned into
    the test by `ToldDesc.planSits_iff` and laid at the closed term by `ldAt_is_full`
    (Johnson/P2LawR/LdAtLeft.lean).
    OFF THE HEAD: the scope · what the public part's maker returns · `laid_at_head`.
    WHAT STAYS, BY NAME: hy : `madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true`.

Limits. hy is shown nowhere here. In scope alone; 4 and 197: the full size alone. No example.
Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.P2LawR.LdAtLeft
import Johnson.Second.Seam.PlanSitsInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P2Law.Left
open OnBytes OnBytes.Maker
open VerifiableInference.Desc
open VerifiableInference.PlanWritten (madePinnedAt)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r' : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- **The five tests on the plan accept at the term `L0.ldAt Zp`.** -/
theorem sits_at_head (h : P5J.AtMg o Z D r' Zp Np cF)
    (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) :
    ToldDesc.planSitsB (P5J.L0.ldAt Zp) (K12.Door.msgsOfChain Zp.made.proof.1)
      (LLT25.vAt Zp (P5J.At.N Zp cF)) 4 197 = true := by
  rw [ldAt_is_full h hy]
  exact (ToldDesc.planSits_iff _ _ _ _ _).2
    (Second.Seam.planSits_at_N h.scope h.laid.pub hy (laid_at_head h) cF)

end P2Law.Left

#print axioms P2Law.Left.sits_at_head
