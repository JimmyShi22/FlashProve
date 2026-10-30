-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/LdAtLeft.lean: the list of places and shapes at the first chain's codes IS the closed
term at which what is left of the last chain's field is laid (`P5J.L0.ldAt Zp`,
Johnson/P5J/L0/LastLeftAt.lean), from the head and one named test on the plan. Two theorems.
Joinings over Johnson/P2LawR/LaidAtLeft.lean.

  `ldAt_is_full`: `P5J.L0.ldAt Zp = LFull`.
  `ld_at_head`: `K12.Door.laidAtCodes Zp.first.codes Zp.made.proof.1 = some (P5J.L0.ldAt Zp)`.
    WHAT STAYS, BY NAME: hy : `madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true`.

Limits. hy is shown nowhere here. In scope alone. No example. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.P2LawR.LaidAtLeft
import Johnson.P5J.L0.LastLeftAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P2Law.Left
open OnBytes OnBytes.Maker
open VerifiableInference.Desc
open VerifiableInference.Desc.K13.Law (LFull)
open VerifiableInference.PlanWritten (madePinnedAt)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r' : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- The term `L0.ldAt Zp` is the written list. -/
theorem ldAt_is_full (h : P5J.AtMg o Z D r' Zp Np cF)
    (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) :
    P5J.L0.ldAt Zp = LFull :=
  ld_is_full h hy

/-- **The list at the first chain's codes is the term `L0.ldAt Zp`.** -/
theorem ld_at_head (h : P5J.AtMg o Z D r' Zp Np cF)
    (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) :
    K12.Door.laidAtCodes Zp.first.codes Zp.made.proof.1 = some (P5J.L0.ldAt Zp) := by
  rw [ldAt_is_full h hy]
  exact hL_at_head h hy

end P2Law.Left

#print axioms P2Law.Left.ldAt_is_full
#print axioms P2Law.Left.ld_at_head
