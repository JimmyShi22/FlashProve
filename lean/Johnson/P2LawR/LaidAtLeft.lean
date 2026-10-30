-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/LaidAtLeft.lean: ONE LIST OF PLACES AND SHAPES AT THE HEAD: under the one named test
on the plan that the field hS leaves (Johnson/P2LawR/HSAtLeft.lean), the list that can be laid is
the written one, `K13.Law.LFull`, by both of its spellings. Three theorems. Joinings: each is one
call of `Second.Seam.*` (Johnson/Second/Seam/CodesOneInScope.lean) at the head's fields.

  `hL_at_head`: `K12.Door.laidAtCodes Zp.first.codes Zp.made.proof.1 = some LFull`.
  `laidOfChain_at_head`: `K12.Door.laidOfChain Zp.made.proof.1 = some LFull`.
  `ld_is_full`: `(K12.Door.laidOfChain Zp.made.proof.1).getD {} = LFull`.
    OFF THE HEAD: the scope · what the public part's maker returns · `laid_at_head`.
    WHAT STAYS, BY NAME: hy : `madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true`.

Limits. hy is shown nowhere here. In scope alone. No example. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.P2LawR.HSAtLeft
import Johnson.Second.Seam.CodesOneInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P2Law.Left
open OnBytes OnBytes.Maker
open VerifiableInference.Desc
open VerifiableInference.Desc.K13.Law (LFull)
open VerifiableInference.PlanWritten (madePinnedAt)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r' : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- **The list at the first chain's codes is the written one.** -/
theorem hL_at_head (h : P5J.AtMg o Z D r' Zp Np cF)
    (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) :
    K12.Door.laidAtCodes Zp.first.codes Zp.made.proof.1 = some LFull :=
  Second.Seam.laidAtCodes_in_scope h.scope h.laid.pub hy (laid_at_head h)

/-- **The list at the chain's own codes is the written one.** -/
theorem laidOfChain_at_head (h : P5J.AtMg o Z D r' Zp Np cF)
    (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) :
    K12.Door.laidOfChain Zp.made.proof.1 = some LFull :=
  Second.Seam.laidOfChain_in_scope h.scope h.laid.pub hy (laid_at_head h)

/-- The same behind "or else the empty list". -/
theorem ld_is_full (h : P5J.AtMg o Z D r' Zp Np cF)
    (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) :
    (K12.Door.laidOfChain Zp.made.proof.1).getD {} = LFull := by
  rw [laidOfChain_at_head h hy]
  rfl

end P2Law.Left

#print axioms P2Law.Left.hL_at_head
#print axioms P2Law.Left.laidOfChain_at_head
#print axioms P2Law.Left.ld_is_full
