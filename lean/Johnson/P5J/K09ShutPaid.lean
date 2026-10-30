-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K09ShutPaid.lean: PAYMENTS BENEATH THE SHUTTING's LIST OF DEBTS (`ShutList`,
Johnson/Desc/First/Link/Law/ShutList.lean) AT THE CARRIAGE's PIECE OVER THE SEATED ROW (`atRec qs
b`,
qs the piece of `h.row 𝔏` at the place): the field lowS, and the equation on the piece's first tree
that `hS_paid` (ShutListPaid.lean) asks. Calls of Johnson/P5J/K09Cap.lean.

  `base_atRec`: (atRec qs b).base = (At.N Zp cF).treesAt At.ps[k]?.
  `lowS_at`: **lowAtB (At.N Zp cF) (atRec qs b).base k = true** FROM THE SAME TEST AT THE TABLE's
COUNT.
WHAT IS LEFT of lowS: the closed test at the table's count: EVALUATED true at all 25 shuttings of
one
stored full-size set of public files (with two bent inputs at which it says no): a run, no theorem.
Limits. No soundness statement.

-/
import Johnson.P5J.K09Cap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.LinkJoin (atRec lowAtB)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- The carriage's piece's first tree is the table's own count at the place. -/
theorem base_atRec (h : AtMg o Z D r Zp Np cF) (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok)
    (q₁ : (F0T o Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T o Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T o Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) (k : ℕ) (hk : k + 1 < cF.blocksInOrder.length)
    (hp : k ≤ At.ps.length) (qs) (hq : (h.row 𝔏)[k]? = some qs) (b : Block S ProofFile.Cl) :
    (atRec qs b).base = (At.N Zp cF).treesAt At.ps[k]? :=
  row_base_at h 𝔏 q₁ q₂ q₃ k hk hp qs hq

/-- **THE FIELD lowS.** -/
theorem lowS_at (h : AtMg o Z D r Zp Np cF) (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok)
    (q₁ : (F0T o Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T o Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T o Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) (k : ℕ) (hk : k + 1 < cF.blocksInOrder.length)
    (hp : k ≤ At.ps.length) (qs) (hq : (h.row 𝔏)[k]? = some qs) (b : Block S ProofFile.Cl)
    (T : lowAtB (At.N Zp cF) ((At.N Zp cF).treesAt At.ps[k]?) k = true) :
    lowAtB (At.N Zp cF) (atRec qs b).base k = true :=
  low_at_row h 𝔏 q₁ q₂ q₃ k hk hp qs hq T

end P5J

#print axioms P5J.base_atRec
#print axioms P5J.lowS_at
