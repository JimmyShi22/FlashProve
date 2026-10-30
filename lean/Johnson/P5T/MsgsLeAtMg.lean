-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5T/MsgsLeAtMg.lean: AT THE HEAD `AtMg`: THE TABLE's COUNT OF MESSAGES AT EVERY BORDER IS
AT MOST THE LENGTH OF THE FOLD's LIST OF MESSAGES' SHAPES. It is what the choice N := `(At.foldD
Zp cF Ld).M.length` owes in what is left of the condition of the kind K9 ("msgsAt ≤ N", by sort:
Johnson/P5J/K09Left.lean). Three theorems. A joining: the evaluation is
Johnson/P5T/MsgsLeFull.lean's.
  `LaidAt.M_is`: in scope, where the value is laid: `msgsOfChain Zp.made.proof.1 = MList`.
  Three lines (inside `shape_fact_laid`, Johnson/LPFE1R/ShapeAtNoFull.lean), here under
  a name: `sends_in_scope` (row 9's pin) and `MW_eq`.
  `AtMg.M_len`: so the fold's list has 199 members, at every Ld.
  `AtMg.msgs_le`: **`(At.N Zp cF).msgsAt At.ps[k]? ≤ (At.foldD Zp cF Ld).M.length`** at every Ld
  and EVERY k.
Limits. Over the verifier's list of fourteen entry tests (Johnson/Desc/Laid/ProofAsks.lean)
alone. The full size alone. No probability: no soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5T.MsgsLeFull
import Johnson.P5T.NotIxAtMg
import Johnson.Goal.Numbers.MadeInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open OnBytes
open VerifiableInference
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.K2Hands (MW MList MW_eq)
open VerifiableInference.Desc.K12.Door (msgsOfChain)
open VerifiableInference.PlanWritten.Joined (sends_in_scope)
open OnBytes.Maker (WholeD)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- In scope, where the value is laid, the first chain's messages' shapes are the written list. -/
theorem LaidAt.M_is (L : LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF)
    (hW : VerifierAndGoals.InScope Z = true) : msgsOfChain Zp.made.proof.1 = MList := by
  rw [sends_in_scope hW L.pub (pins_of_laid hW L).1]
  exact MW_eq

/-- The fold's list has 199 members. -/
theorem AtMg.M_len (h : AtMg o Z D r Zp Np cF) (Ld : Desc.K12.Door.Laid) :
    (At.foldD Zp cF Ld).M.length = 199 := by
  show (msgsOfChain Zp.made.proof.1).length = 199
  rw [h.laid.M_is h.scope]
  exact (Prod.mk.inj P5T.msgs_counts).1

/-- **The count of messages at every border is at most the fold's list's length.** -/
theorem AtMg.msgs_le (h : AtMg o Z D r Zp Np cF) (Ld : Desc.K12.Door.Laid) (k : ℕ) :
    (At.N Zp cF).msgsAt At.ps[k]? ≤ (At.foldD Zp cF Ld).M.length := by
  show (At.N Zp cF).msgsAt At.ps[k]? ≤ (msgsOfChain Zp.made.proof.1).length
  rw [h.laid.msgs h.scope, h.laid.M_is h.scope]
  exact P5T.msgs_le_every k

end P5J

#print axioms P5J.LaidAt.M_is
#print axioms P5J.AtMg.M_len
#print axioms P5J.AtMg.msgs_le
