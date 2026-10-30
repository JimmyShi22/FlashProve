-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/StackIff.lean: the ledger of the three claims on the batched sumcheck's output, pulled
back to the early entries, holds if and only if the three output claims hold.

Cb/Pv/Lay/End/StackA.lean has one direction (stack_pull). This file has the other.

Main names:
  `stack_pull_iff`: the pull-back of stackLed holds if and only if the three output claims hold.
Limits: as Cb/Pv/Lay/End/StackA.lean.


-/
import Cb.Pv.Lay.End.HonOut
import Cb.Pv.Lay.End.StackA

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End

open Finset Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model (Scl)
open Inst.Model.FFSeg (Cell)

variable {E : Type} [Field E] [Fintype E] [scl : Scl] (P : InnPar0 E) {J₂ : Type}
  [DecidableEq P.J] [DecidableEq J₂] [Fintype J₂]

/-- The pull-back of the ledger of the three claims holds if and only if the three output claims
hold. -/
theorem stack_pull_iff
    (hrd : ∀ (a b : E) (m m' : P.J → E) (c : Cell),
      P.rd (fun j => a * m j + b * m' j) c = a * P.rd m c + b * P.rd m' c)
    (a : J₂ → TWhole.Aff E P.J) (o : P.inn.toSum.T.par.Out) (m : P.J → E) :
    TWhole.Ledger.Holds (Cb.Sub.pullL a (stackLed P o)) m ↔
      (P.inn.toSum.T.par.UHolds o m ∧ P.inn.toSum.T.par.EHolds o m (.inl (.inl ())) ∧
        P.inn.toSum.T.par.EHolds o m (.inr (.inl ()))) := by
  refine ⟨stack_pull P hrd a o m, fun h => ?_⟩
  refine (Cb.Sub.pullL_holds _ _ _).2 ((ledOf_holds _ _).2 fun f hf => ?_)
  unfold stackCl at hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · rw [val_upForm]
    exact (Cb.Sub.formU_holds _ _ (fun _ _ b _ => PEmpty.elim b) o m).2 h.1
  · exact (rowF_iff P o _ (a0_aff P hrd o.st _) m _).2 h.2.1
  · exact (rowF_iff P o _ (b0_aff P hrd o.st _) m _).2 h.2.2

end Cb.Pv.Lay.End

#print axioms Cb.Pv.Lay.End.stack_pull_iff
