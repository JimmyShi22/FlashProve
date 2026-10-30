-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/BatOneLaw.lean: what a yes of `batOneOk` and of `batFreeOk`
(Johnson/Desc/K12/Law/BatOneOk.lean) gives. Statements and proofs.

Main names:
  `batOne_of_ok`: at the place's first written round `w0`: `OneElem w0.rd` (the round draws one
    element of the extension field and nothing else) and `w0.rd.entry.logN ≤ 64`.
  `batFree_of_ok`: these two, and `w0.rd.entry.work = 0`.
Limits: That either test says yes at a given plan is not shown here: that is an evaluation. No
soundness is claimed, and nothing is said on hiding.
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the
file's end.

-/
import Johnson.Desc.K12.Law.BatOneOk
import Johnson.Desc.K12.Law.FibreOf
import Johnson.Desc.K12.Law.ChainOf

set_option autoImplicit false
namespace H2K.First
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (WR writtenOf)
open H2K.Fibre (OneElem)

theorem batOne_of_ok (p : P12) (w0 : WR) (l : List WR) (hw : writtenOf p.nums = some (w0 :: l))
    (h : batOneOk p = true) : OneElem w0.rd ∧ w0.rd.entry.logN ≤ 64 := by
  unfold batOneOk at h
  rw [hw, Option.any_some, List.head?_cons, Option.any_some] at h
  unfold batOneOn at h
  rw [Bool.and_eq_true] at h
  exact ⟨beq_iff_eq.1 h.1, of_decide_eq_true h.2⟩

theorem batFree_of_ok (p : P12) (w0 : WR) (l : List WR) (hw : writtenOf p.nums = some (w0 :: l))
    (h : batFreeOk p = true) :
    OneElem w0.rd ∧ w0.rd.entry.logN ≤ 64 ∧ w0.rd.entry.work = 0 := by
  unfold batFreeOk at h
  rw [hw, Option.any_some, List.head?_cons, Option.any_some] at h
  unfold batFreeOn batOneOn at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨beq_iff_eq.1 h.1.1, of_decide_eq_true h.1.2, beq_iff_eq.1 h.2⟩

end H2K.First

#print axioms H2K.First.batOne_of_ok
#print axioms H2K.First.batFree_of_ok
