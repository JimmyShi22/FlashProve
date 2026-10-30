-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyExchangeEmpty.lean: THE THIRD OF THE FOUR DEBTS AT A MEMBER (`Exchange`,
Johnson/Desc/ProofFile/Honest/Thread/Pays.lean) AT THE SIXTEEN SUB-PROTOCOLS OF THE KEY FILE WHOSE
FORWARD ROW OWES NOTHING. At every filling of the threads' other letters. NOTHING IS SHOWN OF ANY
PROVER.

  **`exchange_of_nil`**: GENERAL in the thread: where the row of the sub-protocol number b owes no
      item, `Exchange` holds there: it asks that the items which the row owes hold behind the step
  `owes_none`: at the key file's three tables of forward rows (E2E/KeyThreadBase.lean) the rows that
      owe nothing are just these: ten, three and three: by evaluation
  **`exchange₁`**, **`exchange₂`**, **`exchange₃`**: so `Exchange` at these sixteen, at the base
      threads, whatever the other letters are

Limits.
- IT IS PAID BECAUSE NOTHING IS OWED: a fact on the table's rows, not on any sub-protocol. That a
  row rightly owes nothing is not shown.
- The nineteen other rows owe items: nothing here.
- A thread that is made of a base thread by laying halves or further clauses on the verifier's state
  has the same rows: `exchange_of_nil` serves there too.

-/
import E2E.KeyThreadBase
import Johnson.Desc.ProofFile.Honest.Thread.Pays

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyThread
open VerifiableInference.Desc (FileDescription)
open VerifiableInference.Desc.Key (rows₂ rows₃)
open ProofFile.Honest

/-- **Where a row owes nothing the exchange is empty.** -/
theorem exchange_of_nil {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb) {b : Nat}
    (h : (T.row b).owes = []) : Exchange T b := by
  intro blk _ k s m E ds y cols s' _ _ _
  rw [h]
  intro ds' i hi
  cases hi

/-- The rows that owe nothing are just these. -/
theorem owes_none :
    (List.range 19).filter (fun b => (rowsFirst b).owes.isEmpty) =
        [2, 3, 6, 7, 8, 9, 12, 13, 15, 18] ∧
      (List.range 12).filter (fun b => (rowsAt (rows₂.map sharedRow) b).owes.isEmpty) =
        [0, 6, 11] ∧
      (List.range 4).filter (fun b => (rowsAt rows₃ b).owes.isEmpty) = [1, 2, 3] := by decide

section
variable {Xi W₀ Rc Ky Tr X₀ X : Type} {Bk : ProverCoinCounts} (F : FileDescription Xi)

theorem exchange₁ (R : Rest Bk F.S₁ (Local W₀ Rc Xi Tr)) :
    ∀ b ∈ [2, 3, 6, 7, 8, 9, 12, 13, 15, 18], Exchange (keyBase₁ (X := X) F R) b := fun b hb =>
  exchange_of_nil _ ((by decide : ∀ b ∈ [2, 3, 6, 7, 8, 9, 12, 13, 15, 18],
    (rowsFirst b).owes = []) b hb)

theorem exchange₂ (R : Rest Bk F.S₂ (Common W₀ Rc Ky)) :
    ∀ b ∈ [0, 6, 11], Exchange (keyBase₂ (X₀ := X₀) F R) b := fun b hb =>
  exchange_of_nil _ ((by decide : ∀ b ∈ [0, 6, 11],
    (rowsAt (rows₂.map sharedRow) b).owes = []) b hb)

theorem exchange₃ (R : Rest Bk F.S₃ (Local W₀ Rc Xi Tr)) :
    ∀ b ∈ [1, 2, 3], Exchange (keyBase₃ (X := X) F R) b := fun b hb =>
  exchange_of_nil _ ((by decide : ∀ b ∈ [1, 2, 3], (rowsAt rows₃ b).owes = []) b hb)

end

end AtPublicFiles.KeyThread

#print axioms AtPublicFiles.KeyThread.exchange_of_nil
#print axioms AtPublicFiles.KeyThread.owes_none
#print axioms AtPublicFiles.KeyThread.exchange₁
#print axioms AtPublicFiles.KeyThread.exchange₂
#print axioms AtPublicFiles.KeyThread.exchange₃
