-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WJointOmega.lean: Omega's tree at a job on three members:
the job's column is the sending's.

  tree_third_column    tree number 2 of a job whose third member is Omega's message 0, where the tree
                       is that member's main rows and the member's rows are the sending's at its own
                       coins: its column is the sending's column

By what. column_three, first_three, main_piece_third (WJointTree.lean), columnOf_mine
(K12/TreeIsColumnAt.lean), col_sent (K12/TableIsColumn.lean).

Limits.
  * hrows, the coins' tie, is a premise: omega_is_sent pays it at the book.
  * The premises on the stage and the blocks are public: that they hold at the written place is
    another matter.
  * Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WJointTree
import Johnson.Desc.ProofFile.Honest.K12.TableIsColumn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open Fmt.M1 (Stage)
open ProofFile.Honest.K14 (SendJob SendPub jobOmega Ask columnOf symbolsOf)

variable {W X : Type}

/-- **Tree number 2 of the job is the sending's tree.** -/
theorem tree_third_column (M : ManyJob W X) (mA mB : Mem W X) (An : SendPub) (n : ℕ) (a₀ : Addr)
    (fs : Option ℕ × Option ℕ) (ask : W → Ask)
    (hm : M.mems = [mA, mB, memOfSending (jobOmega ⟨An.P, n⟩) a₀ 0 fs ask none]) {d : ℕ}
    (ht : M.trees[2]? = some (d, [.main 2])) (w : W) (fr : Front X) (C : TestCoins) (x : ℕ)
    (L : ℕ → ProofFile.Honest.K14.Laid)
    (hrows : (memOfSending (jobOmega ⟨An.P, n⟩) a₀ 0 fs ask none).rows w fr (C.mem 2) =
      rowsOfLaid (jobOmega An).Q.codes ((jobOmega An).Q.sent.getD 0 default).shape (L 0))
    (hk : M.s₀.h ≤ M.s₀.k)
    (hc : sameCode ((jobOmega An).Q.codes.base.getD (shapeAt (jobOmega An) 0).code default)
      M.s₀.C = true)
    (hb : (memOfSending (X := X) (jobOmega ⟨An.P, n⟩) a₀ 0 fs ask none).shape.base = false)
    (hin : (memOfSending (X := X) (jobOmega ⟨An.P, n⟩) a₀ 0 fs ask none).shape.mainFirst +
      (shapeAt (jobOmega An) 0).mainRows ≤ 2 ^ M.s₀.k)
    (d0 : ∀ r < (shapeAt (jobOmega An) 0).mainRows, ¬ (mA.shape.mainFirst ≤
        (memOfSending (X := X) (jobOmega ⟨An.P, n⟩) a₀ 0 fs ask none).shape.mainFirst + r ∧
      (memOfSending (X := X) (jobOmega ⟨An.P, n⟩) a₀ 0 fs ask none).shape.mainFirst + r <
        mA.shape.mainFirst + mA.shape.mainRows))
    (d1 : ∀ r < (shapeAt (jobOmega An) 0).mainRows, ¬ (mB.shape.mainFirst ≤
        (memOfSending (X := X) (jobOmega ⟨An.P, n⟩) a₀ 0 fs ask none).shape.mainFirst + r ∧
      (memOfSending (X := X) (jobOmega ⟨An.P, n⟩) a₀ 0 fs ask none).shape.mainFirst + r <
        mB.shape.mainFirst + mB.shape.mainRows))
    (hmine : mineOf (jobOmega An) 0 = [0]) (hmask : (shapeAt (jobOmega An) 0).maskRows = 0) :
    ((M.toRun.toTest.trees₀ w fr C.mem (M.toRun.toTest.first w fr C)).getD 2
        (0, fun _ => [])).2 x =
      columnOf (jobOmega An).Q.codes (jobOmega An).Q.sent L 0 x := by
  obtain ⟨t1, t2⟩ := first_three M mA mB _ hm w fr C
  rw [hrows] at t1 t2
  rw [column_three M mA mB _ hm w fr C.mem _ 2 d [.main 2] ht x, columnOf_mine, hmine]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [hmask, symbolsOf_none, List.append_nil]
  exact main_piece_third M.s₀ hk _ hc mA.shape mB.shape _ _ _ _ (L 0) (L 0)
    (shapeAt (jobOmega An) 0).mainRows _ x rfl rfl rfl hb hin d0 d1 t1 t2
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.tree_third_column
