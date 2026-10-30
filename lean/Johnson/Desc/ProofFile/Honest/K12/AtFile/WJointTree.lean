-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WJointTree.lean: a tree of a job on three members, when the
tree is the third member's main rows: the job's stretch is the sender's column. The laws of
K12/TreeIsColumn.lean and K12/TreeIsColumnAt.lean at two members, at three.

  layRows_third        of three blocks, the rows of the third at a row that the other two do not cover
  main_piece_third     the third member's main rows: the job's stretch is the sender's
  trees₀_three, rows_three, first_three   the trees and the first state of a job on three members
  column_three         tree number i's column, from its pieces

By what. The proofs of layRows_snd, main_piece, column_many, rows_many, first_many.

Limits.
  * Which rows lie in which tree, that the blocks do not overlap, and that the random values agree
    are premises here.
  * Main rows over the extension field alone (m2.base is false).
  * Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.TreeIsColumnAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes.Slice (GE ofE toE lst readE)
open Johnson.Prover.Link (PS symG symG_congr)
open Fmt.M1 (Stage)
open Fmt.M1.Own (PSt words)
open ProofFile.Honest.K14 (Laid symbolsOf)

variable {W X : Type}

/-- Of three blocks, the third's rows at a row that the two others do not cover. -/
theorem layRows_third (n len b : ℕ) (B0 B1 B2 : RowBlock) (hb : b < n)
    (h0 : ¬ (B0.first ≤ b ∧ b < B0.first + B0.count))
    (h1 : ¬ (B1.first ≤ b ∧ b < B1.first + B1.count))
    (h : B2.first ≤ b ∧ b < B2.first + B2.count) :
    (layRows n len [B0, B1, B2]).getD b [] = B2.rows.getD (b - B2.first) [] := by
  unfold layRows
  rw [getD_range n _ _ b hb]
  simp only [List.findSome?_cons, if_neg h0, if_neg h1, if_pos h, Option.getD_some]

/-- **The third member's main rows.** P: a state whose main table and tails are read off the stage's
lists. L: what the member's rows are tabulated from. L': the sender's. -/
theorem main_piece_third (s : Stage) (hk : s.h ≤ s.k) (c : OnBytes.Code) (hc : sameCode c s.C = true)
    (m0 m1 m2 : MemShape) (q0 q1 q2 : PSt) (L L' : Laid) (n : ℕ) (P : PS) (x : ℕ)
    (hM : q2.M = tabE n c.ell L.main) (hR : q2.Rh = tabE n c.r L.mainTail)
    (hn : m2.mainRows = n) (hb : m2.base = false) (hin : m2.mainFirst + n ≤ 2 ^ s.k)
    (d0 : ∀ r < n, ¬ (m0.mainFirst ≤ m2.mainFirst + r ∧
      m2.mainFirst + r < m0.mainFirst + m0.mainRows))
    (d1 : ∀ r < n, ¬ (m1.mainFirst ≤ m2.mainFirst + r ∧
      m2.mainFirst + r < m1.mainFirst + m1.mainRows))
    (hP : P.tabM = (readPS s (layFirst s [(m0, q0), (m1, q1), (m2, q2)])).tabM)
    (hT : P.tM = (readPS s (layFirst s [(m0, q0), (m1, q1), (m2, q2)])).tM)
    (em : ∀ r < n, ∀ j < c.ell, readE (L.main r j) = readE (L'.main r j))
    (et : ∀ r < n, ∀ t < c.r, readE (L.mainTail r t) = readE (L'.mainTail r t)) :
    wordsAt (symOf s P x) (selsOf s [m0, m1, m2] (.main 2)) =
      symbolsOf c x n L'.main L'.mainTail := by
  have e0 : selsOf s [m0, m1, m2] (.main 2) =
      (List.range n).map fun r => ⟨.main, m2.mainFirst + r, false⟩ := by
    show (List.range m2.mainRows).map (fun r => (⟨.main, m2.mainFirst + r, m2.base⟩ : Sel)) = _
    rw [hn, hb]
  rw [e0, mainWords s hk P x _ n hin, symbolsOf_field, code_of_same hc]
  have hl : c.ell = s.C.l := congrArg Fmt.M1.Code.l (code_of_same hc)
  have hr0 : c.r = s.C.r := congrArg Fmt.M1.Code.r (code_of_same hc)
  refine congrArg List.flatten (List.map_congr_left fun r hr => ?_)
  have hr' : r < n := List.mem_range.1 hr
  have hlt : m2.mainFirst + r < 2 ^ s.k := by omega
  have hcov : m2.mainFirst ≤ m2.mainFirst + r ∧ m2.mainFirst + r < m2.mainFirst + m2.mainRows := by
    rw [hn]
    omega
  refine congrArg (fun y => words (ofE y)) (symG_congr _ x _ _ _ _ (fun j hj => ?_) fun t ht => ?_)
  · rw [hP]
    show lst ((layRows (2 ^ s.k) s.C.l [⟨m0.mainFirst, m0.mainRows, q0.M⟩,
      ⟨m1.mainFirst, m1.mainRows, q1.M⟩, ⟨m2.mainFirst, m2.mainRows, q2.M⟩]).getD
        ((m2.mainFirst + r + 2 ^ s.k * j) % 2 ^ s.k) [])
      ((m2.mainFirst + r + 2 ^ s.k * j) / 2 ^ s.k) = _
    rw [(split_idx s.k _ j hlt).1, (split_idx s.k _ j hlt).2,
      layRows_third _ _ _ _ _ _ hlt (d0 r hr') (d1 r hr') hcov]
    show lst (q2.M.getD (m2.mainFirst + r - m2.mainFirst) []) j = _
    rw [Nat.add_sub_cancel_left, hM, lst_tabE n c.ell _ r j hr' (by rw [hl]; exact hj)]
    exact em r hr' j (by rw [hl]; exact hj)
  · rw [hT]
    show lst ((layRows (2 ^ s.k) s.C.r [⟨m0.mainFirst, m0.mainRows, q0.Rh⟩,
      ⟨m1.mainFirst, m1.mainRows, q1.Rh⟩, ⟨m2.mainFirst, m2.mainRows, q2.Rh⟩]).getD
        (m2.mainFirst + r) []) t = _
    rw [layRows_third _ _ _ _ _ _ hlt (d0 r hr') (d1 r hr') hcov]
    show lst (q2.Rh.getD (m2.mainFirst + r - m2.mainFirst) []) t = _
    rw [Nat.add_sub_cancel_left, hR, lst_tabE n c.r _ r t hr' (by rw [hr0]; exact ht)]
    exact et r hr' t (by rw [hr0]; exact ht)

section Many
variable (B : ManyJob W X) (mA mB mC : Mem W X) (hm : B.mems = [mA, mB, mC]) (w : W) (fr : Front X)

include hm in
/-- Tree number i's column, from its pieces. -/
theorem column_three (mem : ℕ → Stretch) (P : Johnson.Prover.Link.PS) (i d : ℕ)
    (ps : List Piece) (ht : B.trees[i]? = some (d, ps)) (x : ℕ) :
    ((B.toRun.toTest.trees₀ w fr mem P).getD i (0, fun _ => [])).2 x =
      wordsAt (symOf B.s₀ P x) (ps.flatMap (selsOf B.s₀ [mA.shape, mB.shape, mC.shape])) := by
  rw [trees₀_many, List.getD_eq_getElem?_getD, List.getElem?_map, ht, hm]
  rfl

include hm in
/-- Tree number i's depth, from its pieces. -/
theorem depth_three (mem : ℕ → Stretch) (P : Johnson.Prover.Link.PS) (i d : ℕ)
    (ps : List Piece) (ht : B.trees[i]? = some (d, ps)) :
    ((B.toRun.toTest.trees₀ w fr mem P).getD i (0, fun _ => [])).1 = d := by
  rw [trees₀_many, List.getD_eq_getElem?_getD, List.getElem?_map, ht]
  rfl

include hm in
/-- The stage's lists at the three members. -/
theorem rows_three (mem : ℕ → Stretch) :
    B.toRun.rows w fr mem =
      layFirst B.s₀ [(mA.shape, mA.rows w fr (mem 0)), (mB.shape, mB.rows w fr (mem 1)),
        (mC.shape, mC.rows w fr (mem 2))] := by
  show layFirst B.s₀ (B.mems.zipIdx.map fun m => (m.1.shape, m.1.rows w fr (mem m.2))) = _
  rw [hm]
  rfl

include hm in
/-- The first state's main tables are read off these lists. -/
theorem first_three (C : TestCoins) :
    (B.toRun.toTest.first w fr C).tabM = (readPS B.s₀ (layFirst B.s₀
        [(mA.shape, mA.rows w fr (C.mem 0)), (mB.shape, mB.rows w fr (C.mem 1)),
          (mC.shape, mC.rows w fr (C.mem 2))])).tabM ∧
      (B.toRun.toTest.first w fr C).tM = (readPS B.s₀ (layFirst B.s₀
        [(mA.shape, mA.rows w fr (C.mem 0)), (mB.shape, mB.rows w fr (C.mem 1)),
          (mC.shape, mC.rows w fr (C.mem 2))])).tM := by
  rw [← rows_three B mA mB mC hm w fr C.mem]
  exact ⟨rfl, rfl⟩

end Many

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.layRows_third
#print axioms ProofFile.Honest.K12.Light.main_piece_third
#print axioms ProofFile.Honest.K12.Light.column_three
#print axioms ProofFile.Honest.K12.Light.depth_three
#print axioms ProofFile.Honest.K12.Light.rows_three
#print axioms ProofFile.Honest.K12.Light.first_three
