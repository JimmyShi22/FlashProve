-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/WrittenView.lean: the view that a decision gets in the written link, for any decision.

The written protocol (Run/PlanQX.lean: `skeletonOverBothExternalStrings`) hands its decision a view: the rounds, and a list of
opened columns, each with its key and position. This file says what that view holds when the
transcript is put together from the link's five rounds and the blocks that follow them
(OnBytes/Slice/ChainCloses.lean: `tailTr`). It is meant for a decision that reads the list of
columns entry by entry and tests each entry's key and position: whatever entry it takes, the column
is the one that the prover sent.

Main theorems.
 `accept_view`    a yes of the written protocol is a yes of the decision on the view.
 `rvSL_joinT`, `view_rounds`   the view's rounds are the written rounds, block by block.
 `colAtS_tree0`, `colAtS_tree1`, `colAtS_tree2`   the three trees' columns.
 `opened_own`     an entry under the key 0, 1 or 2 holds the column of the first, second or third
                  tree at the entry's position.
 `opened_stored`  an entry under a stored table's key holds that table's column at the entry's
                  position.
Not claimed. Which entries the list has, and in which order.
-/
import OnBytes.Slice.SemLib

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Run

/-- A yes of the written protocol is a yes of its decision on the view. -/
theorem accept_view (ds : List PQ.RD) (a : ℕ) (xs : List PQ.XO) (dec : PQ.View → Bool)
    (y : (twoExternalStrings (2 ^ a) PQ.SgX).Str) (τ : Tr (PQ.uL (ckP .two) ds))
    (m0 : (PQ.s0 (ckP .two)).up.Msg) (c0 : (PQ.s0 (ckP .two)).up.Chal)
    (h : (PQ.skeletonOverBothExternalStrings (ckP .two) ds a xs dec).up.loc.accept () y (m0, c0, τ) = true) :
    dec (PQ.viewX (ckP .two) ds a xs y τ) = true := by
  have h4 : (PQ.passSL (ckP .two) ds _ && _ && _ && dec (PQ.viewX (ckP .two) ds a xs y τ)) = true :=
    h
  simp only [Bool.and_eq_true] at h4
  exact h4.2

/-- The rounds of a joined transcript, as a view holds them. -/
theorem rvSL_joinT : ∀ (ds₁ ds₂ : List PQ.RD) (τ : Tr (PQ.uL (ckP .two) ds₁))
    (b : Tr (PQ.uL (ckP .two) ds₂)),
    PQ.rvSL (ckP .two) (ds₁ ++ ds₂) (joinT ds₁ ds₂ τ b) =
      PQ.rvSL (ckP .two) ds₁ τ ++ PQ.rvSL (ckP .two) ds₂ b
  | [], _, _, _ => rfl
  | d :: ds₁, ds₂, (m, c, τ), b =>
    congrArg (PQ.rvSL (ckP .two) [d] (m, c, ()) ++ ·) (rvSL_joinT ds₁ ds₂ τ b)

section
variable (s1 s2 : Sg) (d1 d2 d3 d4 d5 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB : PQ.RD)
  (ht : TreesOK d1 d2 d3 d4 d5 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3)
  (m1 : (wRound d1).Msg) (c1 : (wRound d1).Chal) (m2 : (wRound d2).Msg)
  (c2 : (wRound d2).Chal) (m3 : (wRound d3).Msg) (c3 : (wRound d3).Chal)
  (m4 : (wRound d4).Msg) (c4 : (wRound d4).Chal) (m5 : (wRound d5).Msg) (c5 : (wRound d5).Chal)
  (mA : (wRound dA).Msg) (cA : (wRound dA).Chal)
  (τF1 : Tr (PQ.uL (ckP .two) (foldRds s1 dE1 dT1))) (τC1 : Tr (PQ.uL (ckP .two) [dS2, dC1]))
  (τF2 : Tr (PQ.uL (ckP .two) (foldRds s2 dE2 dT2))) (τC2 : Tr (PQ.uL (ckP .two) [dS3, dC2]))
  (τB : Tr (PQ.uL (ckP .two) [dL, dB]))

/-- All rounds of the written link. -/
abbrev allRds : List PQ.RD :=
  d1 :: d2 :: d3 :: d4 :: d5 :: tailRds s1 s2 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB

/-- A transcript of all rounds, from the five rounds and the blocks' transcripts. -/
def allTr : Tr (PQ.uL (ckP .two)
    (allRds s1 s2 d1 d2 d3 d4 d5 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB)) :=
  (m1, c1, m2, c2, m3, c3, m4, c4, m5, c5,
    tailTr s1 s2 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB mA cA τF1 τC1 τF2 τC2 τB)

/-- The view's rounds are the written rounds, block by block. -/
theorem view_rounds (a : ℕ) (xs : List PQ.XO) (y : (twoExternalStrings (2 ^ a) PQ.SgX).Str) :
    (PQ.viewX (ckP .two) _ a xs y
      (allTr s1 s2 d1 d2 d3 d4 d5 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB m1 c1 m2 c2 m3 c3 m4 c4
        m5 c5 mA cA τF1 τC1 τF2 τC2 τB)).rounds =
      PQ.rvSL (ckP .two) [d1, d2, d3, d4, d5, dA]
        (m1, c1, m2, c2, m3, c3, m4, c4, m5, c5, mA, cA, ()) ++
      (PQ.rvSL (ckP .two) _ τF1 ++ (PQ.rvSL (ckP .two) _ τC1 ++ (PQ.rvSL (ckP .two) _ τF2 ++
        (PQ.rvSL (ckP .two) _ τC2 ++ PQ.rvSL (ckP .two) _ τB)))) := by
  show PQ.rvSL (ckP .two) [d1, d2, d3, d4, d5, dA]
      (m1, c1, m2, c2, m3, c3, m4, c4, m5, c5, mA, cA, ()) ++
    PQ.rvSL (ckP .two) _ (joinT _ _ τF1 (joinT _ _ τC1 (joinT _ _ τF2 (joinT _ _ τC2 τB)))) = _
  rw [rvSL_joinT, rvSL_joinT, rvSL_joinT, rvSL_joinT]

include ht

/-- The first tree is the second round's. -/
theorem colAtS_tree0 (x : ℕ) :
    PQ.colAtS (ckP .two) _
      (allTr s1 s2 d1 d2 d3 d4 d5 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB m1 c1 m2 c2 m3 c3 m4 c4
        m5 c5 mA cA τF1 τC1 τF2 τC2 τB) 0 x = treeCol d2 m2 x := by
  unfold allTr
  rw [colAtS_skip _ _ _ _ _ ht.t1, colAtS_here _ _ _ _ _ ht.t2]
  rfl

/-- The second tree is sent in the first round of the first code switch. -/
theorem colAtS_tree1 (x : ℕ) :
    PQ.colAtS (ckP .two) _
      (allTr s1 s2 d1 d2 d3 d4 d5 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB m1 c1 m2 c2 m3 c3 m4 c4
        m5 c5 mA cA τF1 τC1 τF2 τC2 τB) 1 x = treeCol dS2 τC1.1 x := by
  have nF1 := nTrees_fold s1 dE1 dT1 ht.tE1 ht.tT1
  obtain ⟨mS2, cS2, mC1, cC1, _⟩ := τC1
  unfold allTr tailTr
  rw [colAtS_skip _ _ _ _ _ ht.t1, colAtS_next _ _ _ _ _ ht.t2,
    colAtS_skip _ _ _ _ _ ht.t3, colAtS_skip _ _ _ _ _ ht.t4, colAtS_skip _ _ _ _ _ ht.t5,
    colAtS_skip _ _ _ _ _ ht.tA, colAtS_join_none _ _ nF1]
  show PQ.colAtS (ckP .two) (dS2 :: dC1 :: _) (mS2, cS2, mC1, cC1, _) 0 x = _
  rw [colAtS_here _ _ _ _ _ ht.tS2]
  rfl

/-- The third tree is sent in the first round of the second code switch. -/
theorem colAtS_tree2 (x : ℕ) :
    PQ.colAtS (ckP .two) _
      (allTr s1 s2 d1 d2 d3 d4 d5 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB m1 c1 m2 c2 m3 c3 m4 c4
        m5 c5 mA cA τF1 τC1 τF2 τC2 τB) 2 x = treeCol dS3 τC2.1 x := by
  have nF1 := nTrees_fold s1 dE1 dT1 ht.tE1 ht.tT1
  have nF2 := nTrees_fold s2 dE2 dT2 ht.tE2 ht.tT2
  obtain ⟨mS2, cS2, mC1, cC1, _⟩ := τC1
  obtain ⟨mS3, cS3, mC2, cC2, _⟩ := τC2
  unfold allTr tailTr
  rw [colAtS_skip _ _ _ _ _ ht.t1, colAtS_next _ _ _ _ _ ht.t2,
    colAtS_skip _ _ _ _ _ ht.t3, colAtS_skip _ _ _ _ _ ht.t4, colAtS_skip _ _ _ _ _ ht.t5,
    colAtS_skip _ _ _ _ _ ht.tA, colAtS_join_none _ _ nF1]
  show PQ.colAtS (ckP .two) (dS2 :: dC1 :: _) (mS2, cS2, mC1, cC1, _) (0 + 1) x = _
  rw [colAtS_next _ _ _ _ _ ht.tS2, colAtS_skip _ _ _ _ _ ht.tC1]
  show PQ.colAtS (ckP .two) (foldRds s2 dE2 dT2 ++ _) (joinT (foldRds s2 dE2 dT2) _ τF2 _) 0 x = _
  rw [colAtS_join_none _ _ nF2]
  show PQ.colAtS (ckP .two) (dS3 :: dC2 :: _) (mS3, cS3, mC2, cC2, _) 0 x = _
  rw [colAtS_here _ _ _ _ _ ht.tS3]
  rfl

/-- An entry of the view's list under the key of one of the three trees holds that tree's column
at the entry's position, and the position is one of the tree's. -/
theorem opened_own (a : ℕ) (xs : List PQ.XO) (y : (twoExternalStrings (2 ^ a) PQ.SgX).Str)
    (o : ℕ × ℕ × List UInt64)
    (ho : o ∈ (PQ.viewX (ckP .two) _ a xs y
      (allTr s1 s2 d1 d2 d3 d4 d5 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB m1 c1 m2 c2 m3 c3 m4 c4
        m5 c5 mA cA τF1 τC1 τF2 τC2 τB)).opened) :
    (o.1 = 0 → treeCol d2 m2 o.2.1 = some o.2.2) ∧
    (o.1 = 1 → treeCol dS2 τC1.1 o.2.1 = some o.2.2) ∧
    (o.1 = 2 → treeCol dS3 τC2.1 o.2.1 = some o.2.2) := by
  have key : o.1 < 2 ^ 16 → PQ.colAtS (ckP .two) _
      (allTr s1 s2 d1 d2 d3 d4 d5 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB m1 c1 m2 c2 m3 c3 m4 c4
        m5 c5 mA cA τF1 τC1 τF2 τC2 τB) o.1 o.2.1 = some o.2.2 := by
    intro hlt
    rcases mem_opened _ a xs y _ o ho with h | h | h
    · omega
    · omega
    · exact h.2.2
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have hk := key (by rw [h]; norm_num)
    rw [h, colAtS_tree0 s1 s2 d1 d2 d3 d4 d5 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB ht] at hk
    exact hk
  · have hk := key (by rw [h]; norm_num)
    rw [h, colAtS_tree1 s1 s2 d1 d2 d3 d4 d5 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB ht] at hk
    exact hk
  · have hk := key (by rw [h]; norm_num)
    rw [h, colAtS_tree2 s1 s2 d1 d2 d3 d4 d5 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB ht] at hk
    exact hk

end

/-- An entry of the view's list under a stored table's key holds that table's column at the
entry's position. -/
theorem opened_stored (ds : List PQ.RD) (a : ℕ) (xs : List PQ.XO)
    (y : (twoExternalStrings (2 ^ a) PQ.SgX).Str) (τ : Tr (PQ.uL (ckP .two) ds)) (o : ℕ × ℕ × List UInt64)
    (ho : o ∈ (PQ.viewX (ckP .two) ds a xs y τ).opened) :
    (o.1 = Fmt.storedKey 0 → storedOf a y 0 o.2.1 = some o.2.2) ∧
    (o.1 = Fmt.storedKey 1 → storedOf a y 1 o.2.1 = some o.2.2) := by
  have k0 : Fmt.storedKey 0 = 2 ^ 16 := rfl
  have k1 : Fmt.storedKey 1 = 2 ^ 16 + 1 := rfl
  rw [k0, k1]
  rcases mem_opened ds a xs y τ o ho with h | h | h
  · exact ⟨fun _ => h.2, fun h1 => by omega⟩
  · exact ⟨fun h0 => by omega, fun _ => h.2⟩
  · exact ⟨fun h0 => absurd h0 h.1, fun h1 => absurd h1 h.2.1⟩

end OnBytes.Slice

#print axioms OnBytes.Slice.accept_view
#print axioms OnBytes.Slice.view_rounds
#print axioms OnBytes.Slice.opened_own
#print axioms OnBytes.Slice.opened_stored
