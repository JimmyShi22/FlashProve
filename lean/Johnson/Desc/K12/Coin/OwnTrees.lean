-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Coin/OwnTrees.lean: A PROXIMITY TEST WHOSE FIRST FOLD SENDS ITS OWN MASK: THE TREES
THAT ITS CHAIN SENDS, BY NUMBER. Definitions, statements and proofs.

There the first round of the chain's first fold sends a tree too: the chain's tree number 0 is that
one, number 1 the first switch's, and so on.

  `TreesOwn`: which rounds of such a chain send a tree (beside `Chain.Trees`,
    OnBytes/Slice/ManyShows.lean, which asks that no fold's round sends one).
  `colAtS_own_zero`, `colAtS_own_succ`, `colAtS_sw_zero`, `colAtS_sw_succ`: the columns by number,
    at the first block.
  `col1`, `col1_zero`: the columns of the tree that the chain's first message sends; they are the
    chain's tree number 0's.
  `ownCols_own`: `OwnCols` (Src.lean) of such a chain: the tree of own number n + k is the chain's
    tree number k + 1.
  `woOf`, `colW_woOf`: columns as a written oracle of a given depth and width, and back.
A tool.
-/
import Johnson.Desc.K12.Coin.Own
import Johnson.Desc.K12.Coin.Yes
import Johnson.Desc.K12.Law.OwnMask

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob _root_.Run
open H2K.JointK (WO)
open H2K.Pub (Msg1 msg1)

/-- The first fold's first round sends a tree; else as `Chain.Trees`. -/
def TreesOwn : {s : Sg} → OnBytes.Slice.Chain s → Prop
  | _, .last _ _ _ _ _ _ _ => False
  | _, .step _ _ _ _ _ dE dT dS dC _ _ _ _ _ next =>
    dE.tree.isSome = true ∧ dT.tree.isSome = false ∧ dS.tree.isSome = true ∧
      dC.tree.isSome = false ∧ next.Trees

theorem colAtS_own_zero (s : Sg) (dE dT : PQ.RD) (ds₂ : List PQ.RD)
    (hE : dE.tree.isSome = true) (τF : Tr (PQ.uL (ckP .two) (foldRds s dE dT)))
    (B : Tr (PQ.uL (ckP .two) ds₂)) (x : ℕ) :
    PQ.colAtS (ckP .two) (foldRds s dE dT ++ ds₂) (joinT (foldRds s dE dT) ds₂ τF B) 0 x =
      treeCol dE τF.1 x := by
  obtain ⟨mE, cE, τr⟩ := τF
  show PQ.colAtS (ckP .two) (dE :: (List.replicate (s.h + s.g) dT ++ ds₂))
    (mE, cE, joinT (List.replicate (s.h + s.g) dT) ds₂ τr B) 0 x = _
  rw [colAtS_here _ _ _ _ _ hE]
  rfl

theorem colAtS_own_succ (s : Sg) (dE dT : PQ.RD) (ds₂ : List PQ.RD)
    (hE : dE.tree.isSome = true) (hT : dT.tree.isSome = false)
    (τF : Tr (PQ.uL (ckP .two) (foldRds s dE dT))) (B : Tr (PQ.uL (ckP .two) ds₂)) (n x : ℕ) :
    PQ.colAtS (ckP .two) (foldRds s dE dT ++ ds₂) (joinT (foldRds s dE dT) ds₂ τF B) (n + 1) x =
      PQ.colAtS (ckP .two) ds₂ B n x := by
  obtain ⟨mE, cE, τr⟩ := τF
  show PQ.colAtS (ckP .two) (dE :: (List.replicate (s.h + s.g) dT ++ ds₂))
    (mE, cE, joinT (List.replicate (s.h + s.g) dT) ds₂ τr B) (n + 1) x = _
  rw [colAtS_next _ _ _ _ _ hE, colAtS_join_none _ _ (nTrees_replicate dT hT _)]

theorem colAtS_sw_zero (dS dC : PQ.RD) (rest : List PQ.RD) (hS : dS.tree.isSome = true)
    (τC : Tr (PQ.uL (ckP .two) [dS, dC])) (b : Tr (PQ.uL (ckP .two) rest)) (x : ℕ) :
    PQ.colAtS (ckP .two) ([dS, dC] ++ rest) (joinT [dS, dC] rest τC b) 0 x = treeCol dS τC.1 x := by
  obtain ⟨mS, cS, mC, cC, _⟩ := τC
  show PQ.colAtS (ckP .two) (dS :: dC :: rest) (mS, cS, mC, cC, b) 0 x = _
  rw [colAtS_here _ _ _ _ _ hS]
  rfl

theorem colAtS_sw_succ (dS dC : PQ.RD) (rest : List PQ.RD) (hS : dS.tree.isSome = true)
    (hC : dC.tree.isSome = false) (τC : Tr (PQ.uL (ckP .two) [dS, dC]))
    (b : Tr (PQ.uL (ckP .two) rest)) (k x : ℕ) :
    PQ.colAtS (ckP .two) ([dS, dC] ++ rest) (joinT [dS, dC] rest τC b) (k + 1) x =
      PQ.colAtS (ckP .two) rest b k x := by
  obtain ⟨mS, cS, mC, cC, _⟩ := τC
  show PQ.colAtS (ckP .two) (dS :: dC :: rest) (mS, cS, mC, cC, b) (k + 1) x = _
  rw [colAtS_next _ _ _ _ _ hS, colAtS_skip _ _ _ _ _ hC]

/-- The columns of the tree that the chain's first message sends. -/
def col1 : {s : Sg} → (c : OnBytes.Slice.Chain s) → Msg1 c → ℕ → List UInt64
  | _, .last _ _ dL _ _ _ _ => fun m x => colW dL m.1 x
  | _, .step _ _ _ _ _ dE _ _ _ _ _ _ _ _ _ => fun m x => colW dE m.1 x

theorem col1_zero {s : Sg} (c : OnBytes.Slice.Chain s) (hT : TreesOwn c) (b : c.Bl) (x : ℕ)
    (col : List UInt64) (h : PQ.colAtS (ckP .two) c.rds (c.trL b) 0 x = some col) :
    col = col1 c (msg1 c b) x := by
  cases c with
  | last s e dL dB fu fs εb => exact hT.elim
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next =>
    have h1 : PQ.colAtS (ckP .two) (foldRds s dE dT ++ ([dS, dC] ++ next.rds))
        (joinT (foldRds s dE dT) _ b.1 (joinT [dS, dC] next.rds b.2.1 (next.trL b.2.2))) 0 x =
        some col := h
    rw [colAtS_own_zero s dE dT _ hT.1] at h1
    exact treeCol_some dE b.1.1 x col h1

theorem ownCols_own (P : ToldO → ℕ → List UInt64 → Prop) {s : Sg} (c : OnBytes.Slice.Chain s)
    (hc : TreesOwn c) (b : c.Bl) (n : ℕ)
    (hP : ∀ k (o : ToldO), o.2 = .own (n + k) → ∀ x col, P o x col →
      PQ.colAtS (ckP .two) c.rds (c.trL b) (k + 1) x = some col) : OwnCols P n c b := by
  cases c with
  | last s e dL dB fu fs εb => exact hc.elim
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next =>
    obtain ⟨hE, hT, hS, hC, hN⟩ := hc
    refine ⟨fun o ho x col hp => ?_, ownCols_of P next hN b.2.2 (n + 1) fun k o ho x col hp => ?_⟩
    · have h0 := hP 0 o ho x col hp
      have h1 : PQ.colAtS (ckP .two) (foldRds s dE dT ++ ([dS, dC] ++ next.rds))
          (joinT (foldRds s dE dT) _ b.1 (joinT [dS, dC] next.rds b.2.1 (next.trL b.2.2))) (0 + 1)
          x = some col := h0
      rw [colAtS_own_succ s dE dT _ hE hT, colAtS_sw_zero dS dC _ hS] at h1
      exact treeCol_some dS b.2.1.1 x col h1
    · have h0 := hP (k + 1) o (by rw [ho]; congr 1; omega) x col hp
      have h1 : PQ.colAtS (ckP .two) (foldRds s dE dT ++ ([dS, dC] ++ next.rds))
          (joinT (foldRds s dE dT) _ b.1 (joinT [dS, dC] next.rds b.2.1 (next.trL b.2.2)))
          (k + 1 + 1) x = some col := h0
      rwa [colAtS_own_succ s dE dT _ hE hT, colAtS_sw_succ dS dC _ hS hC] at h1

/-- Columns as a written oracle of depth a and width w: a word that a column lacks is read as 0. -/
def woOf (f : ℕ → List UInt64) (a w : ℕ) : WO := ⟨rdOf a w, fun x k => (f x.val).getD k.val 0⟩

theorem colW_woOf (f : ℕ → List UInt64) (a w x : ℕ) (col : List UInt64) (hx : x < 2 ^ a)
    (hc : f x = col) (hl : col.length = w) : colW (woOf f a w).1 (woOf f a w).2 x = col := by
  unfold colW
  rw [dif_pos (show x < PQ.posN (woOf f a w).1.tree from hx)]
  show List.ofFn (fun k : Fin w => (f x).getD k.val 0) = col
  rw [hc]
  exact ofFn_getD col w hl

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.col1_zero
#print axioms VerifiableInference.Desc.K12.Coin.ownCols_own
#print axioms VerifiableInference.Desc.K12.Coin.colW_woOf
