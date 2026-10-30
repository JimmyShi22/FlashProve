-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/ManyView.lean: the view that a decision gets in the written link, for a chain of any
number of stages.

OnBytes/Slice/WrittenView.lean says what the written protocol's view holds when the rounds after the
link's fifth are three stages' blocks. This file says the same for a chain of stages
(OnBytes/Slice/ManyDefs.lean: `Chain`), by induction on the chain.

Main definitions.
 `HeadTrees`   of the link's five rounds and the batching round the second alone sends a tree.
 `manyRds`, `manyTr`   all rounds of the written link, and a transcript of them.
Main theorems.
 `rvSL_trL`   the rounds of `Chain.trL`, block by block.
 `colAtS_block_zero`, `colAtS_block_succ`   the trees' columns, one code switch at a time.
 `showsFrom_of`  `Chain.ShowsFrom` (OnBytes/Slice/ManyShows.lean) from the columns of a transcript
                 by tree number.
 `view_rounds_many`   the view's rounds are the written rounds, block by block.
 `shows_many`    an entry under the key 0 holds the column of the second round's tree, and
                 `Chain.ShowsFrom` holds from the key 1 on.
Not claimed. Which entries the list has, and in which order. Nothing on the stored tables' entries
(OnBytes/Slice/WrittenView.lean: `opened_stored` holds for every list of rounds).

-/
import OnBytes.Slice.ManyShows
import OnBytes.Slice.WrittenView

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb _root_.Run

/-! ## The rounds -/

/-- The rounds of a chain's transcript, as a view holds them, are the blocks' rounds in a row. -/
theorem rvSL_trL {s : Sg} (c : Chain s) (b : c.Bl) :
    PQ.rvSL (ckP .two) c.rds (c.trL b) = c.rvs b := by
  induction c with
  | last s e dL dB fu fs εb => rfl
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next ih =>
    show PQ.rvSL (ckP .two) (foldRds s dE dT ++ ([dS, dC] ++ next.rds))
      (joinT (foldRds s dE dT) _ b.1 (joinT [dS, dC] _ b.2.1 (next.trL b.2.2))) =
      PQ.rvSL (ckP .two) (foldRds s dE dT) b.1 ++
        (PQ.rvSL (ckP .two) [dS, dC] b.2.1 ++ next.rvs b.2.2)
    rw [rvSL_joinT, rvSL_joinT, ih]

/-! ## The trees' columns -/

/-- Of a transcript that begins with a fold and a code switch: if the fold's rounds send no tree and
the switch's first round sends one, the transcript's first tree is that round's. -/
theorem colAtS_block_zero (s : Sg) (dE dT dS dC : PQ.RD) (rest : List PQ.RD)
    (hE : dE.tree.isSome = false) (hT : dT.tree.isSome = false) (hS : dS.tree.isSome = true)
    (τF : Tr (PQ.uL (ckP .two) (foldRds s dE dT))) (τC : Tr (PQ.uL (ckP .two) [dS, dC]))
    (b : Tr (PQ.uL (ckP .two) rest)) (x : ℕ) :
    PQ.colAtS (ckP .two) (foldRds s dE dT ++ ([dS, dC] ++ rest))
      (joinT (foldRds s dE dT) _ τF (joinT [dS, dC] rest τC b)) 0 x = treeCol dS τC.1 x := by
  obtain ⟨mS, cS, mC, cC, _⟩ := τC
  rw [colAtS_join_none _ _ (nTrees_fold s dE dT hE hT)]
  show PQ.colAtS (ckP .two) (dS :: dC :: rest) (mS, cS, mC, cC, b) 0 x = _
  rw [colAtS_here _ _ _ _ _ hS]
  rfl

/-- If moreover the switch's second round sends no tree, the transcript's later trees are those of
the rounds that follow the code switch, in their order. -/
theorem colAtS_block_succ (s : Sg) (dE dT dS dC : PQ.RD) (rest : List PQ.RD)
    (hE : dE.tree.isSome = false) (hT : dT.tree.isSome = false) (hS : dS.tree.isSome = true)
    (hC : dC.tree.isSome = false)
    (τF : Tr (PQ.uL (ckP .two) (foldRds s dE dT))) (τC : Tr (PQ.uL (ckP .two) [dS, dC]))
    (b : Tr (PQ.uL (ckP .two) rest)) (k x : ℕ) :
    PQ.colAtS (ckP .two) (foldRds s dE dT ++ ([dS, dC] ++ rest))
      (joinT (foldRds s dE dT) _ τF (joinT [dS, dC] rest τC b)) (k + 1) x =
      PQ.colAtS (ckP .two) rest b k x := by
  obtain ⟨mS, cS, mC, cC, _⟩ := τC
  rw [colAtS_join_none _ _ (nTrees_fold s dE dT hE hT)]
  show PQ.colAtS (ckP .two) (dS :: dC :: rest) (mS, cS, mC, cC, b) (k + 1) x = _
  rw [colAtS_next _ _ _ _ _ hS, colAtS_skip _ _ _ _ _ hC]

/-- Let f give a column for a tree's number and a position. If f's trees from the number n on are
the trees of the chain's transcript in their order (`hf`), and every entry of the view's list whose
key lies below n plus the number of code switches holds f's column at its key and position (`hV`),
then the view shows the chain's trees from the key n on. Asked besides: which rounds send a tree. -/
theorem showsFrom_of (V : Fmt.View) (f : ℕ → ℕ → Option (List UInt64)) {s : Sg} (c : Chain s)
    (hc : c.Trees) (b : c.Bl) (n : ℕ)
    (hf : ∀ k x, f (n + k) x = PQ.colAtS (ckP .two) c.rds (c.trL b) k x)
    (hV : ∀ o ∈ V.opened, o.1 < n + c.len → f o.1 o.2.1 = some o.2.2) : c.ShowsFrom V n b := by
  induction c generalizing n with
  | last s e dL dB fu fs εb => trivial
  | step s s' hf' n0 e dE dT dS dC fW fZ fG εf εc next ih =>
    obtain ⟨hE, hT, hS, hC, hN⟩ := hc
    refine ⟨fun o ho hn => ?_, ih hN b.2.2 (n + 1) (fun k x => ?_)
      fun o ho hlt => hV o ho ?_⟩
    · have h1 := hV o ho (by rw [hn]; exact Nat.lt_add_of_pos_right (Nat.succ_pos _))
      rw [hn, ← Nat.add_zero n, hf 0 o.2.1] at h1
      rw [← h1]
      exact (colAtS_block_zero s dE dT dS dC next.rds hE hT hS _ _ _ _).symm
    · rw [Nat.add_assoc, Nat.add_comm 1 k, hf (k + 1) x]
      exact colAtS_block_succ s dE dT dS dC next.rds hE hT hS hC _ _ _ k x
    · show o.1 < n + (next.len + 1)
      omega

/-! ## At the view of the written link -/

section
variable (d1 d2 d3 d4 d5 dA : PQ.RD) {s : Sg} (c : Chain s)
  (m1 : (wRound d1).Msg) (c1 : (wRound d1).Chal) (m2 : (wRound d2).Msg)
  (c2 : (wRound d2).Chal) (m3 : (wRound d3).Msg) (c3 : (wRound d3).Chal)
  (m4 : (wRound d4).Msg) (c4 : (wRound d4).Chal) (m5 : (wRound d5).Msg) (c5 : (wRound d5).Chal)
  (mA : (wRound dA).Msg) (cA : (wRound dA).Chal) (b : c.Bl)

/-- Which of the link's five rounds and the batching round send a tree: the second alone. -/
structure HeadTrees : Prop where
  t1 : d1.tree.isSome = false
  t2 : d2.tree.isSome = true
  t3 : d3.tree.isSome = false
  t4 : d4.tree.isSome = false
  t5 : d5.tree.isSome = false
  tA : dA.tree.isSome = false

/-- All rounds of the written link: the five, the batching, the chain's. -/
abbrev manyRds : List PQ.RD := d1 :: d2 :: d3 :: d4 :: d5 :: dA :: c.rds

/-- A transcript of all rounds, from the first six rounds and the blocks' transcripts. -/
def manyTr : Tr (PQ.uL (ckP .two) (manyRds d1 d2 d3 d4 d5 dA c)) :=
  (m1, c1, m2, c2, m3, c3, m4, c4, m5, c5, mA, cA, c.trL b)

/-- The view's rounds are the written rounds: the first six, then the chain's, block by block. -/
theorem view_rounds_many (a : ℕ) (xs : List PQ.XO) (y : (twoExternalStrings (2 ^ a) PQ.SgX).Str) :
    (PQ.viewX (ckP .two) _ a xs y
      (manyTr d1 d2 d3 d4 d5 dA c m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA b)).rounds =
      PQ.rvSL (ckP .two) [d1, d2, d3, d4, d5, dA]
        (m1, c1, m2, c2, m3, c3, m4, c4, m5, c5, mA, cA, ()) ++ c.rvs b := by
  show PQ.rvSL (ckP .two) [d1, d2, d3, d4, d5, dA]
      (m1, c1, m2, c2, m3, c3, m4, c4, m5, c5, mA, cA, ()) ++
    PQ.rvSL (ckP .two) c.rds (c.trL b) = _
  rw [rvSL_trL]

/-- An entry of the view's list under the key 0 holds the column of the second round's tree at the
entry's position, and an entry under the key 1, 2, ... that of the first, second, ... code switch's
tree. Asked: which rounds send a tree, and that the trees' keys lie below 2 ^ 16, where the stored
tables' keys begin. -/
theorem shows_many (hh : HeadTrees d1 d2 d3 d4 d5 dA) (hc : c.Trees) (hl : 1 + c.len ≤ 2 ^ 16)
    (a : ℕ) (xs : List PQ.XO) (y : (twoExternalStrings (2 ^ a) PQ.SgX).Str) :
    Shows (PQ.viewX (ckP .two) _ a xs y
      (manyTr d1 d2 d3 d4 d5 dA c m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA b)) 0 (treeCol d2 m2) ∧
    c.ShowsFrom (PQ.viewX (ckP .two) _ a xs y
      (manyTr d1 d2 d3 d4 d5 dA c m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA b)) 1 b := by
  have key : ∀ o ∈ (PQ.viewX (ckP .two) _ a xs y
      (manyTr d1 d2 d3 d4 d5 dA c m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA b)).opened,
      o.1 < 1 + c.len → PQ.colAtS (ckP .two) _
        (manyTr d1 d2 d3 d4 d5 dA c m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA b) o.1 o.2.1 =
          some o.2.2 := by
    intro o ho hlt
    rcases mem_opened _ a xs y _ o ho with h | h | h
    · omega
    · omega
    · exact h.2.2
  refine ⟨fun o ho h0 => ?_, showsFrom_of _ _ c hc b 1 (fun k x => ?_) key⟩
  · have hk := key o ho (by omega)
    rw [h0] at hk
    unfold manyTr at hk
    rw [colAtS_skip _ _ _ _ _ hh.t1, colAtS_here _ _ _ _ _ hh.t2] at hk
    exact hk
  · unfold manyTr
    rw [Nat.add_comm 1 k, colAtS_skip _ _ _ _ _ hh.t1, colAtS_next _ _ _ _ _ hh.t2,
      colAtS_skip _ _ _ _ _ hh.t3, colAtS_skip _ _ _ _ _ hh.t4, colAtS_skip _ _ _ _ _ hh.t5,
      colAtS_skip _ _ _ _ _ hh.tA]

end

end OnBytes.Slice
