-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/PolysReaders.lean: THE LIBRARY'S HONEST POLYNOMIALS AT ANY INPUT OF THE
GOALS' TYPE ARE `polysAt` (Johnson/Bind/ForProver/PolysAt.lean) AT THE PLAIN READERS OF THAT INPUT;
AND THE WAY FROM THE GOALS' INPUT TO PLAIN READERS AND BACK LOSES NOTHING THAT THE ENCODER READS.
LAWS ON THE MAPS OF THE TIE. Statements and proofs; general in the sizes.

Why. Two inputs stand side by side: the goals' (a matrix of cells, pads and tails on finite ranges)
and the frame's for an honest prover (functions of two plain numbers). Either can be made of the
other by a definition. Johnson/Bind/ForProver/Polys.lean has the law on the honest polynomials where
the goals' input is made of the frame's (`polysOf_eq_polysAt`). Here is the law for the other
direction, where the frame's readers are made of the goals' input by the readers of the library's
E2E/KeyReaders.lean, and two equations by which a law in the one direction gives the like law in the
other.

Main names (namespace `Bind.ForProver`).
   `gridReader_self`: at numbers that are values of the two ranges a reader gives the function's
      value.
   **`polysOf_eq_polysAt_readers`**: under `Bind.Column.Agree sh S cut` and hfit: at EVERY matrix of
      cells i and all pads and tails q: the library's honest polynomials are `polysAt` at the
      packing of `cellsReader i` and at the coins whose pads are `padReader q.1` and whose tails are
      `tailReader q.2`.
   `qOf_readers`: the coins: to plain readers and back by `qOf` is the identity.
   `cellWords_readers`: the matrix: to a plain reader and back by `cellsOfF` gives the same words of
      the table's messages.
Limits. EVERY STATEMENT HERE IS ON MAPS BETWEEN THE TWO INPUTS (`cellsReader`, `padReader`,
`tailReader` in the one direction; `cellsOfF`, `qOf` in the other). THAT THE HONEST PROVER'S PRIVATE
INPUT AT THE PROTOCOL IS THE GOALS', WITH THE FRAME'S READERS MADE OF IT BY THE FIRST THREE, IS SAID
BY NO FILE BENEATH THIS ONE. `cellsReader` reads a cell's first coordinate alone: at a cell outside
the base field two coordinates are dropped in silence, and the way there and back gives another
matrix; `cellWords_readers` says that the encoder's words do not see it. The other round trip, from
plain functions to the ranges and back, is not the identity: it sets 0 outside the ranges
(Johnson/Bind/ForProver/Restr.lean says where that is not seen). The matrix is a letter: in range or
not, an index's or not. WITHOUT `Agree` THE READERS GIVE 0 WHERE A PAD OR A TAIL IS DUE, IN SILENCE:
the premise is not idle (read off the definitions; no example of this file shows it). `Agree` and
hfit are premises; at the full size they are theorems without premises (`Bind.Column.agree_full`,
Johnson/Bind/ColumnSizes.lean; `full_fits`, Johnson/Flat/ClaimsSizes.lean). One committed table;
which of the protocol's tables it is, the first or a copy, is not said here. No hash function, no
query, no coin's law. This file writes no honest prover. Nothing on completeness, on index privacy,
on soundness or on any program.
Terms: lean/TERMS.md.
-/
import Johnson.Bind.ForProver.Polys

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace Bind.ForProver
open OnBytes.Slice (Sz GF GE toF ofF honestPolys honestMsgs)
open OnBytes.Flat (cellWords cellEntryAt PadsOf MatrixNums rowWords tailWords)
open AtPublicFiles.Key (storedAt cellsReader gridReader padReader tailReader)
open ProofFile.Honest (TableRand)
open Bind.Twin (Shape)
open Bind.Column (Agree)

/-- At numbers that are values of the two ranges a reader gives the function's value. -/
theorem gridReader_self {m n : ℕ} (η : Fin m → Fin n → GF) (b : Fin m) (e : Fin n) :
    gridReader η b.val e.val = η b e := by
  unfold gridReader
  exact Eq.trans (dif_pos ⟨b.isLt, e.isLt⟩) rfl

/-- **The library's honest polynomials, at any input of the goals' type, are `polysAt` at that
input's plain readers.** A law on the maps of the tie: the frame's matrix and coins are the readers
of the goals', as written in the statement; that the honest prover's input at the protocol is so
made is said by no file beneath this one. -/
theorem polysOf_eq_polysAt_readers {S : Sz} {Zs : Cb.Ood.Sample GE S.En} {cut : ℕ}
    {N : MatrixNums} {sh : Shape} (h : Agree sh S cut) (hfit : N.rows * 2 ^ N.kLo ≤ cut)
    (i : OnBytes.Flat.Cells (S.toDecR Zs cut) N)
    (q : PadsOf S cut × (Fin (2 ^ S.P.v) → Fin S.P.T.r → GF)) :
    FlashProve.polysOf S Zs cut N i q =
      polysAt S sh (entryAtF N.kLo N.rows S.P.v (cellsReader i))
        ⟨padReader q.1, tailReader q.2⟩ := by
  have hc : cut + 3 * sh.s = sh.l := h.cut
  have hp : sh.plain = cut := by
    show sh.l - 3 * sh.s = cut
    omega
  have hrf : rowsFit sh N.kLo N.rows = true := (rowsFit_iff h _ _).2 hfit
  funext β k
  have hb' : Sz.rowNo β < 2 ^ sh.v := by
    rw [h.v]
    exact OnBytes.Slice.rowNo_lt β
  show honestPolys S (rowWords S (honestMsgs S (cellWords S Zs cut N i q.1))) (tailWords S q.2)
      β k =
    algebraMap GF GE (rowCoefF sh (entryAtF N.kLo N.rows S.P.v (cellsReader i))
      ⟨padReader q.1, tailReader q.2⟩ (Sz.rowNo β) k.val)
  by_cases hk : k.val < S.P.T.r
  · have hk' : k.val < sh.r := by
      rw [h.r]
      exact hk
    exact (polys_below S _ _ β k hk).trans
      ((congrArg _ (AtPublicFiles.Key.tail_eq S q.2 _ _)).trans
        (congrArg _ (rowCoefF_tail sh _ ⟨padReader q.1, tailReader q.2⟩ _ _ hk').symm))
  · have hj : k.val - S.P.T.r < S.P.T.l := by
      have h5 := k.isLt
      omega
    have e1 : rowCoefF sh (entryAtF N.kLo N.rows S.P.v (cellsReader i))
          ⟨padReader q.1, tailReader q.2⟩ (Sz.rowNo β) k.val =
        rowMsgF sh (entryAtF N.kLo N.rows S.P.v (cellsReader i))
          ⟨padReader q.1, tailReader q.2⟩ (Sz.rowNo β) (k.val - S.P.T.r) := by
      unfold rowCoefF
      rw [h.r, if_neg hk]
    have key := storedAt_eq_rowMsgF sh N.kLo N.rows hrf (cellsReader i)
      ⟨padReader q.1, tailReader q.2⟩ (Sz.rowNo β) (k.val - S.P.T.r) hb'
    rw [hp, h.l, h.v] at key
    rw [polys_from S _ _ β k hk hj, OnBytes.Flat.honestMsgs_rowWords,
      AtPublicFiles.Key.stored_eq_hold S cut N Zs hfit, e1]
    exact congrArg _ key

/-- **The coins: to plain readers and back is the identity.** A law on the maps of the tie. -/
theorem qOf_readers (S : Sz) (cut : ℕ)
    (q : PadsOf S cut × (Fin (2 ^ S.P.v) → Fin S.P.T.r → GF)) :
    qOf S cut ⟨padReader q.1, tailReader q.2⟩ = q :=
  Prod.ext (funext fun b => funext fun j => gridReader_self q.1 b j)
    (funext fun b => funext fun t => gridReader_self q.2 b t)

/-- **The matrix: to a plain reader and back gives the same words.** The encoder reads a cell's
first coordinate alone. A law on the maps of the tie. -/
theorem cellWords_readers (S : Sz) (Zs : Cb.Ood.Sample GE S.En) (cut : ℕ) (N : MatrixNums)
    (i : OnBytes.Flat.Cells (S.toDecR Zs cut) N) (η : PadsOf S cut) :
    cellWords S Zs cut N (cellsOfF S Zs cut N (cellsReader i)) η = cellWords S Zs cut N i η := by
  have e : (fun (y : Fin N.rows) (c : Fin (2 ^ (N.kLo + S.P.v))) =>
      (cellsOfF S Zs cut N (cellsReader i) y c).c0) = fun y c => (i y c).c0 := by
    funext y c
    show cellsReader i y.val c.val = (i y c).c0
    unfold cellsReader
    exact Eq.trans (dif_pos ⟨y.isLt, c.isLt⟩) rfl
  funext b
  exact congrArg (fun M' => (List.range S.P.T.l).map
    (cellEntryAt N.rows N.kLo S.P.v cut S.P.T.l M' η b)) e

end Bind.ForProver

end

#print axioms Bind.ForProver.gridReader_self
#print axioms Bind.ForProver.polysOf_eq_polysAt_readers
#print axioms Bind.ForProver.qOf_readers
#print axioms Bind.ForProver.cellWords_readers
