-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/Restr.lean: WHERE A ROW'S MESSAGE AND TAIL ARE READ, A PLAIN READER AND THE
READER OF ITS RESTRICTION TO THE SHAPE GIVE THE SAME VALUE. Statements and proofs; general in the
sizes.

Why. The frame for an honest prover in Lean (Johnson/Desc/ProofFile/Honest/) hands out the index's
matrix and the stored tables' pads and encoding randomness as functions of two plain numbers. The
library's typed encoder takes them as functions on finite ranges, and the library's
E2E/KeyReaders.lean reads these back by plain numbers, with 0 outside the ranges (`cellsReader`,
`padReader`, `tailReader`). So a plain function, cut down to the ranges and read back, is another
function than the one that was cut. This file says that the layout of a row's message
(`AtPublicFiles.Key.storedAt`) and a row's tail do not see the difference, at a row that the table has. Two
inputs are spoken of below: the goals' (a matrix of cells, pads and tails on finite ranges: what the
library's typed encoder takes) and the frame's (functions of two plain numbers: what the frame for
an honest prover hands out).

Main names (namespace `Bind.ForProver`).
   `gridReader_restr`: inside the two ranges the reader of a restriction gives the function's value.
   `storedAt_restr_at`: at plain numbers: `storedAt` at the readers of the restricted matrix (cast
      into the extension field) and of the restricted pads is `storedAt` at the matrix and the pads
      themselves: at a row b below 2^v and EVERY place e.
   **`storedAt_restr`**: the same at the library's sizes S and the matrix's numbers N, the matrix
      being `cellsOfF` (Johnson/Bind/ForProver/CellsInField.lean).
   **`tailReader_restr`**: the like for the tail: at a row below 2^v and an entry below r.
Limits. THE BOUND ON THE ROW IS NOT IDLE: so the texts read: from the row 2^v on the readers of the
restrictions give 0 and the plain functions whatever they hold; no example of this file shows it.
The same holds of the tail's entries from r on. No premise that the matrix fits before the pads is
asked: both sides are the one text `storedAt`, so a fault in that layout would pass these equations.
What holds the layout against the encoder's words is `AtPublicFiles.Key.stored_eq_hold`; against this folder's
rows, `storedAt_eq_rowMsgF` (Johnson/Bind/ForProver/Polys.lean). THESE ARE LAWS ON THE MAPS OF THE
TIE FROM THE FRAME'S INPUT TO THE GOALS'; that the input of a prover at the protocol is made by such
a restriction is said by no file beneath this one. No hash function, no query, no coin's law. This
file writes no honest prover. Nothing on completeness, on index privacy, on soundness or on any
program.
Terms: lean/TERMS.md.
-/
import E2E.KeyReaders
import Johnson.Bind.ForProver.CellsInField

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace Bind.ForProver
open OnBytes.Slice (Sz GF GE)
open OnBytes.Flat (MatrixNums)
open AtPublicFiles.Key (storedAt cellsReader gridReader padReader tailReader)

/-- Inside the two ranges the reader of a restriction gives the function's value. -/
theorem gridReader_restr (m n : ℕ) (f : ℕ → ℕ → GF) (b e : ℕ) (hb : b < m) (he : e < n) :
    gridReader (m := m) (n := n) (fun b j => f b.val j.val) b e = f b e := by
  unfold gridReader
  exact Eq.trans (dif_pos ⟨hb, he⟩) rfl

/-- **At plain numbers**: the layout of a row's message does not see the restriction, at a row that
the table has and every place. -/
theorem storedAt_restr_at (rows kLo v cut l : ℕ) (w pad : ℕ → ℕ → GF) (b e : ℕ)
    (hb : b < 2 ^ v) :
    storedAt
        (cellsReader (rows := rows) (cols := 2 ^ (kLo + v))
          fun y c => algebraMap GF GE (w y.val c.val))
        (gridReader (m := 2 ^ v) (n := l - cut) fun b j => pad b.val j.val) rows kLo cut l b e =
      storedAt w pad rows kLo cut l b e := by
  have hp : 0 < 2 ^ kLo := Nat.two_pow_pos kLo
  unfold storedAt
  by_cases h1 : e < rows * 2 ^ kLo
  · have hy : e / 2 ^ kLo < rows := (Nat.div_lt_iff_lt_mul hp).2 h1
    have hm : e % 2 ^ kLo < 2 ^ kLo := Nat.mod_lt _ hp
    have hc : e % 2 ^ kLo + 2 ^ kLo * b < 2 ^ (kLo + v) := by
      rw [pow_add]
      calc e % 2 ^ kLo + 2 ^ kLo * b < 2 ^ kLo + 2 ^ kLo * b := Nat.add_lt_add_right hm _
        _ = 2 ^ kLo * (b + 1) := by ring
        _ ≤ 2 ^ kLo * 2 ^ v := Nat.mul_le_mul_left _ hb
    rw [if_pos h1, if_pos h1]
    unfold cellsReader
    exact Eq.trans (dif_pos ⟨hy, hc⟩) rfl
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : cut ≤ e ∧ e < l
    · have h3 : e - cut < l - cut := by
        have h4 := h2.1
        have h5 := h2.2
        omega
      rw [if_pos h2, if_pos h2]
      exact gridReader_restr _ _ pad b (e - cut) hb h3
    · rw [if_neg h2, if_neg h2]

/-- **At the library's sizes**: the matrix as the library's cells, the pads cut to the shape. A law
on the maps of the tie from the frame's input to the goals' (`cellsOfF`; the restriction that `qOf`,
Johnson/Bind/ForProver/PolysAt.lean, writes). -/
theorem storedAt_restr (S : Sz) (Zs : Cb.Ood.Sample GE S.En) (cut : ℕ) (N : MatrixNums)
    (w pad : ℕ → ℕ → GF) (b e : ℕ) (hb : b < 2 ^ S.P.v) :
    storedAt (cellsReader (cellsOfF S Zs cut N w))
        (padReader (S := S) (cut := cut) fun b j => pad b.val j.val) N.rows N.kLo cut S.P.T.l b e =
      storedAt w pad N.rows N.kLo cut S.P.T.l b e :=
  storedAt_restr_at N.rows N.kLo S.P.v cut S.P.T.l w pad b e hb

/-- **The tail**: at a row that the table has and an entry that the tail has. A law on a map of the
tie: the restriction that `qOf` writes. -/
theorem tailReader_restr (S : Sz) (tail : ℕ → ℕ → GF) (b t : ℕ) (hb : b < 2 ^ S.P.v)
    (ht : t < S.P.T.r) :
    tailReader (S := S) (fun b q => tail b.val q.val) b t = tail b t :=
  gridReader_restr _ _ tail b t hb ht

end Bind.ForProver

end

#print axioms Bind.ForProver.gridReader_restr
#print axioms Bind.ForProver.storedAt_restr_at
#print axioms Bind.ForProver.storedAt_restr
#print axioms Bind.ForProver.tailReader_restr
